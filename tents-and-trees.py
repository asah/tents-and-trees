# to use with pypy:
# 1. install pypy3, e.g. brew install pypy3
# 2. install constraint, e.g. pip_pypy3 install python-constraint

import os, sys, re, random, time
import constraint
from ortools.sat.python import cp_model
from ortools.graph import pywrapgraph

SIZE = os.environ.get('SIZE', '10x10').strip()
WIDTH = int(re.sub('x.+', '', SIZE))
if WIDTH < 3 or WIDTH > 100:
  print(f"WIDTH must be between 3 and 100, not {WIDTH}")
  sys.exit(1)
HEIGHT = int(re.sub('.+?x', '', SIZE))
if HEIGHT < 3 or HEIGHT > 100:
  print(f"HEIGHT must be between 3 and 100, not {HEIGHT}")
  sys.exit(1)
DENSITY = float(os.environ.get('DENSITY', '0.5').strip())
if DENSITY < 0.1 or DENSITY > 1.0:
  print(f"DENSITY must be between 0.1 and 0.7, not {DENSITY}")
  sys.exit(1)
# todo: using alarm() to apply timeout to solvers
SOLVER_TIMEOUT = float(os.environ.get('TIMEOUT', '10.0').strip())


DEBUG = (int(os.environ.get('DEBUG', '1').strip()) == 1)
DEBUG=False

EMPTY='~'
WALL='w'
TREE='T'
TENT='t'
GRASS=' '

BOARD = []
for y in range(HEIGHT):
  BOARD.append( [EMPTY] * WIDTH )

def copy_board(board):
  return [board[y].copy() for y in range(HEIGHT)]
  
def copy_board_trees_only():
  newboard = []
  for y in range(HEIGHT):
    newboard.append( [EMPTY] * WIDTH )
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if BOARD[y][x] == TREE:
        newboard[y][x] = TREE
  return newboard
  
def legal_cell(y,x):
  return (0 <= y < HEIGHT and 0 <= x < WIDTH)

def get_cell(board,y,x):
  if not legal_cell(y,x): return WALL
  return board[y][x]

SQUARE_NEIGHBOR_OFFSETS = [ [-1,0], [0,-1], [0,1], [1,0] ]
ALL_NEIGHBOR_OFFSETS = [ [-1,-1], [-1,0], [-1,1], [0,-1], [0,1], [1,-1], [1,0], [1,1] ]
TWOBYTWO_NEIGHBOR_OFFSETS = [ [0,0], [0,1], [1,0], [1,1] ]

def can_place_tent(board,y,x):
  cell = get_cell(board,y,x)
  if cell != EMPTY: return False
  # check neighbors for other tents
  for dy,dx in ALL_NEIGHBOR_OFFSETS:
    if get_cell(board,y+dy,x+dx) == TENT: return False
  return True

def compute_sums(board):
  rowsums = [0] * HEIGHT
  colsums = [0] * WIDTH
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if BOARD[y][x] == TENT:
        colsums[x] += 1
        rowsums[y] += 1
  return rowsums, colsums

def print_board(board, rowsums, colsums):
  print(f"    {' '.join([str(x) for x in colsums])}")
  for y in range(HEIGHT):
    print(f"{rowsums[y]:>3} {''.join([str(x)+' ' for x in board[y]])}")
  print("")


def solver_setup(board):
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] not in [TREE, EMPTY]:
        board[y][x] = EMPTY
  # add grass if cell not adjacent to tree
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == EMPTY:
        for dy,dx in SQUARE_NEIGHBOR_OFFSETS:
          if get_cell(board,y+dy,x+dx) == TREE:
            break
        else: # break not reached i.e. tree not found
          board[y][x] = GRASS

def does_solution_match(board, expected_board, print_mismatches=False):
  mismatches = 0
  for y in range(HEIGHT):
    for x in range(WIDTH):
      cell = board[y][x]
      # ignore mismatches of grass vs empty
      if (cell == TREE or cell == TENT) and cell != expected_board[y][x]:
        if print_mismatches:
          print(f"mismatch at {y},{x}: {board[y][x]} vs {expected_board[y][x]}")
        mismatches += 1
  return (mismatches == 0)

  
def check_solution(board, expected_rowsums, expected_colsums):
  numtrees = numtents = 0
  rowsums = [0] * HEIGHT
  colsums = [0] * WIDTH
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == TREE:
        numtrees += 1
      elif board[y][x] == TENT:
        numtents += 1
        rowsums[y] += 1
        colsums[x] += 1

  errors = []
  if numtrees != numtents:
    errors.append(f"error: {numtrees} trees but {numtents} tents.")
  for y in range(HEIGHT):
    if rowsums[y] != expected_rowsums[y]:
      errors.append(f"error: row {y} has {rowsums[y]} trees but expected {expected_rowsums[y]}.")
  for x in range(WIDTH):
    if colsums[x] != expected_colsums[x]:
      errors.append(f"error: col {x} has {colsums[x]} trees but expected {expected_colsums[x]}.")
  if len(errors) != 0:
    print("\n".join(errors))


def is_one_tree_per_tent(board):
  model = cp_model.CpModel()
  solver = cp_model.CpSolver()
  tent_for_tree_vars = []
  tentidx = []
  cur_tent_idx = 0
  for y in range(HEIGHT):
    tentidx.append( [0] * WIDTH )
    for x in range(WIDTH):
      if board[y][x] == TENT:
        tentidx[y][x] = cur_tent_idx
        cur_tent_idx += 1
  #print(tentidx)
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == TREE:
        # NewIntVarFromDomain wants domains: https://github.com/google/or-tools/blob/master/ortools/sat/python/cp_model.py#L718
        adjacent_tent_idxs = [tentidx[y+dy][x+dx] for dy,dx in SQUARE_NEIGHBOR_OFFSETS if get_cell(board, y+dy, x+dx) == TENT]
        #print(f"tree@{y},{x} adjacent tents = {adjacent_tent_idxs}")
        adjacent_tents = [ [idx,idx] for idx in adjacent_tent_idxs] # lame/unoptimized
        tent_for_tree_vars.append(model.NewIntVarFromDomain(
          cp_model.Domain.FromIntervals(adjacent_tents),
          't4T'+str(len(tent_for_tree_vars))))
  model.AddAllDifferent(tent_for_tree_vars)
  status = solver.Solve(model)
  if status == cp_model.INFEASIBLE:
    return False # no need to print - this is the default
  if status == cp_model.MODEL_INVALID:
    print("is_one_tree_per_tent: invalid")
    return False
  if status == cp_model.UNKNOWN:
    print("is_one_tree_per_tent: unknown")
    return False
  return True

solver_count = 0
start_time = time.time()
def brute_force_solver(board, rowsums, colsums):
  global solver_count
  solver_count += 1
  if solver_count % 100000 == 0:
    print_board(board, ROWSUMS, COLSUMS)
    if time.time() - start_time > SOLVER_TIMEOUT:
      print(f"solver timing out after {SOLVER_TIMEOUT} secs.")
      sys.exit(1)
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == EMPTY and can_place_tent(board,y,x):
        #print(f"trying to place tent in {y},{x}...")
        newboard = copy_board(board)
        newboard[y][x] = TENT
        for dy,dx in ALL_NEIGHBOR_OFFSETS:
          if get_cell(board,y+dy,x+dx) == EMPTY:
            newboard[y+dy][x+dx] = GRASS
        brute_force_solver(newboard)

def constraint_solver(board, rowsums, colsums):
  problem = constraint.Problem(constraint.RecursiveBacktrackingSolver())
  rowsum_vars = []
  for y in range(HEIGHT):
    rowsum_vars.append([])
  colsum_vars = []
  for x in range(WIDTH):
    colsum_vars.append([])
  vars_added = {}
  # row and column sums must add up
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == TREE:
        for dy,dx in SQUARE_NEIGHBOR_OFFSETS:
          varname = f"y{y+dy}x{x+dx}"
          if varname not in vars_added and get_cell(board,y+dy,x+dx) == EMPTY:
            problem.addVariable(varname, [0,1])
            rowsum_vars[y+dy].append(varname)
            colsum_vars[x+dx].append(varname)
            vars_added[varname] = True
  for y in range(HEIGHT):
    print(rowsum_vars[y])
    problem.addConstraint(constraint.ExactSumConstraint(rowsums[y]), rowsum_vars[y])
  for x in range(WIDTH):
    problem.addConstraint(constraint.ExactSumConstraint(colsums[x]), colsum_vars[x])

  # every tree must have at least one tent
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == TREE:
        neighbors = []
        for dy,dx in SQUARE_NEIGHBOR_OFFSETS:
          if get_cell(board,y+dy,x+dx) == EMPTY:
            varname = f"y{y+dy}x{x+dx}"
            neighbors.append(varname)
        problem.addConstraint(constraint.MinSumConstraint(1), neighbors)
  # no tent can be adjacent to another tent
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == EMPTY:
        neighbors = []
        for dy,dx in TWOBYTWO_NEIGHBOR_OFFSETS:
          if get_cell(board,y+dy,x+dx) == EMPTY:
            varname = f"y{y+dy}x{x+dx}"
            neighbors.append(varname)
        problem.addConstraint(constraint.MaxSumConstraint(1), neighbors)

  solution = problem.getSolution()
  if solution is None:
    print("oops! couldn't find a solution.")
    return
  soln_board = copy_board_trees_only()
  for key,val in sorted(solution.items()):
    if val == 1:
      ystr,xstr = key.replace('y','').split('x')
      soln_board[int(ystr)][int(xstr)] = TENT
  print("checking solution...")
  check_solution(soln_board, rowsums, colsums)
  does_solution_match(soln_board, BOARD)
  print_board(soln_board, rowsums, colsums)

class SolutionPrinter(cp_model.CpSolverSolutionCallback):
  """Print intermediate solutions."""

  def __init__(self, variables, rowsums, colsums):
    cp_model.CpSolverSolutionCallback.__init__(self)
    self.__variables = variables
    self.__solnboards = []
    self.__rowsums = rowsums
    self.__colsums = colsums

  def SolutionBoards(self):
    return self.__solnboards

  def OnSolutionCallback(self):
    soln_board = copy_board_trees_only()
    for y in range(HEIGHT):
      for x in range(WIDTH):
        if soln_board[y][x] != TREE:
          soln_board[y][x] = TENT if self.Value(self.__variables[y][x]) == 1 else GRASS
    self.__solnboards.append(soln_board)
    print(".", end='', flush=True)

  def SolutionCount(self):
    return len(self.__solnboards)

def ortools_cpsat_solver(board, rowsums, colsums):
  model = cp_model.CpModel()
  solver = cp_model.CpSolver()
  rowsum_vars = []
  for y in range(HEIGHT):
    rowsum_vars.append([])
  colsum_vars = []
  for x in range(WIDTH):
    colsum_vars.append([])
  vars_added = {}
  vars = []
  for y in range(HEIGHT):
    vars.append( [None] * WIDTH )
  trees = []
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == TREE:
        trees.append( (y,x) )
  # row and column sums must add up
  for y,x in trees:
    for dy,dx in SQUARE_NEIGHBOR_OFFSETS:
      # blank-out rows & columns with zero sums
      if 0 <= dy+y < HEIGHT and rowsum_vars[dy+y] == 0:
        continue
      if 0 <= dx+x < WIDTH and colsum_vars[x+dx] == 0:
        continue
      varname = f"y{y+dy}x{x+dx}"
      if varname not in vars_added and get_cell(board,y+dy,x+dx) == EMPTY:
        newvar = vars[y+dy][x+dx] = model.NewIntVar(0, 1, varname)
        rowsum_vars[y+dy].append(newvar)
        colsum_vars[x+dx].append(newvar)
        vars_added[varname] = True            
  for y in range(HEIGHT):
    model.Add(sum(rowsum_vars[y]) == rowsums[y])
  for x in range(WIDTH):
    model.Add(sum(colsum_vars[x]) == colsums[x])
  # every tree must have at least one tent
  for y,x in trees:
    neighbors = []
    for dy,dx in SQUARE_NEIGHBOR_OFFSETS:
      if get_cell(board,y+dy,x+dx) == EMPTY:
        neighbors.append(vars[y+dy][x+dx])
    model.Add(sum(neighbors) >= 1)
  # no tent can be adjacent to another tent
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == EMPTY:
        neighbors = []
        for dy,dx in TWOBYTWO_NEIGHBOR_OFFSETS:
          if get_cell(board,y+dy,x+dx) == EMPTY:
            neighbors.append(vars[y+dy][x+dx])
        model.Add(sum(neighbors) <= 1)

  callback = SolutionPrinter(vars, rowsums, colsums)
  solver.parameters.max_time_in_seconds = 10.0
  status = solver.SearchForAllSolutions(model, callback)
  if status == cp_model.INFEASIBLE:
    print("oops! solver says INFEASIBLE")
    return
  if status == cp_model.MODEL_INVALID:
    print("oops! solver says MODEL_INVALID")
    return
  if status == cp_model.UNKNOWN:
    print("oops! solver says UNKNOWN / timeout")
    return
  print("\n") # end the dots

  for soln_board in callback.SolutionBoards():
    if not is_one_tree_per_tent(soln_board):
      print("skipping solution that violates no-sharing...\n")
      continue
    if does_solution_match(soln_board, BOARD):
      print("valid solution, and it matches.")
    else:
      print("valid solution, but it doesn't match:")
      print_board(soln_board, rowsums, colsums)
      print("expected:")
      print_board(BOARD, rowsums, colsums)

# place both trees and tents at the same time
for y in range(HEIGHT):
  for x in range(WIDTH):
    if BOARD[y][x] == EMPTY:
      if random.random() < DENSITY:
        random.shuffle(SQUARE_NEIGHBOR_OFFSETS)
        for dy,dx in SQUARE_NEIGHBOR_OFFSETS:
          if can_place_tent(BOARD,y+dy,x+dx):
            BOARD[y+dy][x+dx] = TENT
            BOARD[y][x] = TREE
            if DEBUG:
              print(f"added TREE to {y},{x} and associated tent to {y+dy},{x+dx}")
            break
ROWSUMS, COLSUMS = compute_sums(BOARD)
check_solution(BOARD, ROWSUMS, COLSUMS)
print_board(BOARD, ROWSUMS, COLSUMS)

SOLVER_BOARD = copy_board_trees_only()
#print_board(SOLVER_BOARD, ROWSUMS, COLSUMS)
#solver_setup(SOLVER_BOARD)
#check_solution(SOLVER_BOARD, ROWSUMS, COLSUMS)
#brute_force_solver(SOLVER_BOARD)

solver_setup(SOLVER_BOARD)
#print_board(SOLVER_BOARD, ROWSUMS, COLSUMS)

print("running the solver...")

#constraint_solver(SOLVER_BOARD, ROWSUMS, COLSUMS)

ortools_cpsat_solver(SOLVER_BOARD, ROWSUMS, COLSUMS)

#ortools_assignment_solver(SOLVER_BOARD, ROWSUMS, COLSUMS)


