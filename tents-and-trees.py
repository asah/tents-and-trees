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
SOLVER_TIMEOUT = float(os.environ.get('TIMEOUT', '100.0').strip())

SEED = os.environ.get('SEED', None)
random.seed(SEED)

DEBUG = (int(os.environ.get('DEBUG', '1').strip()) == 1)
DEBUG=False

EMPTY=' '
WALL='w'
TREE='T'
TENT='t'
GRASS='g'

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

def is_empty_single_in_row(board, y, x):
  #print(f"is_empty_single_in_row(board, y={y}, x={x}): {get_cell(board, y, x-1)} - {get_cell(board, y, x)} - {get_cell(board, y, x+1)}")
  return (get_cell(board, y, x-1) != EMPTY and
          get_cell(board, y, x)   == EMPTY and
          get_cell(board, y, x+1) != EMPTY)

def is_empty_double_in_row(board, y, x):
  # start of multiple-empty run only, i.e. behind us is NOT empty!
  return (get_cell(board, y, x-1) != EMPTY and
          get_cell(board, y, x)   == EMPTY and
          get_cell(board, y, x+1) == EMPTY and
          get_cell(board, y, x+2) != EMPTY)

def is_empty_tripleplus_in_row(board, y, x):
  # start of multiple-empty run only, i.e. behind us is NOT empty!
  return (get_cell(board, y, x-1) != EMPTY and
          get_cell(board, y, x)   == EMPTY and
          get_cell(board, y, x+1) == EMPTY and
          get_cell(board, y, x+2) == EMPTY)

def is_empty_single_in_col(board, y, x):
  #print(f"is_empty_single_in_col(board, y={y}, x={x}): {get_cell(board, y-1, x)} - {get_cell(board, y, x)} - {get_cell(board, y+1, x)} (note: vertical)")
  return (get_cell(board, y-1, x) != EMPTY and
          get_cell(board, y,   x) == EMPTY and
          get_cell(board, y+1, x) != EMPTY)

def is_empty_double_in_col(board, y, x):
  # start of multiple-empty run only, i.e. behind us is NOT empty!
  return (get_cell(board, y-1, x) != EMPTY and
          get_cell(board, y,   x) == EMPTY and
          get_cell(board, y+1, x) == EMPTY and
          get_cell(board, y+2, x) != EMPTY)

def is_empty_tripleplus_in_col(board, y, x):
  # start of multiple-empty run only, i.e. behind us is NOT empty!
  return (get_cell(board, y-1, x) != EMPTY and
          get_cell(board, y,   x) == EMPTY and
          get_cell(board, y+1, x) == EMPTY and
          get_cell(board, y+2, x) == EMPTY)

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

def print_vars(vars_array, rowsums, colsums):
  print(f"    {' '.join([str(x) for x in colsums])}")
  for y in range(HEIGHT):
    #print(f"{rowsums[y]:>3} {''.join([re.sub(r'y.+', '?', str(x))+' ' for x in vars_array[y]])}")
    print(f"{rowsums[y]:>3} {''.join([str(x)+' ' for x in vars_array[y]])}")
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
      if cell in [TREE, TENT] and cell != expected_board[y][x]:
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

  print_board(board, [' ']*HEIGHT, [' ']*WIDTH)
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == TREE:
        # NewIntVarFromDomain wants domains: https://github.com/google/or-tools/blob/master/ortools/sat/python/cp_model.py#L718
        adjacent_tent_idxs = [tentidx[y+dy][x+dx] for dy,dx in SQUARE_NEIGHBOR_OFFSETS if get_cell(board, y+dy, x+dx) == TENT]
        print(f"tree@{y},{x} adjacent tents = {adjacent_tent_idxs}")
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
    print(".", end='', flush=True)
    if is_one_tree_per_tent(soln_board):
      self.__solnboards.append(soln_board)
      self.StopSearch()

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

  print("board after setup:")
  print_board(board, rowsums, colsums)

  # didn't use a decorator because I want to define and call at once
  def accelerator(msg, func):
    if func(board, rowsums, colsums):
      print(f"board after accelerator: {msg}")
      print_board(board, rowsums, colsums)
      if not does_solution_match(board, BOARD, print_mismatches=True):
        sys.exit(0)
      return True
    print(f"no change after accelerator: {msg}")
    return False

  def place_grass(board, y, x):
    board[y][x] = GRASS
    print(f"placed grass on {y},{x}")
    return True
  def place_tent(board, y, x):
    board[y][x] = TENT
    print(f"placed tent on {y},{x}")
    grass_around_tent(board, y, x)
    return True

  def grass_on_zero_remaining(board, rowsums, columns):
    changed = False
    for y in range(HEIGHT):
      for x in range(WIDTH):
        if board[y][x] == EMPTY and (colsum_vars[x] == 0 or rowsum_vars[y] == 0):
          changed = place_grass(board, y, x)
    # if no remaining, then grass over remaining cells in the row
    for y in range(HEIGHT):
      numtents = 0
      for x in range(WIDTH):
        if board[y][x] == TENT:
          numtents += 1
      if numtents == rowsums[y]:
        for x in range(WIDTH):
          if board[y][x] == EMPTY:
            changed = place_grass(board, y, x)
    # if no remaining, then grass over remaining cells in the column
    for x in range(WIDTH):
      numtents = 0
      for y in range(HEIGHT):
        if board[y][x] == TENT:
          numtents += 1
      if numtents == colsums[x]:
        for y in range(HEIGHT):
          if board[y][x] == EMPTY:
            changed = place_grass(board, y, x)
    return changed

  def fill_singles_if_sums_match(board, rowsums, columns):
    changed = False
    for y in range(HEIGHT):
      empty_singles, empty_doubles, tents = [], [], []
      for x in range(WIDTH):
        if board[y][x] == TENT:
          tents.append(x)
        if is_empty_tripleplus_in_row(board, y, x):
          break
        if is_empty_single_in_row(board, y, x):
          empty_singles.append(x)
        elif is_empty_double_in_row(board, y, x):
          empty_doubles.append(x)
      else:
        if len(tents) + len(empty_singles) + len(empty_doubles) == rowsums[y]:
          for x in empty_singles:
            if board[y][x] == EMPTY:
              changed = place_tent(board, y, x)
          if changed:
            print(f"fill singles by row: y={y} x={empty_singles} empty_doubles={empty_doubles} sum={rowsums[y]} ")
    for x in range(HEIGHT):
      empty_singles, empty_doubles, tents = [], [], []
      for y in range(WIDTH):
        if is_empty_tripleplus_in_col(board, y, x):
          break
        if board[y][x] == TENT:
          tents.append(y)
        if is_empty_single_in_col(board, y, x):
          empty_singles.append(y)
        elif is_empty_double_in_col(board, y, x):
          empty_doubles.append(y)
      else:
        if len(tents) + len(empty_singles) + len(empty_doubles) == colsums[x]:
          for y in empty_singles:
            if board[y][x] == EMPTY:
              changed = place_tent(board, y, x)
          if changed: print(f"fill singles by col: x={x} y={empty_singles} empty_doubles={empty_doubles} sum={colsums[x]} ")
    return changed

  def grass_around_tent(board, y, x):
    changed = False
    for dy,dx in ALL_NEIGHBOR_OFFSETS:
      if get_cell(board,y+dy,x+dx) == EMPTY:
        changed = place_grass(board, y+dy, x+dx)
    return changed

  def grass_around_tents(board, rowsums, columns):
    changed = False
    for y in range(HEIGHT):
      for x in range(WIDTH):
        if board[y][x] == TENT:
          changed = grass_around_tent(board, y, x)
    return changed

  def place_tent_next_to_lonely_trees(board, rowsums, columns):
    changed = False
    for y in range(HEIGHT):
      for x in range(WIDTH):
        if board[y][x] == TREE:
          empty_cell = None
          for dy,dx in SQUARE_NEIGHBOR_OFFSETS:
            if get_cell(board,y+dy,x+dx) == TENT:
              break # not lonely
            if get_cell(board,y+dy,x+dx) == EMPTY:
              if empty_cell is not None:
                break
              empty_cell = [y+dy, x+dx]
          else: # for-loop fell through i.e. one empty cell
            if empty_cell is not None:
              changed = place_tent(board, empty_cell[0], empty_cell[1])
    return changed

  changed = True
  while changed:
    changed = (
      accelerator("put grass on cells with zero remaining", grass_on_zero_remaining) or
      accelerator("fill singles if count matches rowsums", fill_singles_if_sums_match) or
      accelerator("place tents next to trees with one empty cell", place_tent_next_to_lonely_trees) or
      accelerator("put grass around tents", grass_around_tents) or
      False)
  
  # row and column sums must add up
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == EMPTY:
        vars[y][x] = model.NewIntVar(0, 1, f"y{y}x{x}")
      elif board[y][x] == GRASS:
        vars[y][x] = model.NewConstant(0) # NewIntVar(0, 0, varname)
      elif board[y][x] == TENT:
        vars[y][x] = model.NewConstant(1) # NewIntVar(1, 1, varname)
      elif board[y][x] == TREE:
        vars[y][x] = model.NewConstant(0) # NewIntVar(0, 0, varname)
      rowsum_vars[y].append(vars[y][x])
      colsum_vars[x].append(vars[y][x])
  print_vars(vars, rowsums, colsums)

  #print_board(board, rowsums, colsums)
  def add_rowcol_constraints(model, board, rowsums, colsums):
    for y in range(HEIGHT):
      # skip rows with no empty cells
      if sum([1 for x in range(WIDTH) if board[y][x] == EMPTY]) == 0:
        break
      print(f"rowsums: {rowsums[y]}=sum({sorted(rowsum_vars[y], key=lambda v: v.Name())}))".replace("..", "-").replace('y','').replace('x',','))
      model.Add(sum(rowsum_vars[y]) == rowsums[y])
      break
    for x in range(WIDTH):
      # skip columns with no empty cells
      if sum([1 for y in range(HEIGHT) if board[y][x] == EMPTY]) == 0:
        break
      print(f"colsums: {colsums[x]}=sum({sorted(colsum_vars[x], key=lambda v: v.Name())}))".replace("..", "-").replace('y','').replace('x',','))
      model.Add(sum(colsum_vars[x]) == colsums[x])

  def add_tree_tent_constraints(model, board, trees):
    # every tree must have at least one tent
    for y,x in trees:
      empty_neighbors = []
      for dy,dx in SQUARE_NEIGHBOR_OFFSETS:
        if get_cell(board,y+dy,x+dx) == TENT:
          break
        if get_cell(board,y+dy,x+dx) == EMPTY:
          empty_neighbors.append(vars[y+dy][x+dx])
      else:
        if len(empty_neighbors) > 0:
          model.Add(sum(empty_neighbors) >= 1)  # ignore if a tent is found
          print(f"tree@{y},{x} has tent in neighbors: {empty_neighbors}")

  def add_tent_tent_constraints(model, board):
    # no tent can be adjacent to another tent
    for y in range(HEIGHT):
      for x in range(WIDTH):
        if board[y][x] == EMPTY:
          neighbors = []
          for dy,dx in ALL_NEIGHBOR_OFFSETS:
            if get_cell(board,y+dy,x+dx) in [EMPTY, TENT]:
              neighbors.append(vars[y+dy][x+dx])
          if len(neighbors) > 1:
            print(f"empty@{y},{x} has at most one tent among: {neighbors}")
            model.Add(sum(neighbors) <= 1)

  add_rowcol_constraints(model, board, rowsums, colsums)
  add_tree_tent_constraints(model, board, trees)
  add_tent_tent_constraints(model, board)

  callback = SolutionPrinter(vars, rowsums, colsums)
  solver.parameters.max_time_in_seconds = SOLVER_TIMEOUT
  solver.parameters.random_seed = int(SEED) if SEED else 1234
  #print(dir(solver.parameters))
  solver.parameters.search_branching = cp_model.PORTFOLIO_SEARCH  #FIXED_SEARCH
  #status = solver.SearchForAllSolutions(model, callback)
  status = solver.SolveWithSolutionCallback(model, callback)
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

  if len(callback.SolutionBoards()) == 0:
    print("no valid solutions?!")

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


