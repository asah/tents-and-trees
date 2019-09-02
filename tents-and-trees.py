# to use with pypy:
# 1. install pypy3, e.g. brew install pypy3
# 2. install constraint, e.g. pip_pypy3 install python-constraint

import os, sys, re, random, time
import constraint

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

EMPTY=' '
WALL='w'
TREE='T'
TENT='t'
GRASS='_'

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

def neighbors(y,x):
  neighbors_subboard=[]
  for dy in range(-1,2):
    row = []
    for dx in range(-1,2):
      row.append(get_cell(board,y+dy,x+dx))
    neighbors_subboard.append(row)
  return neighbors_subboard

SQUARE_NEIGHBOR_OFFSETS = [ [-1,0], [0,-1], [0,1], [1,0] ]
ALL_NEIGHBOR_OFFSETS = [ [-1,-1], [-1,0], [-1,1], [0,-1], [0,1], [1,-1], [1,0], [1,1] ]
TWOBYTWO_NEIGHBOR_OFFSETS = [ [0,0], [0,1], [1,0], [1,1] ]

def num_empty_neighbors(y,x):
  """includes cell itself"""
  return sum([1 if BOARD[y+dy][x+dx] == EMPTY else 0 for dx,dy in SQUARE_NEIGHBOR_OFFSETS])

def neighbors_list(y,x):
  res = []
  for col in neighbors(y,x):
    for row in col:
      res += row
  return res

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

def check_solution_match(board, expected_board):
  mismatches = 0
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] != expected_board[y][x]:
        print(f"mismatch at {y},{x}: {board[y][x]} vs {expected_board[y][x]}")
        mismatches += 1
  if mismatches == 0:
    print("solution matches expected.")
  
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
  if len(errors) == 0:
    print("solution is valid!")
  else:
    print("\n".join(errors))

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
      soln_board[int(ystr)][int(xstr)] = 't'
  print("checking solution...")
  check_solution(soln_board, rowsums, colsums)
  check_solution_match(soln_board, BOARD)
  print_board(soln_board, rowsums, colsums)
    
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

print("setting up solver - stripping the trees...")
solver_setup(SOLVER_BOARD)
#print_board(SOLVER_BOARD, ROWSUMS, COLSUMS)
constraint_solver(SOLVER_BOARD, ROWSUMS, COLSUMS)

#check_solution(SOLVER_BOARD, ROWSUMS, COLSUMS)
