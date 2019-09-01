import os, sys, re, random

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
ROWSUMS, COLSUMS = compute_sums(BOARD)
print_board(BOARD, ROWSUMS, COLSUMS)

SOLVER_BOARD = copy_board_trees_only()
print_board(SOLVER_BOARD, ROWSUMS, COLSUMS)

def solver(board):
  print("adding grass if cell not adjacent to tree...")
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == EMPTY:
        for dy,dx in SQUARE_NEIGHBOR_OFFSETS:
          if get_cell(board,y+dy,x+dx) == TREE:
            break
        else: # break not reached i.e. tree not found
          board[y][x] = GRASS
  print_board(board, ROWSUMS, COLSUMS)        

solver_count = 0
def try_solving(board):
  global solver_count
  solver_count += 1
  if solver_count % 1000 == 0:
    print_board(board, ROWSUMS, COLSUMS)
  for y in range(HEIGHT):
    for x in range(WIDTH):
      if board[y][x] == EMPTY and can_place_tent(board,y,x):
        #print(f"trying to place tent in {y},{x}...")
        newboard = copy_board(board)
        newboard[y][x] = TENT
        for dy,dx in ALL_NEIGHBOR_OFFSETS:
          if get_cell(board,y+dy,x+dx) == EMPTY:
            newboard[y+dy][x+dx] = GRASS
        try_solving(newboard)

solver(SOLVER_BOARD)
try_solving(SOLVER_BOARD)

