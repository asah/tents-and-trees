# to run
# while [ 1 ]; do BOARD=24x24 python3 tents-and-trees.py > output.txt; status=$?; egrep 'SEED|success|oops' output.txt; if [ $status -ne 0 ]; then break; fi; done

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

DBG_CONSTRAINT = int(os.environ.get('DBG_CONSTRAINT', '0'))

SEED = int(os.environ.get('SEED', random.randint(0, 9999999)))
print(f"SEED={SEED}")
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

def board_height(board):
  return len(board)

def board_width(board):
  return len(board[0])

def copy_board(board):
  return [board[y].copy() for y in range(board_height(board))]
  
def copy_board_trees_only(board=BOARD):
  newboard = []
  for y in range(board_height(board)):
    newboard.append( [EMPTY] * board_width(board) )
  for y in range(board_height(board)):
    for x in range(board_width(board)):
      if board[y][x] == TREE:
        newboard[y][x] = TREE
  return newboard
  
def legal_cell(board, y,x):
  return (0 <= y < board_height(board) and 0 <= x < board_width(board))

def get_cell(board,y,x):
  if not legal_cell(board, y,x): return WALL
  return board[y][x]

def frac_filled(board):
  numtrees,numfills = 0,0
  for y in range(board_height(board)):
    for x in range(board_width(board)):
      if board[y][x] == TREE:
        numtrees += 1
      elif board[y][x] != EMPTY:
        numfills += 1
  return (1.0*numfills) / (board_height(board) * board_width(board) - numtrees)

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

def is_empty_n_in_row(board, y, x, n, bounded=True):
  #print(f"is_empty_single_in_row(board, y={y}, x={x}): {get_cell(board, y, x-1)} - {get_cell(board, y, x)} - {get_cell(board, y, x+1)}")
  if get_cell(board, y, x-1) == EMPTY: return False
  for i in range(n):
    if get_cell(board, y, x+i) != EMPTY: return False
  if bounded and get_cell(board, y, x+n) == EMPTY: return False
  return True
  
def is_empty_single_in_row(board, y, x):
  return is_empty_n_in_row(board, y, x, 1)

def is_empty_double_in_row(board, y, x):
  return is_empty_n_in_row(board, y, x, 2)

def is_empty_triple_in_row(board, y, x):
  return is_empty_n_in_row(board, y, x, 3)

def is_empty_quad_in_row(board, y, x):
  return is_empty_n_in_row(board, y, x, 4)

def is_empty_fiveplus_in_row(board, y, x):
  return is_empty_n_in_row(board, y, x, 5, bounded=False)


def is_empty_n_in_col(board, y, x, n, bounded=True):
  #print(f"is_empty_single_in_col(board, y={y}, x={x}): {get_cell(board, y-1, x)} - {get_cell(board, y, x)} - {get_cell(board, y+1, x)} (note: vertical)")
  if get_cell(board, y-1, x) == EMPTY: return False
  for i in range(n):
    if get_cell(board, y+i, x) != EMPTY: return False
  if bounded and get_cell(board, y+n, x) == EMPTY: return False
  return True

def is_empty_single_in_col(board, y, x):
  return is_empty_n_in_col(board, y, x, 1)

def is_empty_double_in_col(board, y, x):
  return is_empty_n_in_col(board, y, x, 2)

def is_empty_triple_in_col(board, y, x):
  return is_empty_n_in_col(board, y, x, 3)

def is_empty_quad_in_col(board, y, x):
  return is_empty_n_in_col(board, y, x, 4)

def is_empty_fiveplus_in_col(board, y, x):
  return is_empty_n_in_col(board, y, x, 5, bounded=False)

def has_empty(board):
  for y in range(board_height(board)):
    for x in range(board_width(board)):
      if board[y][x] == EMPTY:
        return True
  return False

def compute_sums(board):
  rowsums = [0] * board_height(board)
  colsums = [0] * board_width(board)
  for y in range(board_height(board)):
    for x in range(board_width(board)):
      if board[y][x] == TENT:
        colsums[x] += 1
        rowsums[y] += 1
  return rowsums, colsums

def print_board(board, rowsums=None, colsums=None):
  colnums = ''.join([f"{x%10}" for x in range(board_width(board))])
  print(f"cols:   {colnums}")
  if colsums is not None:
    colsumvals = ''.join([f"{int(x/10)}".replace('0',' ') for x in colsums])
    print(f"sum*10: {colsumvals}")
    colsumvals = ''.join([f"{x%10}" for x in colsums])
    print(f"sum* 1: {colsumvals}")
  for i, y in enumerate(range(len(board))):
    print(f"{i:>4} {'' if rowsums is None else rowsums[y]:>2} {''.join([str(x) for x in board[y]])}")
  print("")

def print_vars(board, vars_array, rowsums=None, colsums=None):
  colnums = ''.join([f"{x%10}" for x in range(board_width(board))])
  if colsums is not None:
    colsumvals = ''.join([f"{int(x/10)}".replace('0',' ') for x in colsums])
    print(f"sum*10: {colsumvals}")
    colsumvals = ''.join([f"{x%10}" for x in colsums])
    print(f"sum* 1: {colsumvals}")
  for y in range(len(vars_array)):
    print(f"{'' if rowsums is None else rowsums[y]:>3} {''.join([str(x)+' ' for x in vars_array[y]])}")
  print("")


def solver_setup(board):
  for y in range(board_height(board)):
    for x in range(board_width(board)):
      if board[y][x] not in [TREE, EMPTY]:
        board[y][x] = EMPTY
  # add grass if cell not adjacent to tree
  for y in range(board_height(board)):
    for x in range(board_width(board)):
      if board[y][x] == EMPTY:
        for dy,dx in SQUARE_NEIGHBOR_OFFSETS:
          if get_cell(board,y+dy,x+dx) == TREE:
            break
        else: # break not reached i.e. tree not found
          board[y][x] = GRASS

def does_solution_match(board, expected_board, rowsums, colsums, print_mismatches=False, exit_on_mismatch=False):
  mismatches = 0
  for y in range(board_height(board)):
    for x in range(board_width(board)):
      cell = board[y][x]
      # ignore mismatches of grass vs empty
      if (cell in [TREE, TENT] and cell != expected_board[y][x]) or \
         (cell == GRASS and expected_board[y][x] == TENT):
        if print_mismatches:
          print(f"mismatch at {y},{x}: {board[y][x]} vs {expected_board[y][x]}")
          print_board(board, rowsums, colsums)
          print_board(expected_board, rowsums, colsums)
        mismatches += 1
  if exit_on_mismatch and mismatches > 0:
    sys.exit(1)
  return (mismatches == 0)

  
def check_solution(board, expected_rowsums, expected_colsums):
  numtrees = numtents = 0
  rowsums = [0] * board_height(board)
  colsums = [0] * board_width(board)
  for y in range(board_height(board)):
    for x in range(board_width(board)):
      if board[y][x] == TREE:
        numtrees += 1
      elif board[y][x] == TENT:
        numtents += 1
        rowsums[y] += 1
        colsums[x] += 1

  errors = []
  if numtrees != numtents:
    errors.append(f"error: {numtrees} trees but {numtents} tents.")
  for y in range(board_height(board)):
    if rowsums[y] != expected_rowsums[y]:
      errors.append(f"error: row {y} has {rowsums[y]} trees but expected {expected_rowsums[y]}.")
  for x in range(board_width(board)):
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
  for y in range(board_height(board)):
    tentidx.append( [0] * board_width(board) )
    for x in range(board_width(board)):
      if board[y][x] == TENT:
        tentidx[y][x] = cur_tent_idx
        cur_tent_idx += 1

  #print_board(board, [' ']*board_height(board), [' ']*board_width(board))
  for y in range(board_height(board)):
    for x in range(board_width(board)):
      if board[y][x] == TREE:
        # NewIntVarFromDomain wants domains: https://github.com/google/or-tools/blob/master/ortools/sat/python/cp_model.py#L718
        adjacent_tent_idxs = [tentidx[y+dy][x+dx] for dy,dx in SQUARE_NEIGHBOR_OFFSETS if get_cell(board, y+dy, x+dx) == TENT]
        if len(adjacent_tent_idxs) == 0:
          print(f"is_one_tree_per_tent: tree@{y},{x} is missing a tent !")
          return False
        #print(f"tree@{y},{x} adjacent tents = {adjacent_tent_idxs}")
        adjacent_tents = [ [idx,idx] for idx in adjacent_tent_idxs] # lame/unoptimized
        tent_for_tree_vars.append(model.NewIntVarFromDomain(
          cp_model.Domain.FromIntervals(adjacent_tents),
          't4T'+str(len(tent_for_tree_vars))))
  model.AddAllDifferent(tent_for_tree_vars)
  status = solver.Solve(model)
  if status == cp_model.INFEASIBLE:
    print("is_one_tree_per_tent: can't match trees and tents")
    return False
  if status == cp_model.MODEL_INVALID:
    print("is_one_tree_per_tent: invalid")
    print(model.Validate())
    return False
  if status == cp_model.UNKNOWN:
    print("is_one_tree_per_tent: unknown")
    return False
  return True

class SolutionPrinter(cp_model.CpSolverSolutionCallback):
  """Print intermediate solutions."""

  def __init__(self, board, variables):
    cp_model.CpSolverSolutionCallback.__init__(self)
    self.__board = board
    self.__variables = variables
    self.__solnboards = []

  def SolutionBoards(self):
    return self.__solnboards

  def OnSolutionCallback(self):
    board = copy_board_trees_only(self.__board)
    for y in range(board_height(board)):
      for x in range(board_width(board)):
        if board[y][x] != TREE:
          board[y][x] = TENT if self.Value(self.__variables[y][x]) == 1 else GRASS
    print(".", end='', flush=True)
    if is_one_tree_per_tent(soln_board):
      print(" found solution - stopping.")
      self.__solnboards.append(board)
      self.StopSearch()

  def SolutionCount(self):
    return len(self.__solnboards)

def ortools_cpsat_solver(board, rowsums, colsums):
  rowsum_vars = []
  for y in range(board_height(board)):
    rowsum_vars.append([])
  colsum_vars = []
  for x in range(board_width(board)):
    colsum_vars.append([])

  print("board after setup:")
  print_board(board, rowsums, colsums)

  # row and column sums must add up
  def create_vars(model, board):
    vars = []
    for y in range(board_height(board)):
      vars.append([])
      for x in range(board_width(board)):
        if board[y][x] == EMPTY:
          vars[y].append(model.NewIntVar(0, 1, f"y{y}x{x}"))
        elif board[y][x] == GRASS:
          vars[y].append(model.NewConstant(0)) # NewIntVar(0, 0, varname)
        elif board[y][x] == TENT:
          vars[y].append(model.NewConstant(1)) # NewIntVar(1, 1, varname)
        elif board[y][x] == TREE:
          vars[y].append(model.NewConstant(0)) # NewIntVar(0, 0, varname)
        elif board[y][x] == WALL:
          # ignore WALL, e.g. for miniboards
          vars[y].append(None)
          pass
        else:
          print(f"ERROR: unknown board state @ {y},{x}: {board[y][x]}")
          sys.exit(1)
    print_vars(board, vars, rowsums, colsums)
    return vars

  # didn't use a decorator because I want to define and call at once
  def accelerator(msg, func):
    if func(board, rowsums, colsums):
      print(f"board after accelerator ({100.0*frac_filled(board):.1f}%): {msg}")
      print_board(board, rowsums, colsums)
      does_solution_match(board, BOARD, rowsums, colsums, True, True)
      return True
    print(f"no change after accelerator: {msg}")
    return False

  def place_grass(board, y, x, msg=None):
    # note: not for use on mini-boards bec of does_solution_match() call
    board[y][x] = GRASS
    print(f"placed grass on {y:2},{x:2}{(': '+msg) if msg else ''}")
    does_solution_match(board, BOARD, rowsums, colsums, True, True)
    return True
  def place_tent(board, y, x, msg=None):
    # note: not for use on mini-boards bec of does_solution_match() call
    board[y][x] = TENT
    print(f"placed  tent on {y:2},{x:2}{(': '+msg) if msg else ''}")
    does_solution_match(board, BOARD, rowsums, colsums, True, True)
    grass_around_tent(board, y, x)
    return True

  def grass_on_zero_remaining(board, rowsums, colsums, changed=False):
    for y in range(board_height(board)):
      for x in range(board_width(board)):
        if board[y][x] != EMPTY: continue
        if colsums[x] == 0:
          changed |= place_grass(board, y, x, f"grass_on_zero_remaining: colsum[{x}]=0")
        if rowsums[y] == 0:
          changed |= place_grass(board, y, x, f"grass_on_zero_remaining: rowsum[{y}]=0")
    # if no remaining, then grass over remaining cells in the row
    for y in range(board_height(board)):
      numtents = 0
      for x in range(board_width(board)):
        if board[y][x] == TENT:
          numtents += 1
      if numtents == rowsums[y]:
        for x in range(board_width(board)):
          if board[y][x] == EMPTY:
            changed |= place_grass(board, y, x, f"grass_on_zero_remaining: numtents={numtents} rowsum[{y}]={rowsums[y]}")
    # if no remaining, then grass over remaining cells in the column
    for x in range(board_width(board)):
      numtents = 0
      for y in range(board_height(board)):
        if board[y][x] == TENT:
          numtents += 1
      if numtents == colsums[x]:
        for y in range(board_height(board)):
          if board[y][x] == EMPTY:
            changed |= place_grass(board, y, x, f"grass_on_zero_remaining: numtents={numtents} colsum[{x}]={colsums[x]}")
    return changed

  def add_tree_tent_constraints(model, board, vars):
    num_constraints = 0
    for y in range(len(board)):
      for x in range(len(board[0])):
        if board[y][x] == TREE:
          empty_neighbors = []
          for dy,dx in SQUARE_NEIGHBOR_OFFSETS:
            if get_cell(board,y+dy,x+dx) == TENT:
              if DBG_CONSTRAINT: print(f"tree@{y},{x} has neighboring tent and doesn't need a constraint")
              break
            if get_cell(board,y+dy,x+dx) == EMPTY:
              empty_neighbors.append(vars[y+dy][x+dx])
          else:
            if len(empty_neighbors) == 0:
              if DBG_CONSTRAINT: print(f"tree@{y},{x} has no neighboring empties tent and doesn't need a constraint")
              continue
            model.Add(sum(empty_neighbors) >= 1)  # ignore if a tent is found
            num_constraints += 1
            if DBG_CONSTRAINT: print(f"tree must be next to tents: {y},{x}: {empty_neighbors} >= 1")
    return num_constraints

  def add_tent_tent_constraints(model, board, vars):
    num_constraints = 0
    # no tent can be adjacent to another tent - one tent per 2x2 grid
    for y in range(len(board)):
      for x in range(len(board[0])):
        empty_neighbors = [vars[y+dy][x+dx] for dy,dx in TWOBYTWO_NEIGHBOR_OFFSETS
                           if get_cell(board,y+dy,x+dx) == EMPTY ]
        tent_neighbors = [vars[y+dy][x+dx] for dy,dx in TWOBYTWO_NEIGHBOR_OFFSETS
                          if get_cell(board,y+dy,x+dx) == TENT ]
        if len(empty_neighbors) > 1:
          if DBG_CONSTRAINT: print(f"no tent adjacency: sum(empty_neighbors={empty_neighbors} + tent_neighbors={tent_neighbors} <= 1)")
          model.Add(sum(empty_neighbors + tent_neighbors) <= 1)
          num_constraints += 1
    return num_constraints

  def solve_miniboards(board, rowsums, columns, changed=False):
    # look at a smaller subset of the board and see if there's only one possible solution
    # (obviously, we don't have colsums/rowsums but we still have adjacency rules)
    for y in [4*i for i in range(int(board_height(board) / 4))]:  # every Nth
      for x in [4*i for i in range(int(board_width(board) / 4))]:  # every Nth
        minimodel = cp_model.CpModel()
        minisolver = cp_model.CpSolver()
        def ncell(y,x):  # neighboring cell
          return WALL if get_cell(board,y,x) == WALL else EMPTY
        # surround the miniboard with the neighboring cells, to avoid the fatally-bad assumption that they're walls
        # TODO: breaks code... need to actually shrink the board on the side(s) with walls...
        miniboard = [ [ ncell(y-1,x-1), ncell(y-1,x+0), ncell(y-1,x+1), ncell(y-1,x+2), ncell(y-1,x+3), ncell(y-1,x+4) ],
                      [ ncell(y+0,x-1), board[y+0][x+0], board[y+0][x+1], board[y+0][x+2], board[y+0][x+3], ncell(y+0,x+4) ],
                      [ ncell(y+1,x-1), board[y+1][x+0], board[y+1][x+1], board[y+1][x+2], board[y+1][x+3], ncell(y+1,x+4) ],
                      [ ncell(y+2,x-1), board[y+2][x+0], board[y+2][x+1], board[y+2][x+2], board[y+2][x+3], ncell(y+2,x+4) ],
                      [ ncell(y+3,x-1), board[y+3][x+0], board[y+3][x+1], board[y+3][x+2], board[y+3][x+3], ncell(y+3,x+4) ],
                      [ ncell(y+4,x-1), ncell(y+4,x+0), ncell(y+4,x+1), ncell(y+4,x+2), ncell(y+4,x+3), ncell(y+4,x+4) ] ]
        minivars = create_vars(minimodel, miniboard)
        print(f"miniboard: 4x4 @ {y},{x}")
        print_board(miniboard)
        add_tree_tent_constraints(minimodel, miniboard, minivars)
        add_tent_tent_constraints(minimodel, miniboard, minivars)
        callback = SolutionPrinter(miniboard, minivars)
        status = minisolver.SearchForAllSolutions(minimodel, callback)
        if status == cp_model.INFEASIBLE:
          print("oops! miniboard solver says INFEASIBLE")
          return
        if status == cp_model.MODEL_INVALID:
          print("oops! miniboard solver says MODEL_INVALID")
          return
        if status == cp_model.UNKNOWN:
          print("oops! miniboard solver says UNKNOWN / timeout")
          return
        for dy in range(4):
          for dx in range(4):
            if board[y+dy][x+dx] != EMPTY:
              continue
            miniboards = callback.SolutionBoards()
            for miniboard in miniboards[1:]:
              if miniboard[dy][dx] != miniboards[0][dy][dx]:
                break
            else:
              # on every board, the value is the same
              if miniboards[0][dy][dx] == GRASS:
                changed |= place_grass(board, y+dy, x+dx, msg="placing grass - all 4x4 miniboard solutions demand it.")
              elif miniboards[0][dy][dx] == TENT:
                changed |= place_tent(board, y+dy, x+dx, msg="placing tent - all 4x4 miniboard solutions demand it.")
    return changed
  
  def solve_rowcol_subsets(board, rowsums, columns, changed=False):
    # look at 2-3 rows/columns at once and see if they have only one solution.
    # (we have either colsums or rowsums but not both, and still have adjacency rules)
    for y in range(board_height(board)-1):
      valcounts = {EMPTY: 0, TREE: 0, TENT: 0, GRASS: 0, WALL: 0}
      for x in range(board_width(board)):
        valcounts[get_cell(board, y, x)] += 1
        valcounts[get_cell(board, y+1, x)] += 1
      # 2x2 can only house one
      if valcounts[EMPTY] + valcounts[TENT] == rowsums[y] + rowsums[y+1]:
        print(f"TODO: fill two rows: valcounts[{valcounts[EMPTY] + valcounts[TENT]}: EMPTY={valcounts[EMPTY]} + TENT={valcounts[TENT]}] ?=? rowsums[{y}-{y+1}]={rowsums[y] + rowsums[y+1]}: {rowsums[y]} & {rowsums[y+1]}]")
        print(f"yep, I'd fill that.")
    return changed
  
  def grass_around_trees_with_assigned_tents(board, rowsums, columns, changed=False):
    # SEED=9860347 SIZE=24x24
    # placed grass on 12, 0: grassing around assigned tree @13,0
    # placed grass on 20, 0: grassing around assigned tree @21,0
    for y in range(board_height(board)):
      for x in range(board_width(board)):
        if board[y][x] != TREE:
          break
        # tree must have exactly one tent neighbor (TODO: remove this limitation?)
        tent_neighbors = [[y+dy,x+dx] for dy,dx in SQUARE_NEIGHBOR_OFFSETS if get_cell(board, y+dy, x+dx) == TENT]
        if len(tent_neighbors) != 1:
          break
        # neighboring tent cannot have other trees next to it (n=2+) - could be assigned to that
        tent_neighbor = tent_neighbors[0]
        if 1 != sum([1 for _dy,_dx in SQUARE_NEIGHBOR_OFFSETS if get_cell(board, tent_neighbor[0]+_dy, tent_neighbor[1]+_dx) == TREE]):
          break
        # neighboring empty cells cannot have neighboring tents or trees
        for dy,dx in SQUARE_NEIGHBOR_OFFSETS:
          if get_cell(board, y+dy, x+dx) != EMPTY:
            continue
          empty_cell = [y+dy, x+dx]
          if 1 == sum([1 for _dy,_dx in SQUARE_NEIGHBOR_OFFSETS if get_cell(board, empty_cell[0]+_dy, empty_cell[1]+_dx) in [TREE, TENT]]):
            changed |= place_grass(board, empty_cell[0], empty_cell[1], f"grassing around assigned tree @{y},{x}")
    return changed
          
  def grass_on_right_angles(board, rowsums, columns, changed=False):
    for y in range(board_height(board)):
      for x in range(board_width(board)):
        if board[y][x] == TREE:
          if (get_cell(board, y, x-1) == EMPTY and get_cell(board, y-1, x) == EMPTY and \
              get_cell(board, y, x+1) != EMPTY and get_cell(board, y+1, x) != EMPTY and \
              get_cell(board, y-1, x-1) == EMPTY):
            changed |= place_grass(board, y-1, x-1, f"grass_on_right_angles upper-left tent@{y},{x} vs adj empties at {y},{x-1} and {y-1},{x}")
          if (get_cell(board, y-1, x) == EMPTY and get_cell(board, y, x+1) == EMPTY and \
              get_cell(board, y+1, x) != EMPTY and get_cell(board, y, x-1) != EMPTY and \
              get_cell(board, y-1, x+1) == EMPTY):
            changed |= place_grass(board, y-1, x+1, f"grass_on_right_angles upper-right tent@{y},{x} vs adj empties at {y},{x-1} and {y-1},{x}")
          if (get_cell(board, y, x+1) == EMPTY and get_cell(board, y+1, x) == EMPTY and \
              get_cell(board, y, x-1) != EMPTY and get_cell(board, y-1, x) != EMPTY and \
              get_cell(board, y+1, x+1) == EMPTY):
            changed |= place_grass(board, y+1, x+1, f"grass_on_right_angles lower-right tent@{y},{x} vs adj empties at {y},{x-1} and {y-1},{x}")
          if (get_cell(board, y+1, x) == EMPTY and get_cell(board, y, x-1) == EMPTY and \
              get_cell(board, y-1, x) != EMPTY and get_cell(board, y, x+1) != EMPTY and \
              get_cell(board, y+1, x-1) == EMPTY):
            changed |= place_grass(board, y+1, x-1, f"grass_on_right_angles lower-left tent@{y},{x} vs adj empties at {y},{x-1} and {y-1},{x}")
    return changed

  def fill_singles_if_sums_match(board, rowsums, columns, changed=False):
    for y in range(board_height(board)):
      empty_singles, empty_doubles, empty_triples, empty_quads, tents = [], [], [], [], []
      for x in range(board_width(board)):
        if board[y][x] == TENT:
          tents.append(x)
        elif is_empty_single_in_row(board, y, x):
          empty_singles.append(x)
        elif is_empty_double_in_row(board, y, x):
          empty_doubles.append(x)
        elif is_empty_triple_in_row(board, y, x):
          empty_triples.append(x)
        elif is_empty_quad_in_row(board, y, x):
          empty_quads.append(x)
        elif is_empty_fiveplus_in_row(board, y, x):
          break
      else:
        if len(tents) + len(empty_singles) + len(empty_doubles) + 2*len(empty_triples) + 2*len(empty_quads) == rowsums[y]:
          localchg = False
          for x in empty_singles:
            localchg |= place_tent(board, y, x, f"fill_singles_if_sums_match (single-row) @{y},{x}")
          for x in empty_triples:
            localchg |= place_tent(board, y, x+2, f"fill_singles_if_sums_match (triple-row) @{y},{x+2}")
          for x in empty_doubles:
            for dy,dx in [ [-1,0], [1,0], [-1,1], [1,1] ]: # squares around the double
              if get_cell(board, y+dy, x+dx) == EMPTY:
                localchg |= place_grass(board, y+dy, x+dx, f"fill adjacent-to-doubles in row @{y}")
          changed |= localchg
          #print_board(board, rowsums, colsums)
          if localchg: print(f"fill by row: y={y} singles={empty_singles} dbls={empty_doubles} trips=2*{empty_triples} quads=2*{empty_quads} tents={tents} sum={rowsums[y]} ")
        elif len(tents) + len(empty_singles) + len(empty_doubles) + 2*len(empty_triples) + 2*len(empty_quads) == rowsums[y] + 1:           
          # one extra single/double - shoot out neighbors...
          for i in range(len(empty_singles) - 1):
            if empty_singles[i+1] - empty_singles[i] == 2:  # g g g  <= grass
              if get_cell(board, y-1, empty_singles[i]+1) == EMPTY:
                changed |= place_grass(board, y-1, empty_singles[i]+1, f"fill adjacent-to-singles in row @{y}")
              if get_cell(board, y+1, empty_singles[i]+1) == EMPTY:
                changed |= place_grass(board, y+1, empty_singles[i]+1, f"fill adjacent-to-singles in row @{y}")
          for x in empty_triples:
            for dy,dx in [ [-1,1], [1,1] ]: # squares around the center of the triple
              if get_cell(board, y+dy, x+dx) == EMPTY:
                changed |= place_grass(board, y+dy, x+dx, f"fill adjacent-to-triples in row @{y}")
    #if changed: print_board(board, rowsums, colsums)
    for x in range(board_height(board)):
      empty_singles, empty_doubles, empty_triples, empty_quads, tents = [], [], [], [], []
      for y in range(board_width(board)):
        if board[y][x] == TENT:
          tents.append(y)
        elif is_empty_single_in_col(board, y, x):
          empty_singles.append(y)
        elif is_empty_double_in_col(board, y, x):
          empty_doubles.append(y)
        elif is_empty_triple_in_col(board, y, x):
          empty_triples.append(y)
        elif is_empty_quad_in_col(board, y, x):
          empty_quads.append(y)
        elif is_empty_fiveplus_in_col(board, y, x):
          break
      else:
        if len(tents) + len(empty_singles) + len(empty_doubles) + 2*len(empty_triples) + 2*len(empty_quads) == colsums[x]:
          print_board(board, rowsums, colsums)
          for y in empty_singles:
            changed |= place_tent(board, y, x, f"fill_singles_if_sums_match (single-col) @{y},{x}")
          print_board(board, rowsums, colsums)
          for y in empty_triples:
            changed |= place_tent(board, y+2, x, f"fill_singles_if_sums_match (triple-col) @{y},{x}")
          for y in empty_doubles:
            for dy,dx in [ [0,-1], [0,1], [1,-1], [1,1] ]: # squares around the double
              if get_cell(board, y+dy, x+dx) == EMPTY:
                changed |= place_grass(board, y+dy, x+dx, f"fill adjacent-to-doubles in col @{x}")
          for y in empty_triples:
            for dy,dx in [ [-1,1], [1,1] ]: # squares around the center of the triple
              if get_cell(board, y+dy, x+dx) == EMPTY:
                changed |= place_grass(board, y+dy, x+dx, f"fill adjacent-to-triples in col @{x}")
          #if len(empty_triples)>0: print_board(board, rowsums, colsums)
          if changed: print(f"fill by col: x={x} singles={empty_singles} dbls={empty_doubles} trips=2*{empty_triples} quads=2*{empty_quads} tents={tents} sum={colsums[x]} ")
        elif len(tents) + len(empty_singles) + len(empty_doubles) + 2*len(empty_triples) + 2*len(empty_quads) == colsums[x] + 1:
          # one extra single/double - shoot out neighbors...
          for i in range(len(empty_singles) - 1):
            if empty_singles[i+1] - empty_singles[i] == 2:  # g g g  <= grass
              if get_cell(board, empty_singles[i]+1, x-1) == EMPTY:
                changed |= place_grass(board, empty_singles[i]+1, x-1, f"fill adjacent-to-singles for empty in {empty_singles[i]},{x}")
              if get_cell(board, empty_singles[i]+1, x+1) == EMPTY:
                changed |= place_grass(board, empty_singles[i]+1, x+1, f"fill adjacent-to-singles for empty in {empty_singles[i]},{x}")
          for y in empty_triples:
            for dy,dx in [ [1,-1], [1,1] ]: # squares around the center of the triple
              if get_cell(board, y+dy, x+dx) == EMPTY:
                changed |= place_grass(board, y+dy, x+dx, f"fill adjacent-to-triples in col @{x}")
    #if changed: print_board(board, rowsums, colsums)
    return changed

  def grass_around_tent(board, y, x, changed=False):
    for dy,dx in ALL_NEIGHBOR_OFFSETS:
      if get_cell(board,y+dy,x+dx) == EMPTY:
        changed |= place_grass(board, y+dy, x+dx, f"grass_around_tent at {y:2},{x:2}")
    return changed

  def grass_around_tents(board, rowsums, columns, changed=False):
    for y in range(board_height(board)):
      for x in range(board_width(board)):
        if board[y][x] == TENT:
          changed |= grass_around_tent(board, y, x)
    return changed

  def place_tent_next_to_lonely_trees(board, rowsums, columns, changed=False):
    # lonely = one empty cell available = empty must be a tent
    for y in range(board_height(board)):
      for x in range(board_width(board)):
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
              changed |= place_tent(board, empty_cell[0], empty_cell[1], f"place tent next to lonely trees")
    return changed

  def deductive_solver():
    while True:
      if not ( # changed...
          accelerator("put grass on cells with zero remaining", grass_on_zero_remaining) or
          accelerator("fill singles if count matches rowsums", fill_singles_if_sums_match) or
          accelerator("place tents next to trees with one empty cell", place_tent_next_to_lonely_trees) or
          accelerator("put grass around tents", grass_around_tents) or
          accelerator("grass in the diagonal of a tree with right-angle empties", grass_on_right_angles) or
          accelerator("grass around assigned tents", grass_around_trees_with_assigned_tents) or
          #accelerator("try solving rowcol subsets", solve_rowcol_subsets) or
          False):
        break

  deductive_solver()
  #while solve_miniboards(board, rowsums, colsums):
  #  deductive_solver()
      
  if not has_empty(board):
    if not is_one_tree_per_tent(board):
      print("error! after accelerator - is_one_tree_per_tent(board) == False")
      sys.exit(1)
    if does_solution_match(board, BOARD, rowsums, colsums, print_mismatches=True):
      print("success! after accelerator - and it matches")
      sys.exit(0)
    print("success! after accelerator - but it doesn't match (new solution)")
    sys.exit(0)
  
  #print_board(board, rowsums, colsums)
  def add_rowcol_constraints(model, board, rowsums, colsums, vars):
    num_constraints = 0
    for y in range(board_height(board)):
      # skip rows with no empty cells
      if sum([1 for x in range(board_width(board)) if board[y][x] == EMPTY]) == 0:
        continue
      rowsum_vars = [vars[y][x] for x in range(board_width(board))]
      if DBG_CONSTRAINT: print(f"rowsum[{y}]: {rowsums[y]} = sum({rowsum_vars})")
      model.Add(rowsums[y] == sum(rowsum_vars))
      num_constraints += 1
    for x in range(board_width(board)):
      # skip columns with no empty cells
      if sum([1 for y in range(board_height(board)) if board[y][x] == EMPTY]) == 0:
        continue
      colsum_vars = [vars[y][x] for y in range(board_height(board))]
      if DBG_CONSTRAINT: print(f"colsum[{x}]: {colsums[x]} = sum({colsum_vars})")
      model.Add(colsums[x] == sum(colsum_vars))
      num_constraints += 1
    return num_constraints

  model = cp_model.CpModel()
  vars = create_vars(model, board)
  num_constraints = 0
  num_constraints += add_rowcol_constraints(model, board, rowsums, colsums, vars)
  num_constraints += add_tree_tent_constraints(model, board, vars)
  num_constraints += add_tent_tent_constraints(model, board, vars)

  print(f"num_constraints={num_constraints}")
  solver = cp_model.CpSolver()
  callback = SolutionPrinter(board, vars)
  solver.parameters.max_time_in_seconds = SOLVER_TIMEOUT
  solver.parameters.random_seed = SEED
  #print(dir(solver.parameters))
  #solver.parameters.search_branching = cp_model.FIXED_SEARCH  #PORTFOLIO_SEARCH  #FIXED_SEARCH
  status = solver.SearchForAllSolutions(model, callback)
  #status = solver.SolveWithSolutionCallback(model, callback)  # errors for some reason?
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
    if does_solution_match(soln_board, BOARD, rowsums, colsums):
      print("success! valid solution, and it matches.")
      sys.exit(0)
    else:
      print("success! valid solution, but it doesn't match (new solution)...")
      print_board(soln_board, rowsums, colsums)
      print("expected:")
      print_board(BOARD, rowsums, colsums)
      sys.exit(0)

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
solver_setup(SOLVER_BOARD)

print("running the solver...")
ortools_cpsat_solver(SOLVER_BOARD, ROWSUMS, COLSUMS)
