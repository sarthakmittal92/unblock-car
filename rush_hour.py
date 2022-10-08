import z3
import sys

######################################## FUNCTIONS ############################################
# Assign values to board
def assign (point, type):
    global board
    [i, j] = point
    if board[i][j] != 0 and board[i][j] != 3:
        print('unsat')
        sys.exit(0)
    board[i][j] = type + 1

# Find number of cars/mines
def findCounts (board):
    global n
    vCars = [0 for i in range(n)]
    hCars = [0 for i in range(n)]
    vMines = [0 for i in range(n)]
    hMines = [0 for i in range(n)]
    for i in range(n):
        for j in range(n):
            if board[i][j] == 1:
                vCars[j] += 1
            elif board[i][j] == 2:
                hCars[i] += 1
            elif board[i][j] == 3:
                vMines[j] += 1
                hMines[i] += 1
    return [vCars, hCars, vMines, hMines]

# Get head for the tail
def tailToHead (tail, type):
    if type == 0:
        return [tail[0] + 1, tail[1]]
    elif type == 1 or type == 3:
        return [tail[0], tail[1] + 1]
    else:
        return tail

# Fill in the car/mine
def fillBoard (point, type):
    assign(point, type)
    assign(tailToHead(point, type), type)

# Print moves in model
def printer (s,steps):
    m = s.model()
    for l in range(steps):
        count = 0
        for i in range(n):
            for j in range(n):
                x = str(m.evaluate(Y[l][i][j]))
                y = str(m.evaluate(Y[l + 1][i][j]))
                if x != y:
                    if count == 0:
                        p1 = i
                        q1 = j
                        count += 1
                    else:
                        p2 = i
                        q2 = j
        print((p1 + p2) // 2, (q1 + q2) // 2, sep=',')
###############################################################################################

########################################### INPUT #############################################
inputFile = sys.argv[1]
file = open(inputFile, 'r')

# Parameters
info = list(map(int, file.readline().strip().split(',')))
n = info[0]
k = info[1]

board = [[0 for i in range(n)] for j in range(n)]

# Red car parameters
redCarInfo = list(map(int, file.readline().strip().split(',')))
fillBoard(redCarInfo, 3)
redRowIndex = redCarInfo[0]
redCol = redCarInfo[1]

# Fill in all cars/mines from input
for line in file:
    info = list(map(int, line.strip().split(',')))
    type = info[0]
    point = [info[1], info[2]]
    fillBoard(point, type)

vCars, hCars, vMines, hMines = findCounts(board)

# z3 variables
Y = [[[z3.Int("x_%s_%s_%s" % (l, i, j)) for j in range(n)] for i in range(n)] for l in range(k + 1)]
s = z3.Solver()
###############################################################################################

######################################### MOVES ###############################################
for l in range(k + 1):

    # print(l)
    X = Y[l]
    # basic conditions carrying over from previous position
    bounds = [z3.And(0 <= X[i][j], X[i][j] <= 4) for i in range(n) for j in range(n)]
    vertical = [z3.PbEq([(X[i][j] == 1, 1) for i in range(n)], vCars[j]) for j in range(n)]
    horizontal = [z3.PbEq([(X[i][j] == 2, 1) for j in range(n)], hCars[i]) for i in range(n)]
    minesVert = [z3.PbEq([(X[i][j] == 3, 1) for i in range(n)], vMines[j]) for j in range(n)]
    minesHori = [z3.PbEq([(X[i][j] == 3, 1) for j in range(n)], hMines[i]) for i in range(n)]
    redCarRest = [z3.PbEq([(X[redRowIndex][j] == 4, 1) for j in range(n)], 2)]
    uniqueRedCar = [z3.PbEq([(X[i][j] == 4, 1) for j in range(n) for i in range(n)], 2)]
    redCarNeigh = [z3.PbEq([(z3.And(X[redRowIndex][j] == 4, X[redRowIndex][j + 1] == 4), 1) for j in range(n - 1)], 1)]
    hLones = [z3.Not(z3.And(X[i][j] == 2, z3.And(z3.Or(j == n - 1, X[i][j + 1] != 2), z3.Or(j == 0, X[i][j - 1] != 2))))
              for j in range(n - 1) for i in range(n)]
    vLones = [z3.Not(z3.And(X[i][j] == 1, z3.And(z3.Or(i == n - 1, X[i + 1][j] != 1), z3.Or(i == 0, X[i - 1][j] != 1))))
              for i in range(n - 1) for j in range(n)]
    hLonesLast = [z3.Not(z3.And(X[i][n - 1] == 2, X[i][n - 2] != 2)) for i in range(n)]
    vLonesLast = [z3.Not(z3.And(X[n - 1][j] == 1, X[n - 2][j] != 1)) for j in range(n)]

    # add to solver
    s.add(bounds)
    s.add(vertical)
    s.add(horizontal)
    s.add(minesVert)
    s.add(minesHori)
    s.add(redCarRest)
    s.add(uniqueRedCar)
    s.add(redCarNeigh)
    s.add(hLones)
    s.add(vLones)
    s.add(hLonesLast)
    s.add(vLonesLast)

    # initialise
    if l == 0:
        init = [z3.PbEq([(X[i][j] == board[i][j], 1) for j in range(n) for i in range(n)], n * n)]
        s.add(init)
    else:
        # update exactly 2 positions
        update = [z3.PbEq([(Y[l][i][j] == Y[l - 1][i][j], 1) for j in range(n) for i in range(n)], n * n - 2)]

        # check that exactly 1 car moved
        lst = []
        for i in range(n-1):
            for j in range(n):
                if 0 < i < n-2:
                    lst.append((z3.And(z3.And(Y[l - 1][i][j] == 1, Y[l - 1][i + 1][j] == 1),
                                       z3.Xor(Y[l][i][j] == 1, Y[l][i + 1][j] == 1),
                                       z3.Or(z3.And(Y[l][i][j] == 0, Y[l - 1][i + 2][j] == 0, Y[l][i + 2][j] == 1),
                                             z3.And(Y[l][i + 1][j] == 0, Y[l - 1][i - 1][j] == 0, Y[l][i - 1][j] == 1))), 1))
                elif 0 == i:
                    lst.append((z3.And(z3.And(Y[l - 1][i][j] == 1, Y[l - 1][i + 1][j] == 1),
                                       z3.Xor(Y[l][i][j] == 1, Y[l][i + 1][j] == 1),
                                       z3.And(Y[l][i][j] == 0, Y[l - 1][i + 2][j] == 0, Y[l][i + 2][j] == 1)), 1))
                elif i == n-2:
                    lst.append((z3.And(z3.And(Y[l - 1][i][j] == 1, Y[l - 1][i + 1][j] == 1),
                                       z3.Xor(Y[l][i][j] == 1, Y[l][i + 1][j] == 1),
                                       z3.And(Y[l][i + 1][j] == 0, Y[l - 1][i - 1][j] == 0, Y[l][i - 1][j] == 1)), 1))
        
        for j in range(n-1):
            for i in range(n):
                if 0 < j < n-2:
                    lst.append((z3.And(z3.And(Y[l - 1][i][j] == 2, Y[l - 1][i][j + 1] == 2),
                                       z3.Xor(Y[l][i][j] == 2, Y[l][i][j + 1] == 2),
                                       z3.Or(z3.And(Y[l][i][j] == 0, Y[l - 1][i][j + 2] == 0, Y[l][i][j + 2] == 2),
                                             z3.And(Y[l][i][j + 1] == 0, Y[l - 1][i][j - 1] == 0, Y[l][i][j - 1] == 2))), 1))
                elif 0 == j:
                    lst.append((z3.And(z3.And(Y[l - 1][i][j] == 2, Y[l - 1][i][j + 1] == 2),
                                       z3.Xor(Y[l][i][j] == 2, Y[l][i][j + 1] == 2),
                                       z3.And(Y[l][i][j] == 0, Y[l - 1][i][j + 2] == 0, Y[l][i][j + 2] == 2)), 1))
                elif j == n-2:
                    lst.append((z3.And(z3.And(Y[l - 1][i][j] == 2, Y[l - 1][i][j + 1] == 2),
                                       z3.Xor(Y[l][i][j] == 2, Y[l][i][j + 1] == 2),
                                       z3.And(Y[l][i][j + 1] == 0, Y[l][i][j - 1] == 0, Y[l][i][j - 1] == 2)), 1))
        
        for j in range(n-1):
            i = redRowIndex
            if 0 < j < n-2:
                lst.append((z3.And(z3.And(Y[l - 1][i][j] == 4, Y[l - 1][i][j + 1] == 4),
                                   z3.Xor(Y[l][i][j] == 4, Y[l][i][j + 1] == 4),
                                   z3.Or(z3.And(Y[l][i][j] == 0, Y[l - 1][i][j + 2] == 0, Y[l][i][j + 2] == 4),
                                         z3.And(Y[l][i][j + 1] == 0, Y[l - 1][i][j - 1] == 0, Y[l][i][j - 1] == 4))), 1))
            elif 0 == j:
                lst.append((z3.And(z3.And(Y[l - 1][i][j] == 4, Y[l - 1][i][j + 1] == 4),
                                   z3.Xor(Y[l][i][j] == 4, Y[l][i][j + 1] == 4),
                                   z3.And(Y[l][i][j] == 0, Y[l-1][i][j + 2] == 0, Y[l][i][j + 2] == 4)), 1))
            elif j == n-2:
                lst.append((z3.And(z3.And(Y[l - 1][i][j] == 4, Y[l - 1][i][j + 1] == 4),
                                   z3.Xor(Y[l][i][j] == 4, Y[l][i][j + 1] == 4),
                                   z3.And(Y[l][i][j + 1] == 0, Y[l][i][j - 1] == 0, Y[l][i][j - 1] == 4)), 1))
        
        upd = z3.PbEq(lst, 1)
        
        # none of the mines move
        vertMineUpdate = [z3.PbEq([(z3.And(Y[l - 1][i][j] == 3, Y[l][i][j] == 3), 1) for i in range(n)], vMines[j]) for
                          j in range(n)]
        horiMineUpdate = [z3.PbEq([(z3.And(Y[l - 1][i][j] == 3, Y[l][i][j] == 3), 1) for j in range(n)], hMines[i]) for
                          i in range(n)]

        # add to solver
        s.add(update)
        s.add(upd)
        s.add(vertMineUpdate)
        s.add(horiMineUpdate)
    
    # goal clause so far
    solution = [z3.PbEq([(z3.And(Y[l1][redRowIndex][n - 2] == 4, Y[l1][redRowIndex][n - 1] == 4),1) for l1 in range(l + 1)],1)]
    
    # check goal
    s.push()
    s.add(solution)
    if s.check() == z3.sat:
        printer(s,l)
        sys.exit(0)
    else:
        if l == k:
            print('unsat')
        s.pop()