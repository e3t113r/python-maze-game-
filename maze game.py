import random
import pygame
import math
import heapq
from collections import deque


class Cell: #stores wall information about the cell
    def __init__(self, x, y):
        self._x, self._y = x, y #ints
        self._walls = {'top': True, #the walls are a dictionary of booleans just to check if they have that wall in that direction
                       'bottom': True,
                       'left': True,
                       'right': True}
        self._visited = False #kept in cell class as it's only describing a singular cell


    def getPosition(self): #put in a method for less confusion
        return self._x, self._y #(x,y) coordinate -- a tuple


    def getWalls(self): #put in a method for less confusion
        return self._walls #dictionary of tuples : {wall : boolean}
   
    def removeWalls(self, neighbour):
        nx, ny = neighbour.getPosition() #return int (x,y) coordinates of neighbour cell
        if self._y - ny == 1: #current pos - neighbour pos to find which direction it's trying to head in
            self._walls['top'] = False
            neighbour._walls['bottom'] = False #set all connected walls as False to clear a path
        elif self._y - ny == -1:
            self._walls['bottom'] = False
            neighbour._walls['top'] = False
        elif self._x - nx == 1:
            self._walls['left'] = False
            neighbour._walls['right'] = False
        elif self._x - nx == -1:
            self._walls['right'] = False
            neighbour._walls['left'] = False
   


class Maze:
    def __init__(self, rows, cols):
        self._rows = rows #int : in this case should be 800//40
        self._cols = cols #int : in this case should be 600//40
        self.cells = {(x, y): Cell(x, y) for y in range(rows) for x in range(cols)} #eg {(0,0)} -> returns state of walls
        self.graph = {pos: [] for pos in self.cells} #eg {(0,0) : (1, 0), (0,1)} -> a dictionary of tuples about tuples (connected cells)
        self.start = (0, 0) #top left corner
        self.destination = (self._cols-1, self._rows-1) #bottom right corner


    def removeSpecificWall(self, og, neighbour, ogWall, neighbourWall):
        og._walls[ogWall] = False #update that particular direction's wall to no more wall
        neighbour._walls[neighbourWall] = False #and the wall directly connected to that


    def getNeighbours(self, cell):
        neighbours = []
        x, y = cell.getPosition() #load in that cell's coordinates
        #directions are saved as a list of tuples
        directions = [(0, -1, 'top', 'bottom'), #(dx, dy, wall direction, opp wall direction)
                      (0, 1, 'bottom', 'top'),
                      (1, 0, 'left', 'right'),
                      (-1, 0, 'right', 'left')]
        for dx, dy, wall, oppWall in directions: #describes what's inside the tuples
            nx, ny = x+dx, y+dy #coord of neighbour
            if (nx, ny) in self.cells and not self.cells[(nx, ny)]._visited:  #cell chosen is adjacent and has not been visited
                neighbours.append((self.cells[(nx, ny)], wall, oppWall)) #add into neighbours
        return neighbours


    def generateMaze(self, x, y): #guarantee at least 1 path solvable
        stack = [(x, y)] #start with initial cell on stack
        visited = set() #init visited stack
       
        while stack:
            cx, cy = stack[-1] #from the top of the stack
            visited.add((cx, cy)) #mark as visited
            neighbours = [(cx+dx, cy+dy) for dx, dy in [(0,-1), (0,1), (-1,0), (1,0)]
                         if (cx+dx, cy+dy) in self.cells and (cx+dx, cy+dy) not in visited]
            #neighbours update the cell in the right direction as long as its in range of
            #maze dimensions and have not been visited
           
            if neighbours:
                nx, ny = random.choice(neighbours) #randomly choose a neighbour from list of items
                self.cells[(cx, cy)].removeWalls(self.cells[(nx, ny)])  #remove wall between current and chosen cell
                self.graph[(cx, cy)].append((nx, ny)) #update the graph
                self.graph[(nx, ny)].append((cx, cy))
                stack.append((nx, ny)) #move to new cell
            else:
                stack.pop() #backtracK if no more unvisited cells
   
    def removeExtraWalls(self): #removes random walls to make maze contain more than one path
        for (x, y), cell in self.cells.items(): #cell in range
            for direction in cell._walls.keys(): #in the dictionary of walls load direction = "top" etc
                if cell._walls[direction] and random.random() < 0.1: #
                    # Determine neighbor's coordinates
                    nx, ny = x, y #just in case
                    if direction == 'top':    
                        ny -= 1
                    elif direction == 'bottom':
                        ny += 1
                    elif direction == 'left':  
                        nx -= 1
                    elif direction == 'right':  
                        nx += 1
                    if (nx, ny) in self.cells:
                        neighbor = self.cells[(nx, ny)]
                        cell._walls[direction] = False
                        #find the wall connecting to its own
                        opposite = {'top': 'bottom',
                                    'bottom': 'top',
                                    'left': 'right',
                                    'right': 'left'}
                        neighbor._walls[opposite[direction]] = False #remove that wall
        self.updateGraph() #ensure graph is properly saved




    def updateGraph(self): #update graph based on current walls #tihs is made as an emergency reset
        for (x, y), cell in self.cells.items():
            self.graph[(x, y)] = [] #reset every key's neighbour in the dictionary
            if not cell._walls['top'] and (x, y-1) in self.cells: #check all 4 directions
                 self.graph[(x, y)].append((x, y-1))
            if not cell._walls['bottom'] and (x, y+1) in self.cells:
                self.graph[(x, y)].append((x, y+1))
            if not cell._walls['left'] and (x-1, y) in self.cells:
                self.graph[(x, y)].append((x-1, y))
            if not cell._walls['right'] and (x+1, y) in self.cells:
                self.graph[(x, y)].append((x+1, y))




    def generateStarsLocation(self, maze, num):
        positions = list(maze.cells.keys()) #get all available cell positions
        positions = [pos for pos in positions if pos !=self.start and pos != self.destination] #exclude start and destination
        starsLocation = random.sample(positions, num) # randomly generate num positions (new list each time)
        return starsLocation #a list




class AutoSolver:
    def __init__(self, maze):
        self.maze = maze
        self.__shortestPath = [] #stores shortest path after running Dijkstra
        self.__priorityQueue = [] #priority queue modelled using heap to select the node with shortest distance


    def newDijkstra(self, start, end):
        distance = {node : float('+inf') for node in self.maze.graph} #set all distance to inf
        previous = {node: None for node in self.maze.graph} #stores the cell that came before each node along the shortest path
        distance[start] = 0 #set starting cell
        self.__priorityQueue = [(0, start)] #distance, node -- this places start node in priority queue


        while self.__priorityQueue: #keep visiting closest unvisited nodes
            currentDist, currentNode = heapq.heappop(self.__priorityQueue)
            if currentNode == end: #reached target node so stop
                break
            for neighbour in self.maze.graph[currentNode]: #every neighbour in that node
                newDist = currentDist + 1 #increment distance by 1 as my graph not weighted right now
                if newDist < distance[neighbour]:
                    distance[neighbour] = newDist
                    previous[neighbour] = currentNode
                    heapq.heappush(self.__priorityQueue, (newDist, neighbour)) #add


        path, step = [], end #start reconstructing path
        while step is not None:
            path.append(step) #add current node to path
            step = previous[step] #take 1 step back in path
            shortestPath = path[::-1] #path is in reverse order so reverse path to get from start to end
        self.setShortestPath(shortestPath)




    def getShortestPath(self, start, end): #direcctly call for use by obstacles
        self.newDijkstra(start, end)
        return self.__shortestPath
   
    def setShortestPath(self, shortestPath):
        self.__shortestPath = shortestPath








class Player: #handles player movements
    def __init__(self, x, y, maze):
        self._x, self._y = x, y #int coordinates
        self.maze = maze #instantiated in game class
        self.autoSolver = AutoSolver(maze) #aggregated from AutoSolver
       
    def updatePlayerPosition(self, dx, dy): #dx, dy is direction it's going in (eg go right would be (1,0))
        nx, ny = self._x+dx, self._y+dy #move to next cell
        if (nx, ny) in self.maze.graph[(self._x, self._y)]: #check if no walls in between the 2 cells
            self.setPosition(nx, ny) #only update position if there's no walls in between


    def setPosition(self, x, y): #chooses position; made for clarity's sake
        self._x, self._y = x, y #int coordinates
       
    def getPosition(self): #returns position ; made for clarity's sake
        return self._x, self._y






class Obstacle(Player): #inherited handling positions from player class ; this is a static class
    def __init__(self, x, y ,maze, difficulty):
        super().__init__(x, y, maze) #inherit from Player class
        self.__difficulty = difficulty #str ; will be instantiated in game class


    def getDifficulty(self):
        return self.__difficulty #str
   
    def setDifficulty(self, difficulty):
        self.__difficulty = difficulty #str


    def moveTowardsPlayer(self, end):
        start = self.getPosition() #get obstacle's own position
        path = self.autoSolver.getShortestPath(start, end) #should be start being own position and end the user's
        if not path or len(path) < 2:  #Nowhere to go or already at target
            return  
        else:
            self.setPosition(*path[1]) #break tuple into 2 int values ; choose the 1 step in path (as path[0] is its current position)


    #normal exclusive movement - - - - - - - - - - -


    def setTarget(self, target): #return a coord tuple (x, y) eg (12, 3) | chooses which cell to teleport to
        self._target = target


    def getTarget(self): #made for clarity's sake
        return self._target
   
    def decideLandingSpot(self, player): #shld update in a way that's accounts for considering cell status
        path = self.autoSolver.getShortestPath(self.getPosition(), player.getPosition()) #uses Dijkstra to calculate best path
        self.setTarget(path[random.randint(1, len(path)-1)]) #like any random location on path ; path[5] for example


    #hard exclusive movement - - - - - - - - -


    def updateCooldown(self, cooldown): #made individual for hard obstacle to count if wall is moveable
        self._cooldown = cooldown


    def setAllowMoveWall(self):
        if self._cooldown >=2: #every 2 moves it'll be allowed to teleport
            self._canMoveWall = True #confirm moveable
        else:
            self._canMoveWall = False #else reset just in case




    def getAllowMoveWall(self): #wall would be allowed to move
        self.setAllowMoveWall()
        return self._canMoveWall




    def moveWalls(self, target): #decided using BFS
        visited = set() #just an array to store already visited cells for just this run
        queue = deque([(self.getPosition(), [])]) #cells to explore in next BFS ; start from current position of the obstacle
        while queue:
            (x, y), path = queue.popleft() #take the next cell from the queue
            if (x, y) == target:
                return None #already at target no need to move remove walls (just collision avoidance)
            visited.add((x, y)) #keep track of visited nodes
            #define movement directions {'wall direction' : (coordinates of direction to head in)}
            directions = {'top':(0,-1),
                          'bottom':(0,1),
                          'left':(-1,0),
                          'right':(1,0)}
            for direction, (dx, dy) in directions.items(): #direction is the string ; dx, dy is the direction coordinate
                nx, ny = x+dx, y+dy #update final coord
                if (nx, ny) in self.maze.cells: #if the final coord is an existing cell
                    if self.maze.cells[(x,y)]._walls[direction]: #if there is a wall in that direction
                        return ((x,y), (nx,ny), direction) #return the current cell's wall + connected neighbour wall to be removed
                    elif (nx, ny) not in visited:
                        queue.append(((nx, ny), path + [(nx, ny)]))
                #continues until the first blocking wall is found which blocks the obstacle from reaching the player
        return None
   
    def breakWall(self, wall):
        (x1, y1), (x2, y2), direction = wall #decide which wall
        #get opp wall in str
        opposite = {'top' : 'bottom',
                    'bottom' : 'top',
                    'left': 'right',
                    'right': 'left'}[direction]
        self.maze.cells[(x1, y1)]._walls[direction] = False #just break those 2 connected walls
        self.maze.cells[(x2, y2)]._walls[opposite] = False
        self.maze.updateGraph()  #update graph so that it will be drawn properly


    #to be overridden
    def updateMovement(self, player, movesCounter, destination = None): #parameters set this way so no need to update in game class individually
        pass




class EasyObstacle(Obstacle):
    def __init__(self, x, y, maze, difficulty):
        super().__init__(x, y, maze, difficulty)


    def updateMovement(self, player, movesCounter, destination):
        if movesCounter == 0: #doesnt move at first initialising
            self.setPosition(*destination) #starts the obstacle at destination
        elif movesCounter%2==0: #will chase player every 2 moves
            self.moveTowardsPlayer(player.getPosition()) #this returns a tuple (x,y) position of the user passed on to chasing method from obstacle class




class NormalObstacle(Obstacle):
    def __init__(self, x, y, maze, difficulty):
        super().__init__(x, y, maze, difficulty)
        self._target = None #where to teleport to | a tuple (x, y) -> int coord


    def updateMovement(self, player, movesCounter, destination=None):
        if movesCounter%3 ==2: #1 move in advance to run
            self.decideLandingSpot(player)


        elif movesCounter%3 ==0: #every 3 moves
            self.setPosition(*self._target) #teleport
            if self.getTarget() is None: #if no target exist
                self.moveTowardsPlayer(player.getPosition()) #just move
            self._target = None #reset everything
       
        if movesCounter%3 !=0: #chase when not teleporting
            self.moveTowardsPlayer(player.getPosition())




class HardObstacle(Obstacle):
    def __init__(self, x, y, maze, difficulty):
        super().__init__(x, y, maze, difficulty)
        self._cooldown = 0 #allow wall Move
        self._canMoveWall = False #flag to check
   


    def updateMovement(self, player, movesCounter, destination=None): #kept the parameters so game class can use the same call no matter the difficulty
        #no need to update game class if there's change in logic
        target = player.getPosition()
        if not self.getAllowMoveWall(): #
            self.moveTowardsPlayer(target)
            self.updateCooldown(self._cooldown+1)
        else:
            wall = self.moveWalls(target) #choose a wall to break
            if wall: #there is a wall
                self.breakWall(wall) #break it
            self.updateCooldown(0) #update cooldown when there's wall found
     


class UI: #handles all drawings
    def __init__(self, screen, tileSize):
        self.screen = screen #dimension of screen to draw on ; decided in game loop
        self.tileSize = tileSize #should be 40 in this case
        self.font = pygame.font.SysFont("Arial", 32) #for simpler calling
        self.smallFont = pygame.font.SysFont("Arial", 20) #for simpler calling in methods | arial font of size 20


    def drawText(self, text, x, y, font=None, colour=pygame.Color("lightgoldenrod1"), centre=False): #made a separate method for easier coding
        if font is None: #defaulting a font
            font = pygame.font.SysFont("Arial", 28)
        rendered = font.render(text, True, colour) #text is message to be shown on screen | Antialias set as on forever | colour
        rect = rendered.get_rect() #draw the text box
        if centre: #see if necessary
            rect.center = (x, y) #pygame's own function to centre
        else:
            rect.topleft = (x, y) #else just draw from coordinate scale with leftmost order
        self.screen.blit(rendered, rect)


    def drawStartScreen(self): #done
        self.screen.fill(pygame.Color('darkslategray'))
        self.drawText("MAZE GAME",WIDTH // 2, 150, self.font, centre=True)
        pygame.draw.rect(self.screen, pygame.Color('darkslategray'), (WIDTH//2 - 75, 250, 150, 50))
        self.drawText("START", WIDTH // 2, 275, self.font, centre=True)
        self.drawText("Press M", WIDTH // 2, 320, self.smallFont, centre=True)


    def drawMenu(self):
        self.screen.fill(pygame.Color('darkslategray'))
        self.drawText("Choose difficulty",WIDTH // 2, 30, self.font, centre=True)
        self.drawText("Press E for EASY | obstacle will hunt you down from destination", 70, 160, self.smallFont)
        self.drawText("Press N for NORMAL | obstacle will hunt you down by teleporting and chasing", 70, 220, self.smallFont)
        self.drawText("Press H for Hard | Obstacle will now modify maze walls as well", 70, 280, self.smallFont)




    def drawPlaying(self, maze): #draw playing screen
        self.screen.fill('darkslategray')
        self.drawMaze(maze)


    def drawEndScreenTexts(self, state, movesCounter): #get win or lose message and movescounter
        self.screen.fill(pygame.Color('darkslategray'))
        self.drawText(state, WIDTH // 2, 100, self.font, centre=True)
        self.drawText("No. of steps used: ", 150, 150, self.smallFont)
        self.drawText(str(movesCounter), 400, 150, self.smallFont) #the steps used
   
    #THOSE EXTRA NON SCREEN DRAWINGS


    def drawMaze(self, maze):
        for (x, y), cell in maze.cells.items():
            tx, ty = x * self.tileSize, y * self.tileSize #translate to screen px coordinates
            #the walls should be 4px thick -- 2 walls stick to each other so each wall should be drawn 2px wide
            if cell._walls['top']:
                pygame.draw.line(self.screen, ('darkgoldenrod1'), (tx, ty), (tx + self.tileSize, ty), 2)
            if cell._walls['bottom']:
                pygame.draw.line(self.screen, ('darkgoldenrod1'), (tx, ty + self.tileSize), (tx + self.tileSize, ty + self.tileSize), 2)
            if cell._walls['left']:
                pygame.draw.line(self.screen, ('darkgoldenrod1'), (tx, ty), (tx, ty + self.tileSize), 2)
            if cell._walls['right']:
                pygame.draw.line(self.screen, ('darkgoldenrod1'), (tx + self.tileSize, ty), (tx + self.tileSize, ty + self.tileSize), 2)
   
    def drawObject(self, thing, colour): #for obstacles and player too
        x, y = thing.getPosition()
        tx, ty = x*self.tileSize, y*self.tileSize
        pygame.draw.rect(self.screen, colour, (tx+2, ty+2, self.tileSize-2, self.tileSize-2))


    def drawDestination(self): #its own method to prevent confusion later on
        pygame.draw.rect(self.screen, pygame.Color('lightgoldenrod1'), (WIDTH-self.tileSize+2, HEIGHT-self.tileSize+2, self.tileSize+2, self.tileSize-2))
        #walls are 4px wide --> each wall 2px


    def highlightCell(self, target, colour): #for any sudden cells requiring a highlight
        x, y = target
        tx, ty = x*self.tileSize, y*self.tileSize
        pygame.draw.rect(self.screen, colour, (tx+2, ty+2, self.tileSize-2, self.tileSize+2))


    def drawStar(self, colour, centre, radius, points=5, width=0):
       
        cx, cy = centre# Get center coordinates of the star
        starPoints = [] # Empty list to store star points
   
        angleInBetween = math.pi / points  # Calculate angle between each point | Half circle angle / number of points
   
        for i in range(2 * points): # Loop through to calculate outer and inner points
            if i % 2 == 0:
                r = radius  # external point
            else:
                r = radius / 2  # internal point


            theeta = i * angleInBetween - math.pi / 2  # rotate pi/2 rad ACW to start from the top
            x = cx + r * math.cos(theeta)
            y = cy + r * math.sin(theeta)
            starPoints.append((x, y))


        pygame.draw.polygon(self.screen, colour, starPoints, width)  # Draw the polygon using the calculated points




    def drawStarinMaze(self, targetCoord): #this draws the star inside the maze specifically
        x, y = targetCoord
        tileCentre = (x*self.tileSize + self.tileSize//2, y*self.tileSize + self.tileSize//2)
        self.drawStar(pygame.Color('mintcream'), tileCentre, self.tileSize//3)




    def drawStarinWin(self, index):
        spacing = 100  # pixels between stars
        base_x = WIDTH // 2 - spacing  # Start a bit left of centre
        y = HEIGHT// 2
        # Compute the x-position for each star based on its index (0, 1, 2)
        x = base_x + index * spacing
        self.drawStar(pygame.Color('lemonchiffon1'), (x, y), 30, 5) #30 is radius




class ManageGameStates: #handles game state outside of main game class for better clarity and logic handling
    def __init__(self):
        self._gameState = 'START'#just a str for simplicity and adding in any states if needed in an update
   
    def setCurrentGameState(self, state): #written for clarity's sake
        self._gameState = state #still str


    def getCurrentGameState(self): #written for clairty's sake
        return self._gameState


class Game:
    def __init__(self, rows, cols, tileSize):
        pygame.init()
        self.running = True
        self.tileSize = tileSize #40 | literally tile Size
        self.rows, self.cols = rows, cols #in this case should be 15*20
        self.screen = pygame.display.set_mode((cols * tileSize, rows * tileSize))
        self.clock = pygame.time.Clock()
        self.initialiseObjects(self.rows, self.cols, self.tileSize)      
       
        #flags
        self.win = False
        self.gameOver = False


        #counters
        self._movesCounter = 0 #counting amount of moves user used


        #stars lists
        self.__starsLocation = None #will become a list of tuples | generated later on
        self.__starsCollected = [] #left as a list so that reset can just give these checkpoints back




    #initialising objects
    def initialiseObjects(self, rows, cols, tileSize):
        pygame.init()
        self.maze = Maze(rows, cols)
        self.ui = UI(self.screen, tileSize)
        self.autoSolver = AutoSolver(self.maze)
        self.stateManager = ManageGameStates()
        self.obstacle = Obstacle(*self.maze.destination, self.maze, "EASY")


    def initialiseMaze(self):
        self.maze.generateMaze(*self.maze.start) #start generating maze from start
        self.maze.removeExtraWalls() #tear down random walls to make more available paths
        self.maze.updateGraph() #update graph just in case
        self.setStarsLocation() #then decide all stars location just once


    def initialiseObstacle(self, difficulty): #initialising the right obstacles
        if difficulty == "EASY":
            self.obstacle = EasyObstacle(*self.maze.destination, self.maze, difficulty)
        elif difficulty == "NORMAL":
            self.obstacle = NormalObstacle(*self.maze.destination, self.maze, difficulty)
        elif difficulty == "HARD":
            self.obstacle = HardObstacle(*self.maze.destination, self.maze, difficulty)


       
    def initialisePlayer(self):
        self.player = Player(*self.maze.start, self.maze) #start player at origin


   
    def resetGame(self): #to ensure smooth running | made for better clarity
        self.initialiseMaze()
        self.initialisePlayer()
       


 #handling end screens - - -- - - - - - - - - - - - - -
    def checkWinningCondition(self):
        if not self.gameOver: #make sure game wasn't over to begin with
            if self.player.getPosition() == self.maze.destination: #user has reached destination
                self.win = True #user has won
                self.gameOver = True
                self.stateManager.setCurrentGameState("WIN") #switch state so that the win screen can be drawn




            if self.player.getPosition() == self.obstacle.getPosition(): #user is inside same cell as obstacle
                self.win = False #user lost hence did not win
                self.gameOver = True  
                self.stateManager.setCurrentGameState("LOSE") #switch state so that lose screen can be drawn
       
    def getWinLoseText(self): #directly return the message to be printed
        if self.win:
            return "YOU WIN"
        else:
            return "YOU LOSE"
   
    def drawWinScreen(self):
        self.ui.drawEndScreenTexts(self.getWinLoseText(),self._movesCounter) #prints winning texts
        self.drawStarsOntoWinScreen() #draw the stars accordingly




    def drawLoseScreen(self): #separated from drawWinScreen to prevent confusion
        self.ui.drawEndScreenTexts(self.getWinLoseText(), self._movesCounter) #prints losing texts only no stars


    #star related business - - - - - - - - - - -


    def drawStarsOntoMazeGame(self): #draws stars 3 times or none at all
        for target in self.__starsLocation:
            self.ui.drawStarinMaze(target)
   
    def setStarsLocation(self):
        self.__starsLocation = list(self.maze.generateStarsLocation(self.maze, 3)) #randomly generates 3 locations to store stars


    def getStarsLocation(self): #current stars location in current maze
        return self.__starsLocation
   
    def getStarsCollected(self): #stores the location of stars the user collected
        return self.__starsCollected


    def updateStarsCollected(self): #
        pos = self.player.getPosition()
        if pos in self.__starsLocation:
            self.__starsLocation.remove(pos)
            self.__starsCollected.append(pos)
   
    def drawStarsOntoWinScreen(self): #this draws the star 3 times max or none at all
        for i in range (len(self.__starsCollected)):
            self.ui.drawStarinWin(i) #no need location since im only counting


    #obstacle related updates  - - - -- - - - - -


    def updateObstacleDifficultyFromMenu(self, difficulty): #separated so this would be done once only
        if self.stateManager.getCurrentGameState() == "MENU":
            self.initialiseObstacle(difficulty) #obstacle first initiated here
            self.stateManager.setCurrentGameState("PLAYING")
            self.setStarsLocation() #and star location decided here


    def updateObstacleCurrentMovement(self): #put in own method for clarity
        self.obstacle.updateMovement(self.player, self._movesCounter, self.maze.destination) #use the corresponding difficulty to decide movement


   
    #handling player movement - - - - - - -
    def getPlayerMovement(self, event):
        if event.type == pygame.KEYDOWN: #only react when key is pressed once | aka should only update once to long pressing a key
            if event.key == pygame.K_w:
                self.move = "UP" #user moves up if walkable
            elif event.key == pygame.K_s:
                self.move = "DOWN" #user moves down if walkable
            elif event.key == pygame.K_a:
                self.move = "LEFT"
            elif event.key == pygame.K_d:
                self.move = "RIGHT"


            elif event.key == pygame.K_m:
                if self.stateManager.getCurrentGameState() == "START": #only allow m to react if used in start screen
                    self.stateManager.setCurrentGameState("MENU")
                   
            elif event.key == pygame.K_n:
                self.updateObstacleDifficultyFromMenu("NORMAL")
                self.resetGame() #initialises maze and player


            elif event.key == pygame.K_e:
                self.updateObstacleDifficultyFromMenu("EASY")
                self.resetGame() #initialises maze and player


            elif event.key == pygame.K_h:
                self.updateObstacleDifficultyFromMenu("HARD")
                self.resetGame() #initialises maze and player


        else:
             self.move  = None #move set to None when keys are not clicked
       


    def updatePlayerMovementInMaze(self):
        moved = False #flagged to ensure moveCounter etc does not update per flip and instead reacts to user movement only
        if self.move == "UP":
            self.player.updatePlayerPosition(0, -1) #logically update user's position ensuring direction is moveable
            moved = True
        elif self.move == "DOWN":
            self.player.updatePlayerPosition(0, 1)
            moved = True
        elif self.move == "LEFT":
            self.player.updatePlayerPosition(-1, 0)
            moved = True
        elif self.move == "RIGHT":
            self.player.updatePlayerPosition(1, 0)
            moved = True


        if moved:
            self.move = None #reset move so it won't continuously update
            self._movesCounter += 1 #counter starts from 0 so is incremented before
            self.updateObstacleCurrentMovement() #only moves when user has moved
            if self.obstacle.getDifficulty() == "NORMAL": #additional drawing needed for normal difficulty
                target = self.obstacle.getTarget()
                if target: #check if there is a pending target
                    self._highlightedTarget = target #draw the cell it's about to jump to
                else:
                    if hasattr(self, '_highlightedTarget'): #makes sure that it's only handled for normalObstacle
                        del self._highlightedTarget #if not then delete it
            self.maze.updateGraph() #just in case (especially for hard obstacle)


    #main game loop - - -- - - - - -  
    def run(self):
        self.stateManager.setCurrentGameState("START") #should load start screen as program starts running
        while self.running:
            self.screen.fill('darkslategray') #background colour
            for event in pygame.event.get():
                if event.type == pygame.QUIT: #as long as window still open keep updating
                    self.running = False
                self.getPlayerMovement(event) #should get player key presses
                if self.stateManager.getCurrentGameState() == "PLAYING": #
                    self.updatePlayerMovementInMaze() #user moves and move counter gets updated -> obstacle moves


            if self.stateManager.getCurrentGameState() == "START":
                self.ui.drawStartScreen() #message


            if self.stateManager.getCurrentGameState() == "MENU":
                self.ui.drawMenu() #difficulty menu setting




            if self.stateManager.getCurrentGameState() == "PLAYING":
                self.ui.drawMaze(self.maze) #keep drawing maze
                self.ui.drawDestination() #destination should be visible on screen
                self.updateStarsCollected()
                self.drawStarsOntoMazeGame() #make sure star drawing is updated accordingly
                if hasattr(self, '_highlightedTarget'): #ensures this is only handled for normal diff
                    self.ui.highlightCell(self._highlightedTarget, pygame.Color("lightcyan1")) #the cell to be teleported to
                self.ui.drawObject(self.player, pygame.Color('darkorange'))  #draw player as pink box
                self.ui.drawObject(self.obstacle, pygame.Color('olivedrab1')) #draw obstacle as green box
                self.checkWinningCondition() #keep checking for game over


            if self.stateManager.getCurrentGameState() == "WIN":
                self.drawWinScreen() #load msgs, stars collected and moves used


            if self.stateManager.getCurrentGameState() == "LOSE":
                self.drawLoseScreen() #load msgs, stars collected and moves used


            pygame.display.flip()
            self.clock.tick(60)
        pygame.quit()




if __name__ == "__main__":
    RES = WIDTH, HEIGHT = 800, 600
    TILE_SIZE = 40
    ROWS, COLS = HEIGHT//TILE_SIZE, WIDTH//TILE_SIZE #15, 20
    pygame.init()
    pygame.display.set_mode((WIDTH, HEIGHT))
    pygame.display.set_caption("Maze Game")
    game = Game(ROWS, COLS, TILE_SIZE) #initialise game
    game.run()
