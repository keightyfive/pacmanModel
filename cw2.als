/*********************************************************************************
Heriot-Watt University 
Coursework 2 - Rigerous Methods of Software Engineering
Dynamic model of the Pacman videogame 
Author: Kevin Klein
Name: cw2.als
*********************************************************************************/

open util/ordering[Item]
open util/ordering[Position]
open util/integer

// This alloy modul represents a classic game from the 1980s, Pacman
module Pacman

/**********************************************************************************
Signatures - 5 alltogether, plus one subset which inherits from a parent set
**********************************************************************************/

// abstract Signature for status of the game
	abstract sig GameStatus
	{

	}

// sub signature of status for playing, winning, or losing the game
	one sig Play, Won, Lost extends GameStatus
	{

	}

// Signature for game items -- pacman, ghosts, walls, dots and status of the game
	sig Item
	{
		pacman: one Position,  	// total Relation -- pacman, only one per instance
		ghosts: some Position,	// total Relation -- the ghosts, more than one
		walls: set Position,			// partial Relation -- walls
 		dots: set Position,			// partial Relation -- dots
 		status: GameStatus		// Relation -- status (win, play, lose)
	}

// Signature for positions of the maze: neighbours, coordinates, rows, columns
	sig Position
	{
    	neighbour: set Position,
    	coordinates: Int -> Int,
    	row: Int,
    	column: Int
	}
	{
    	int[column] >= 0
    	int[column] < int[Width.i]
    	int[row] >= 0
    	int[row] < int[Height.i]
    	coordinates = column -> row
	}

// Signature -- for the width of the maze
	one sig Width
	{
    	i: Int
	}
	{
    	int[i] = 5 // after testing, not more than 7 recommended
	}

// Signature -- for height of the maze
	one sig Height
	{
    	i: Int
	}
	{
    	int[i] = 5 // after testing, not more than 7 recommended 
	}

/**********************************************************************************
Facts - 4 facts alltogether
these describe the rules of the game, things which are not allowed
**********************************************************************************/

// Fact 1 - initialises game
	fact initialState
	{
  		InitGame[first]
	}

// Fact 2 - no position can exist twice
	fact NoDoublePositions
	{
    	all p1, p2: Position |
    	(p1 != p2) => (p1.column != p2.column) || (p1.row != p2.row)
	}
       
// Fact 3 - each position has a neighbour position to which pacman or the ghosts can move to
	fact NeighbourPositions
	{
    	all p, a: Position
		{
       	(a in p.neighbour) iff
			{
				int[a.row] = int[p.row] and
				{
           		int[a.column] = int[p.column].add[1] or
           		int[a.column] = int[p.column].sub[1]
         		}
            	or
            	int[a.column] = int[p.column] and
			 	{
               	int[a.row] = int[p.row].add[1]
				  	or
                	int[a.row] = int[p.row].sub[1]
            	}
        	}
    	}       
	}

// Fact 4 - defining the order of each position
	fact PositionOrder
	{
    	all p: Position, p': p.next
		{
        	let a = int[p.row].mul[int[Width.i]], a' = int[p'.row].mul[int[Width.i]]
		 	{
           	(a + int[p.column]) < (a' + int[p'.column])
        	}
		}
	}

/*****************************************************************************
Assertions - 3 alltogether
*****************************************************************************/

// Assertion 1 - Game is won if all the dots are gone
	assert GameWonIfAllDotsGone
	{
    	all s : Item |
       	s.status= Won iff s.dots = none
	}

// Assertion 2 - Game is lost if Ghost gets Pacman
	assert GameLostIfGhostGetsPacman
	{
    	all s : Item |
       	s.status = Lost iff s.ghosts = s.pacman
	}

// Assertion 3 - behaviour which is valid according to predicates
	assert ValidBehaviour
	{
    	all s: Item, s': s.next
		{
        	DotsCannotIncrease[s,s'] and							// for pred 1
        	DotsEatenByPacman[s,s'] and							// for pred 2
        	MovementOnlyToNeighbourPosition[s,s'] and	// for pred 4
        	WallsCannotMove[s,s'] and								// for pred 3
        	MovementOnlyWhilePlaying[s,s']						// for pred 5
    	}
	}

/*****************************************************************************************************************
Predicates - 9 alltogehter
these describe the dynamic state transitions of the model from the current state (s) to the next state (s')
******************************************************************************************************************/

// Predicate 1 - the dots never increase
	pred DotsCannotIncrease[s, s' : Item]
	{
    	s'.dots in s.dots
	}

// Predicate 2 - dots are eaten only by pacman
	pred DotsEatenByPacman[s, s': Item]
	{
    	s'.dots = s.dots - s.pacman
	}

// Predicate 3 - walls cannot move
	pred WallsCannotMove[s, s' : Item]
	{
    	s.walls = s'.walls
	}

// Predicate 4 - pacman and ghosts can only move to their respective neighbour positions
	pred MovementOnlyToNeighbourPosition[s, s':Item]
	{
    	let p = (s'.pacman), q = (s.pacman) | (p -> q in neighbour) and not(q in s.walls || p in s'.walls)
    	let p = (s'.ghosts), q = (s.ghosts) | (p -> q in neighbour) and not(q in s.walls || p in s'.walls)
	}

// Predicate 5 - pacman and ghosts can only move while gameplay is on
	pred MovementOnlyWhilePlaying[s,s':Item]
	{
    	s.status != Play implies s = s'
	}

// Predicate 6 - initialises game
	pred InitGame[s : Item]
	{
    	s.walls.coordinates = Int[3] -> Int[0] + Int[3] -> Int[1] + Int[3] -> Int[2] and
    	s.dots.coordinates = Int[0] -> Int[0] + Int[1] -> Int[0] + Int[2] -> Int[0] + Int[0] -> Int[1] + Int[1] -> Int[1] + Int[2] -> Int[1] + Int[0] -> Int[2] + Int[1] -> Int[2] +Int[2] -> Int[2] and
    	s.status = Play
	}

// Predicate 7 - game is won
	pred GameIsWon
	{
    	last.status = Won
	}

// Predicate 8 - game is lost
	pred GameIsLost
	{
    	last.status = Lost
	}

// Predicate 9 - game is played
	pred GameIsPlayed()
	{
    	last.status = Play
	}

/*****************************************************************************************
The run command generates various instances of the dynamic model 
for 3 game states: game is beeing played, game is won, game is lost
*****************************************************************************************/

run GameIsPlayed for 3 Item, exactly 25 Position, 5 int
//run GameIsLost for 3 Item, exactly 25 Position, 5 int
//run GameIsWon for 10 Item, exactly 25 Position, 5 int
