/* Spaceships_and_asteroids
 * Author: Rusiru
 * Creation date: 11/16/2021
 */
MACHINE
    Spaceships_and_asteroids

SETS
    // holds the possible alerts the system can output
    ALERTS = { 
        MOVED_UP, 
        MOVED_DOWN, 
        MOVED_FORWARD, 
        MOVED_BACKWARD, 
        WARPDRIVED,
        ASTEROID_COLLISION, 
        OUT_OF_BOUNDS, 
        INSUFFICIENT_POWER,
        DOCKED,
        NOT_DOCKED,
        GAME_WON, 
        GAME_NOT_OVER, 
        GAME_LOST 
    }

CONSTANTS
    normal_move,      // holds the consumption of power for a normal move (i.e. MoveUp, MoveDown, MoveForward, MoveBackward)
    warpdrive,        // holds the consumption of power for a warp-drive
    asteroid_hit,     // holds the amount of power loss when hit to an asteroid
    GRID_X,           // holds the x axis values
    GRID_Y,           // holds the y axis values
    ASTEROIDS,        // holds the asteroid locations
    starbase,         // holds the star-base location
    homebase          // holds the homebase location
    
PROPERTIES
    normal_move : NAT & normal_move = 5 &
    warpdrive : NAT & warpdrive = 20 &
    asteroid_hit : NAT & asteroid_hit = 10 &
    GRID_X <: NAT1 & GRID_X = 1..12 &
    GRID_Y <: NAT1 & GRID_Y = 1..7 &
    ASTEROIDS : GRID_X <-> GRID_Y & ASTEROIDS = {(3 |-> 2), (3 |-> 5), (5 |-> 4), (6 |-> 7), (7 |-> 1), (7 |-> 5), (7 |-> 7), (8 |-> 3), (10 |-> 6), (11 |-> 2), (12 |-> 5)} &
    starbase = (6 |-> 4) &
    homebase = (1 |-> 1)
    
VARIABLES
    spaceship_x,         // this holds the current x position of the spaceship
    spaceship_y,         // this holds the current y position of the spaceship
    spaceship_route,     // this holds the route the spaceship has taken from the homebase to the current position
    power,               // this holds the power of the spaceship in a single game
    collisions           // this holds the number of collisions the spaceship has had in a single game

INVARIANT
    spaceship_x : GRID_X &                   // because value of x should be a value between 1..12 inclusive
    spaceship_y : GRID_Y &                   // because value of x should be a value between 1..7 inclusive
    power : INTEGER &                        // because power can be less than 0
    collisions : NAT &                       // because collisions can be 0
    spaceship_route : seq(GRID_X * GRID_Y)   // spaceship route is a sequence that contains maplets of x and y

INITIALISATION
    spaceship_x, spaceship_y, power, collisions, spaceship_route := 1, 1, 0, 0, [(homebase)]
    
OPERATIONS
    
    // Start/Re-Start game
    NewGame(new_power) = 
    PRE
        // check whether the new_power is a member of natural number set starting from one, and new_power value is equal to or greater than 40 (i.e. the least possible power needed to reach the star-base through normal moves)
        new_power : NAT1 & new_power >= 40
    THEN
        // reset all values to default with the new power
        spaceship_x, spaceship_y, power, collisions, spaceship_route := 1, 1, new_power, 0, [(homebase)]
    END;    
    
    // Move up Operation
    message <-- MoveUp = 
    BEGIN
        IF
            // checks whether the spaceship is already in the star-base
            spaceship_x |-> spaceship_y = starbase
        THEN
            // show alert if the spaceship is in the star-base
            message := GAME_WON
        ELSE
            IF
                // check whether there is power to do a normal move
                power >= normal_move    
            THEN
                IF
                    // check whether the new position in within the boundary
                    succ(spaceship_y) : GRID_Y 
                THEN
                    IF
                        // check if the moving position doesn't a asteroid
                        spaceship_x |-> succ(spaceship_y) /: ASTEROIDS
                    THEN
                        // if not collided with asteroid, update position, add current position to route, update power and return status alert 
                        spaceship_route, spaceship_y, power, message := (spaceship_route <- (spaceship_x, succ(spaceship_y))), succ(spaceship_y), (power - normal_move), MOVED_UP
                    ELSE                 
                        // if collided with asteroid, increment number of collision, reduce power, and return status alert
                        collisions, power, message := (collisions + 1), (power - asteroid_hit), ASTEROID_COLLISION 
                    END
               ELSE
                   // show alert if out of bounds
                   message := OUT_OF_BOUNDS
               END
            ELSE
                // show alert if not enough power
                message := INSUFFICIENT_POWER            
            END
        END        
    END;
       
    // Move Down Operation
    message <-- MoveDown =
    BEGIN
        IF
            // checks whether the spaceship is already in the star-base
            spaceship_x |-> spaceship_y = starbase
        THEN
            // show alert if the spaceship is in the star-base
            message := GAME_WON
        ELSE
            IF
                // check whether there is power to do a normal move
                power >= normal_move
            THEN
                IF
                    // check whether the new position in within the boundary
                    pred(spaceship_y) : GRID_Y
                THEN
                    IF
                        // check if the moving position doesn't a asteroid
                        spaceship_x |-> pred(spaceship_y) /: ASTEROIDS
                    THEN
                        // if not collided with asteroid, update position, add current position to route, update power and return status alert
                        spaceship_route, spaceship_y, power, message := (spaceship_route <- (spaceship_x, pred(spaceship_y))), pred(spaceship_y), (power - normal_move), MOVED_DOWN  
                    ELSE                    
                        // if collided with asteroid, increment number of collision, reduce power, and return status alert
                        collisions, power, message := (collisions + 1), (power - asteroid_hit), ASTEROID_COLLISION       
                    END
                ELSE
                    // show alert if out of bounds
                    message := OUT_OF_BOUNDS
                END
            ELSE
                // show alert if not enough power
                message := INSUFFICIENT_POWER
            END     
        END
    END;
    
    // Move spaceship Forward
    message <-- MoveForward =
    BEGIN
        IF
            // checks whether the spaceship is already in the star-base
            spaceship_x |-> spaceship_y = starbase
        THEN
            // show alert if the spaceship is in the star-base
            message := GAME_WON
        ELSE
            IF
                // check whether there is power to do a normal move
                power >= normal_move 
            THEN
                IF
                    // check whether the new position in within the boundary
                    succ(spaceship_x) : GRID_X
                THEN
                    IF
                        // check if the moving position doesn't a asteroid
                        succ(spaceship_x) |-> spaceship_y /: ASTEROIDS                    
                    THEN      
                        // if not collided with asteroid, update position, add current position to route, update power and return status alert
                        spaceship_route, spaceship_x, power, message := (spaceship_route <- (succ(spaceship_x), spaceship_y)), succ(spaceship_x), (power - normal_move), MOVED_FORWARD                                                  
                    ELSE 
                        // if collided with asteroid, increment number of collision, reduce power, and return status alert
                        collisions, power, message := (collisions + 1), (power - asteroid_hit), ASTEROID_COLLISION
                    END
                ELSE
                    // show alert if out of bounds
                    message := OUT_OF_BOUNDS
                END
            ELSE
                // show alert if not enough power
                message := INSUFFICIENT_POWER
            END  
        END
    END;
    
    // Move spaceship Backward
    message <-- MoveBackward =
    BEGIN
        IF
            // checks whether the spaceship is already in the star-base
            spaceship_x |-> spaceship_y = starbase
        THEN
            // show alert if the spaceship is in the star-base
            message := GAME_WON
        ELSE
            IF
                // check whether there is power to do a normal move
                power >= normal_move 
            THEN
                IF
                    // check whether the new position in within the boundary
                    pred(spaceship_x) : GRID_X
                THEN
                    IF
                        // check if the moving position doesn't a asteroid
                        pred(spaceship_x) |-> spaceship_y /: ASTEROIDS                    
                    THEN      
                        // if not collided with asteroid, update position, add current position to route, update power and return status alert
                        spaceship_route, spaceship_x, power, message := (spaceship_route <- (pred(spaceship_x), spaceship_y)), pred(spaceship_x), (power - normal_move), MOVED_BACKWARD
                    ELSE 
                        // if collided with asteroid, increment number of collision, reduce power, and return status alert
                        collisions, power, message := (collisions + 1), (power - asteroid_hit), ASTEROID_COLLISION
                    END
                ELSE
                    // show alert if out of bounds
                    message := OUT_OF_BOUNDS
                END
            ELSE
                // show alert if not enough power
                message := INSUFFICIENT_POWER
            END
        END            
    END;
    
    // Engage in a warp-drive 
    message <-- EngageWarpDrive (x_position, y_position) =
    PRE
        // check whether the parameters are natural numbers starting from 1 and is not the coordinates of the same position of the spaceship
        x_position : NAT1 &
        y_position : NAT1 & 
        (x_position |-> y_position) /= (spaceship_x |-> spaceship_y)     
    THEN
        IF
            // checks whether the spaceship is already in the star-base
            spaceship_x |-> spaceship_y = starbase
        THEN
            // show alert if the spaceship is in the star-base
            message := GAME_WON
        ELSE
            IF
                // check if enough power is there to warp drive
                power >= warpdrive
            THEN            
                IF
                    // check whether the new position in within the boundary
                    x_position : GRID_X & y_position : GRID_Y
                THEN
                    IF
                        // check if the moving position doesn't a asteroid
                        x_position |-> y_position /: ASTEROIDS
                    THEN
                        // if not collided with asteroid, update position, add current position to route, update power and return status alert
                        spaceship_route, spaceship_x, spaceship_y, power, message := spaceship_route <- (x_position, y_position), x_position, y_position, power - warpdrive, WARPDRIVED                   
                    ELSE
                        // if collided with asteroid, increment number of collision, reduce power, and return status alert 
                        collisions, power, message := collisions + 1, power - asteroid_hit, ASTEROID_COLLISION
                    END
                ELSE
                    // show alert if out of bounds
                    message := OUT_OF_BOUNDS
                END                            
            ELSE 
                // show alert if not enough power
                message := INSUFFICIENT_POWER
            END 
        END
    END;
    
    
    // Display Mission Status
    current_location, power_left, number_of_collision <-- MissionStatus =
    BEGIN
        // output current location, the power left and the number of collisions
        current_location, power_left, number_of_collision := spaceship_x |-> spaceship_y, power, collisions
    END;
    
    // Display Mission Route of the Spaceship
    path <-- RegionsVisited =
    BEGIN
        // output the path spaceship has visited
        path := spaceship_route
    END;
    
    // Current Location of the spaceship
    message <-- DockedAtStarBase  =
    BEGIN
        IF 
            // check if star-base location is the same as spaceship's current location
            starbase = (spaceship_x |-> spaceship_y)
        THEN
            // docked if both locations are same
            message := DOCKED
        ELSE
            // not docked if locations are different
            message := NOT_DOCKED
        END
    END;
    
    // Display Status of the Game
    status <-- GameStatus  =
    BEGIN
        IF
            // check if star-base location is the same as spaceship's current location
            starbase = (spaceship_x |-> spaceship_y) 
        THEN 
            // game won if locations are same
            status := GAME_WON
        ELSE
            IF 
                // check if there is power to do the least possible operation (i.e. a normal move)
                power >= normal_move
            THEN
                // if there is enough power, the game is still ongoing
                status := GAME_NOT_OVER
            ELSE
                // if there is no power enough to do a move, the game is lost
                status := GAME_LOST
            END
        END
    END
END
