---------------------------- MODULE TowerOfHanoi ----------------------------
EXTENDS Integers
VARIABLES tower1, tower2, tower3, tower1Top, tower2Top, tower3Top

TowersOK == /\ tower1 \in 0..3
            /\ tower2 \in 0..3
            /\ tower3 \in 0..3
            /\ tower1Top \in 1..4
            /\ tower2Top \in 1..4
            /\ tower3Top \in 1..4
 
Init == /\ tower1 = 3
        /\ tower2 = 0
        /\ tower3 = 0
        /\ tower1Top = 1
        /\ tower2Top = 4
        /\ tower3Top = 4        

Tower1toTower2 == \/ /\ tower1 > 0
                     /\ tower2 < 3
                     /\ tower1Top < tower2Top
                     /\ tower1' = tower1 - 1
                     /\ tower2' = tower2 + 1
                     /\ tower3' = tower3
                     /\ tower1Top' = tower1Top + 1
                     /\ tower2Top' = tower2Top - 1
                     /\ tower3Top' = tower3Top

Tower1toTower3 == \/ /\ tower1 > 0
                     /\ tower3 < 3
                     /\ tower1Top < tower3Top
                     /\ tower1' = tower1 - 1
                     /\ tower2' = tower2
                     /\ tower3' = tower3 + 1
                     /\ tower1Top' = tower1Top + 1
                     /\ tower2Top' = tower2Top
                     /\ tower3Top' = tower3Top - 1

Tower2toTower1 == \/ /\ tower2 > 0
                     /\ tower1 < 3
                     /\ tower2Top < tower1Top
                     /\ tower1' = tower1 + 1
                     /\ tower2' = tower2 - 1
                     /\ tower3' = tower3              
                     /\ tower1Top' = tower1Top - 1
                     /\ tower2Top' = tower2Top + 1
                     /\ tower3Top' = tower3Top

Tower2toTower3 == \/ /\ tower2 > 0
                     /\ tower3 < 3
                     /\ tower2Top < tower3Top
                     /\ tower1' = tower1
                     /\ tower2' = tower2 - 1
                     /\ tower3' = tower3 + 1   
                     /\ tower1Top' = tower1Top     
                     /\ tower2Top' = tower2Top + 1
                     /\ tower3Top' = tower3Top - 1          
                                                         
Tower3toTower1 == \/ /\ tower3 > 0
                     /\ tower1 < 3
                     /\ tower3Top < tower1Top
                     /\ tower1' = tower1 + 1
                     /\ tower2' = tower2
                     /\ tower3' = tower3 - 1              
                     /\ tower1Top' = tower1Top - 1
                     /\ tower2Top' = tower2Top
                     /\ tower3Top' = tower3Top + 1

Tower3toTower2 == \/ /\ tower3 > 0
                     /\ tower2 < 3
                     /\ tower3Top < tower2Top
                     /\ tower1' = tower1
                     /\ tower2' = tower2 + 1
                     /\ tower3' = tower3 - 1
                     /\ tower1Top' = tower1Top
                     /\ tower2Top' = tower2Top - 1 
                     /\ tower3Top' = tower3Top + 1              
                                          
Next == \/ Tower1toTower2
        \/ Tower1toTower3
        \/ Tower2toTower1
        \/ Tower2toTower3
        \/ Tower3toTower1
        \/ Tower3toTower2

=============================================================================
\* Modification History
\* Last modified Thu Apr 18 21:15:07 PDT 2019 by jasondebolt
\* Created Thu Apr 18 19:50:30 PDT 2019 by jasondebolt
