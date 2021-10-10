-------------------------- MODULE SingleLaneBridge --------------------------

\* A bridge over a river is only wide enough to permit a single lane of traffic.
\* Consequently, cars can only move concurrently if they are moving in the same 
\* direction. A safety violation occurs if two cars moving in different directions
\* enter the bridge at the same time.
\* To visualize the problem, refer to https://flylib.com/books/en/2.752.1.48/1/
   
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions 

ASSUME CarsRight \cap CarsLeft = {}
ASSUME Bridge \subseteq Positions
ASSUME Cardinality(CarsRight \union CarsLeft ) # 0

VARIABLES Location, Waiting
vars == <<Location, Waiting>>

Cars == CarsRight \union CarsLeft 

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

StartBridge == CHOOSE min \in Bridge : \A e \in Bridge : min <= e
EndBridge   == CHOOSE max \in Bridge : \A e \in Bridge : max >= e

StartPos == CHOOSE min \in Positions : \A p \in Positions : min <= p
EndPos   == CHOOSE max \in Positions : \A p \in Positions : max >= p

RMove(pos) == IF pos > StartPos THEN pos - 1 ELSE EndPos
LMove(pos) == IF pos < EndPos THEN pos + 1 ELSE StartPos

NextLocation(car) == IF car \in CarsRight THEN RMove(Location[car]) ELSE LMove(Location[car])

ChangeLocation(car) ==
    /\ IF \/ car \in CarsRight /\ NextLocation(car) = EndBridge + 1
          \/ car \in CarsLeft /\ NextLocation(car) = StartBridge - 1
        THEN Waiting' = Append(Waiting, car)
        ELSE UNCHANGED Waiting
    /\ Location' = [ Location EXCEPT ![car] = NextLocation(car) ]

HaveSameDirection(car) ==
    \/ car \in CarsRight /\ \A c \in CarsInBridge : c \in CarsRight
    \/ car \in CarsLeft /\ \A c \in CarsInBridge : c \in CarsLeft

\* Actions
MoveOutsideBridge(car) ==
    /\ NextLocation(car) \notin Bridge
    /\ ChangeLocation(car)

MoveInsideBridge(car) ==
    /\ car \in CarsInBridge
    /\ \A c \in Cars : Location[c] # NextLocation(car)
    /\ ChangeLocation(car)

EnterBridge ==
    \/  /\ CarsInBridge = {}
        /\ Len(Waiting) # 0
        /\ Location' = [ Location EXCEPT ![Head(Waiting)] = NextLocation(Head(Waiting)) ]
        /\ Waiting' = Tail(Waiting)
    \/  /\ Len(Waiting) # 0
        /\ Head(Waiting) \notin CarsInBridge
        /\ HaveSameDirection(Head(Waiting))
        /\ \A c \in Cars : Location[c] # NextLocation(Head(Waiting))
        /\ Location' = [ Location EXCEPT ![Head(Waiting)] = NextLocation(Head(Waiting)) ]
        /\ Waiting' = Tail(Waiting)


Init == 
    /\ Location = [ c \in Cars |-> IF c \in CarsRight THEN EndPos ELSE StartPos  ]
    /\ Waiting = <<>>

Next == \E car \in Cars : EnterBridge \/ MoveOutsideBridge(car) \/ MoveInsideBridge(car)

Fairness ==
    /\ \A car \in Cars : WF_vars(MoveOutsideBridge(car))
    /\ \A car \in Cars : WF_vars(MoveInsideBridge(car))
    /\ \A car \in Cars : WF_vars(EnterBridge)

Spec == Init /\ [][Next]_vars /\ Fairness

Invariants ==
    \* Two cars or more cannot be in the same location in the Bridge at the same time
    /\ \A a,b \in Cars :
        /\ Location[a] \in Bridge
        /\ Location[a] = Location[b]
        => a = b
    \* The bridge capacity should be respected
    /\ Cardinality(CarsInBridge) < Cardinality(Bridge) + 1
    \* Two cars of different directions can never be in the bridge
    /\ \A <<r,l>> \in CarsRight \X CarsLeft :
        ~ (Location[r] \in Bridge /\ Location[l] \in Bridge) 

TypeOK ==
    /\ Location \in [ Cars -> Positions ]
    /\ Len(Waiting) <= Cardinality(Cars)

CarsInBridgeExitBridge ==
    \* All cars eventually exit the Bridge 
    \A car \in Cars : Location[car] \in Bridge ~> Location[car] \notin Bridge

CarsEnterBridge ==
    \* All cars eventually enter the bridge
    \A car \in Cars : Location[car] \notin Bridge ~> Location[car] \in Bridge

THEOREM Spec => [] Invariants

THEOREM Spec => [] TypeOK

THEOREM Spec => CarsInBridgeExitBridge
THEOREM Spec => CarsEnterBridge


=============================================================================
\* Modification History
\* Last modified Sun Oct 10 22:05:04 CEST 2021 by youne
