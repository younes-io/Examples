------------------------------- MODULE TLCMC -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Convertes the given Sequence seq into a Set of all the                  *) 
(* Sequence's elements. In other words, the image of the function          *)
(* that seq is.                                                            *)
(***************************************************************************)
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)} 

(***************************************************************************)
(* Returns a Set of those permutations created out of the elements of Set  *)
(* set which satisfy Filter.                                               *)
(***************************************************************************)
SetToSeqs(set, Filter(_)) == UNION {{perm \in [1..Cardinality(set) -> set]: 
                            \* A filter applied on each permutation
                            \* generated by [S -> T]       
                            Filter(perm)}}

(***************************************************************************)
(* Returns a Set of all possible permutations with distinct elemenents     *)
(* created out of the elements of Set set. All elements of set occur in    *)
(* in the sequence.                                                        *)
(***************************************************************************)
SetToDistSeqs(set) == SetToSeqs(set, 
                    LAMBDA p: Cardinality(SeqToSet(p)) = Cardinality(set))

(***************************************************************************)
(* A (state) graph G is a directed cyclic graph.                           *)
(*                                                                         *)
(* A graph G is represented by a record with 'states' and 'actions'        *)
(* components, where G.states is the set of states and G.actions[s] is the *)
(* set of transitions of s -- that is, all states t such that there is an  *)
(* action (arc) from s to t.                                               *)
(***************************************************************************)
IsGraph(G) == /\ {"states", "initials", "actions"} = DOMAIN G
              /\ G.actions \in [G.states -> SUBSET G.states]
              /\ G.initials \subseteq G.states

(***************************************************************************)
(* A set of all permutations of the inital states of G.                    *)
(***************************************************************************)
SetOfAllPermutationsOfInitials(G) == SetToDistSeqs(G.initials)

(***************************************************************************)
(* A Set of successor states state.                                        *)
(***************************************************************************)
SuccessorsOf(state, SG) == {successor \in SG.actions[state]:
                            successor \notin {state}}

(***************************************************************************)
(* The predecessor of v in a forest t is the first element of the pair     *)
(* <<predecessor, successor>> nested in a sequence of pairs. In an actual  *)
(* implementation such as TLC, pair[1] is rather an index into t than      *)
(* an id of an actual state.                                               *)
(***************************************************************************)
Predecessor(t, v) == SelectSeq(t, LAMBDA pair: pair[2] = v)[1][1]

CONSTANT StateGraph, ViolationStates, null

ASSUME \* The given StateGraph is actually a graph
       \/ IsGraph(StateGraph)
       \* The violating states are vertices in the state graph.
       \/ ViolationStates \subseteq StateGraph.states

(***************************************************************************
The PlusCal code of the model checker algorithm
--fair algorithm ModelChecker {
    variables
              \* A FIFO containing all unexplored states. A simple
              \* set provides no order, but TLC should explore the
              \* StateGraph in either BFS (or DFS => LIFO).
              \* Note that S is initialized with each
              \* possible permutation of the initial states
              \* here because there is no defined order
              \* of initial states.
              S \in SetOfAllPermutationsOfInitials(StateGraph),
              \* A set of already explored states.      
              C = {},
              \* The state currently being explored in scsr
              state = null,
              \* The set of state's successor states              
              successors = {},
              \* Counter
              i = 1,
              \* A path from some initial state ending in a
              \* state in violation.
              counterexample = <<>>,
              \* A sequence of pairs such that a pair is a
              \* sequence <<predecessor, successors>>.
              T = <<>>;
    {
       (* Check initial states for violations. We could
          be clever and check the inital states as part
          of the second while loop. However, we then
          either check all states twice or add unchecked
          states to S. *)
       init: while (i \leq Len(S)) {
             \*  Bug in thesis: 
             \*state := Head(S);
             state := S[i]; 
             \* state is now fully explored,
             \* thus exclude it from any
             \* futher exploration if graph
             \* exploration visits it again
             \* due to a cycle. 
             C := C \cup {state};
             i := i + 1;
             if (state \in ViolationStates) {
                     counterexample := <<state>>;
                     \* Terminate model checking
                     goto trc;
             };
       };
       \* Assert that all initial states have been explored.
       initPost: assert C = SeqToSet(S);

       (* Explores all successor states 
          until no new successors are found
          or a violation has been detected. *)
       scsr: while (Len(S) # 0) {
            \* Assign the first element of
            \* S to state. state is
            \* what is currently being checked.
            state := Head(S);
            \* Remove state from S.
            S := Tail(S);
            
            \* For each unexplored successor 'succ' do:
            successors := SuccessorsOf(state, StateGraph) \ C;
            if (SuccessorsOf(state, StateGraph) = {}) {
                \* Iff there exists no successor besides
                \* the self-loop, the system has reached
                \* a deadlock state.
                counterexample := <<state>>;
                goto trc;
            };
            each: while (successors # {}) {
                with (succ \in successors) {
                     \* Exclude succ in this while loop.
                     successors := successors \ {succ};

                     \* Mark successor globally visited.
                     C := C \cup {succ}; S := S \o <<succ>>;
                     
                     \* Append succ to T and add it
                     \* to the list of unexplored states.
                     T  := T \o << <<state,succ>> >>;
                     
                     \* Check state for violation of a
                     \* safety property (simplified 
                     \* to a check of set membership.
                     if (succ \in ViolationStates) {
                       counterexample := <<succ>>;
                       \* Terminate model checking
                       goto trc;
                     };
                };
            };
       };
       (* Model Checking terminated without finding
          a violation. *)
       \* No states left unexplored and no ViolationState given.
       assert S = <<>> /\ ViolationStates = {};
       goto Done;
       
       (* Create a counterexample, that is a path
          from some initial state to a state in
          ViolationStates. In the Java implementation
          of TLC, the path is a path of fingerprints. 
          Thus, a second, guided state exploration
          resolves fingerprints to actual states. *)
       trc : while (TRUE) {
                if (Head(counterexample) \notin StateGraph.initials) {
                   counterexample := <<Predecessor(T, Head(counterexample))>> \o counterexample;
                } else {
                   assert counterexample # <<>>;
                   goto Done;
                };
       };
    }        
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES S, C, state, successors, i, counterexample, T, pc

vars == << S, C, state, successors, i, counterexample, T, pc >>

Init == (* Global variables *)
        /\ S \in SetOfAllPermutationsOfInitials(StateGraph)
        /\ C = {}
        /\ state = null
        /\ successors = {}
        /\ i = 1
        /\ counterexample = <<>>
        /\ T = <<>>
        /\ pc = "init"

init == /\ pc = "init"
        /\ IF i \leq Len(S)
              THEN /\ state' = S[i]
                   /\ C' = (C \cup {state'})
                   /\ i' = i + 1
                   /\ IF state' \in ViolationStates
                         THEN /\ counterexample' = <<state'>>
                              /\ pc' = "trc"
                         ELSE /\ pc' = "init"
                              /\ UNCHANGED counterexample
              ELSE /\ pc' = "initPost"
                   /\ UNCHANGED << C, state, i, counterexample >>
        /\ UNCHANGED << S, successors, T >>

initPost == /\ pc = "initPost"
            /\ Assert(C = SeqToSet(S), 
                      "Failure of assertion at line 116, column 18.")
            /\ pc' = "scsr"
            /\ UNCHANGED << S, C, state, successors, i, counterexample, T >>

scsr == /\ pc = "scsr"
        /\ IF Len(S) # 0
              THEN /\ state' = Head(S)
                   /\ S' = Tail(S)
                   /\ successors' = SuccessorsOf(state', StateGraph) \ C
                   /\ IF SuccessorsOf(state', StateGraph) = {}
                         THEN /\ counterexample' = <<state'>>
                              /\ pc' = "trc"
                         ELSE /\ pc' = "each"
                              /\ UNCHANGED counterexample
              ELSE /\ Assert(S = <<>> /\ ViolationStates = {}, 
                             "Failure of assertion at line 164, column 8.")
                   /\ pc' = "Done"
                   /\ UNCHANGED << S, state, successors, counterexample >>
        /\ UNCHANGED << C, i, T >>

each == /\ pc = "each"
        /\ IF successors # {}
              THEN /\ \E succ \in successors:
                        /\ successors' = successors \ {succ}
                        /\ C' = (C \cup {succ})
                        /\ S' = S \o <<succ>>
                        /\ T' = T \o << <<state,succ>> >>
                        /\ IF succ \in ViolationStates
                              THEN /\ counterexample' = <<succ>>
                                   /\ pc' = "trc"
                              ELSE /\ pc' = "each"
                                   /\ UNCHANGED counterexample
              ELSE /\ pc' = "scsr"
                   /\ UNCHANGED << S, C, successors, counterexample, T >>
        /\ UNCHANGED << state, i >>

trc == /\ pc = "trc"
       /\ IF Head(counterexample) \notin StateGraph.initials
             THEN /\ counterexample' = <<Predecessor(T, Head(counterexample))>> \o counterexample
                  /\ pc' = "trc"
             ELSE /\ Assert(counterexample # <<>>, 
                            "Failure of assertion at line 177, column 20.")
                  /\ pc' = "Done"
                  /\ UNCHANGED counterexample
       /\ UNCHANGED << S, C, state, successors, i, T >>

Next == init \/ initPost \/ scsr \/ each \/ trc
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

Live == ViolationStates # {} => <>[](/\ Len(counterexample) > 0
                                     /\ counterexample[Len(counterexample)] \in ViolationStates
                                     /\ counterexample[1] \in StateGraph.initials)

=============================================================================
