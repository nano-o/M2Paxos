-------------------------- MODULE CorrectnessTest --------------------------

EXTENDS TLC

C1 == INSTANCE Correctness WITH
    Commands <- {"c1","c2"},
    Objects <- {"o1","o2"},
    AccessedBy <- LAMBDA c : CASE c = "c1" -> {"o1","o2"} [] c = "c2" -> {"o1","o2"} 

State1 == (1 :> ("o1" :> <<"c1","c2">> @@ "o2" :> <<"c1","c2">>) @@ 2 :> ("o1" :> <<"c1","c2">> @@ "o2" :> <<"c1","c2">>))

ASSUME C1!Correctness(State1)

(***************************************************************************)
(* This is the example from the Correctness module.                        *)
(***************************************************************************)
State5 == (1 :> ("o1" :> <<"c1","c2">> @@ "o2" :> <<"c2">>) @@ 2 :> ("o1" :> <<"c1">> @@ "o2" :> <<"c2","c1">>))

ASSUME \neg C1!Correctness(State5)

State2 == (1 :> ("o1" :> <<"c1","c2">> @@ "o2" :> <<"c1">>) @@ 2 :> ("o1" :> <<"c1">> @@ "o2" :> <<"c1","c2">>))

ASSUME C1!Correctness(State2)

State3 == (1 :> ("o1" :> <<"c1","c2">> @@ "o2" :> <<>>) @@ 2 :> ("o1" :> <<"c1">> @@ "o2" :> <<"c1","c2">>))

ASSUME C1!Correctness(State3)

C2 == INSTANCE Correctness WITH
    Commands <- {"c1","c2"},
    Objects <- {"o1","o2"},
    AccessedBy <- LAMBDA c : CASE c = "c1" -> {"o1","o2"} [] c = "c2" -> {"o1"} 
    
State4 == (1 :> ("o1" :> <<"c1","c2">> @@ "o2" :> <<"c1">>) @@ 2 :> ("o1" :> <<"c1","c2">> @@ "o2" :> <<>>))

ASSUME C2!Correctness(State4)

C3 == INSTANCE Correctness WITH
    Commands <- {"c1","c2","c3"},
    Objects <- {"o1","o2","o3"},
    AccessedBy <- LAMBDA c : CASE 
            c = "c1" -> {"o1","o2"} 
        []  c = "c2" -> {"o2","o3"}
        []  c = "c3" -> {"o3","o1"}

State6 == (1 :> ("o1" :> <<"c1","c3">> @@ "o2" :> <<"c1","c2">> @@ "o3" :> <<"c2","c3">>) 
    @@ 2 :> ("o1" :> <<"c1","c3">> @@ "o2" :> <<"c1">> @@ "o3" :> <<"c2","c3">>))

ASSUME C3!Correctness(State6)

(***************************************************************************)
(* This state is bad because it is not possible to extend the sequence of  *)
(* o2 without violating the correctness property.  However it still        *)
(* satisfies the correctness property.                                     *)
(***************************************************************************)
State7 == (1 :> ("o1" :> <<"c1">> @@ "o2" :> <<"c1">> @@ "o3" :> <<"c2","c3">>)
    @@ 2 :> ("o1" :> <<"c1","c3">> @@ "o2" :> <<"c1">> @@ "o3" :> <<"c2">>))

ASSUME C3!Correctness(State7)

(***************************************************************************)
(* A cycle involving three commands.                                       *)
(***************************************************************************)
State8 == (1 :> ("o1" :> <<"c3","c1">> @@ "o2" :> <<"c1","c2">> @@ "o3" :> <<"c2","c3">>) 
    @@ 2 :> ("o1" :> <<"c3","c1">> @@ "o2" :> <<"c1">> @@ "o3" :> <<"c2","c3">>))

ASSUME \neg C3!Correctness(State8)

=============================================================================
\* Modification History
\* Last modified Fri Jun 10 13:28:01 EDT 2016 by nano
\* Created Fri Jun 10 12:57:45 EDT 2016 by nano
