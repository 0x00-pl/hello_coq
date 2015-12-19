(* Seven Trees in One *)
(* http://www.thebigquestions.com/2013/05/09/seven-trees-in-one/ *)

Inductive Tree :=
| Nil : Tree
| Cons :Tree -> Tree -> Tree.

Notation "[ a , b ]" := (Cons a b).

Check (Cons (Cons Nil Nil) Nil).
Check ([[Nil, Nil], Nil]).

Definition combineT (zt:Tree*Tree*Tree*Tree*Tree*Tree*Tree) :Tree :=
  match zt with
    | (t1,t2,t3,t4,t5,t6,t7) =>
      match t1,t2,t3,t4 with
        | Nil,Nil,Nil,Nil =>
          match t5,t6 with
            | [t5a,t5b],_ =>
              [[[[Nil,t7],t6],t5a],t5b]
            | Nil,[_,_] =>
              [[[[[t6,t7],Nil],Nil],Nil],Nil]
            | Nil,Nil =>
              match t7 with
                | [[[[t7a,t7b],t7c],t7d],t7e] =>
                  [[[[[Nil,t7a],t7b],t7c],t7d],t7e]
                | _ => t7
              end
          end
        | _,_,_,_ =>
          [[[[[[t7,t6],t5],t4],t3],t2],t1]
      end
  end.


Eval compute in (combineT (Nil,Nil,[Nil,Nil],Nil,Nil,Nil,Nil)).

Definition splitT (t:Tree) :Tree*Tree*Tree*Tree*Tree*Tree*Tree :=
  match t with
    | [[[[[[t7,t6],t5],t4],t3],t2],t1] =>
      match t1,t2,t3,t4 with
        | Nil,Nil,Nil,Nil =>
          (* case 3 *)
          (Nil,Nil,Nil,Nil,Nil,[t7,t6],t5)
        | _,_,_,_ =>
          (* case 1 *)
          (t1,t2,t3,t4,t5,t6,t7)
      end
    | [[[[[Nil,t7a],t7b],t7c],t7d],t7e] =>
      (Nil,Nil,Nil,Nil,Nil,Nil,[[[[t7a,t7b],t7c],t7d],t7e])
    | [[[[Nil,t7],t6],t5a],t5b] =>
      (Nil,Nil,Nil,Nil,[t5a,t5b],t6,t7)
    | _ =>
      (Nil,Nil,Nil,Nil,Nil,Nil,t)
  end.

Definition test_case1_0 := ([Nil,Nil],Nil,Nil,Nil,Nil,Nil,Nil).
Definition test_case1_1 := (Nil,[Nil,Nil],Nil,Nil,Nil,Nil,Nil).
Definition test_case2_0 := (Nil,Nil,Nil,Nil,[Nil,Nil],Nil,Nil).
Definition test_case2_1 := (Nil,Nil,Nil,Nil,[Nil,Nil],Nil,[Nil,Nil]).
Definition test_case3_0 := (Nil,Nil,Nil,Nil,Nil,[Nil,Nil],Nil).
Definition test_case3_1 := (Nil,Nil,Nil,Nil,Nil,[Nil,Nil],[Nil,Nil]).
Definition test_case4_0 := (Nil,Nil,Nil,Nil,Nil,Nil,[[[[Nil,Nil],Nil],Nil],Nil]).
Definition test_case4_1 := (Nil,Nil,Nil,Nil,Nil,Nil,[[[[Nil,Nil],Nil],[Nil,Nil]],Nil]).
Definition test_case4_2 := (Nil,Nil,Nil,Nil,Nil,Nil,[[[[Nil,Nil],Nil],Nil],[Nil,Nil]]).
Definition test_case4_3 := (Nil,Nil,Nil,Nil,Nil,Nil,[[[[Nil,[Nil,Nil]],Nil],Nil],Nil]).
Definition test_case5_0 := (Nil,Nil,Nil,Nil,Nil,Nil,Nil).
Definition test_case5_1 := (Nil,Nil,Nil,Nil,Nil,Nil,[Nil,Nil]).

Eval compute in splitT (combineT test_case1_0) = test_case1_0.
Eval compute in splitT (combineT test_case1_1) = test_case1_1.
Eval compute in splitT (combineT test_case2_0) = test_case2_0.
Eval compute in splitT (combineT test_case2_1) = test_case2_1.
Eval compute in splitT (combineT test_case3_0) = test_case3_0.
Eval compute in splitT (combineT test_case3_1) = test_case3_1.
Eval compute in splitT (combineT test_case4_0) = test_case4_0.
Eval compute in splitT (combineT test_case4_1) = test_case4_1.
Eval compute in splitT (combineT test_case4_2) = test_case4_2.
Eval compute in splitT (combineT test_case4_3) = test_case4_3.
Eval compute in splitT (combineT test_case5_0) = test_case5_0.
Eval compute in splitT (combineT test_case5_1) = test_case5_1.


Goal forall zt, splitT (combineT zt) = zt.
Proof.
  intros.
  unfold combineT.
  destruct zt as [[[[[[t1 t2] t3] t4] t5] t6] t7].
  destruct t5; destruct t6; destruct t7; simpl;
  destruct t1; destruct t2; destruct t3; destruct t4; try reflexivity.
  destruct t7_1; try reflexivity.
  destruct t7_1_1; try reflexivity.
  destruct t7_1_1_1; try reflexivity.
Qed.


Goal forall t, combineT (splitT t) = t.
Proof.
  intro t1. unfold splitT.
  destruct t1 as [_|t2]. reflexivity.
  destruct t2 as [_|t3]. reflexivity.
  destruct t3 as [_|t4]. reflexivity.
  destruct t4 as [_|t5]. reflexivity.
  destruct t5 as [_|t6]. reflexivity.
  destruct t6. reflexivity.

  destruct t4_1; destruct t3_1; destruct t2_1; destruct t1_1; reflexivity.
Qed.

