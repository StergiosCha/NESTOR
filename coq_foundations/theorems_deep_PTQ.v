(************************************************************************)
(*  PTQ_deep_Theorems.v -- Key metatheorems for the deep IL embedding   *)
(************************************************************************)

From Coq Require Import Classical Classical_Prop Nat PeanoNat.
Require Import PTQ_deep.
Set Implicit Arguments.

(* 1. every man walks -> a man walks (given there exists a man) *)

Theorem every_to_some_man_walks : forall i,
  (exists z : IndivConcept, man_den z i) ->
  eval_closed il_every_man_walks_c i ->
  eval_closed il_a_man_walks_c i.
Proof.
  intros i [z Hz] H.
  unfold eval_closed in *; simpl in *.
  exists z. auto.
Qed.

(* 2. every man walks -> Bill walks (given Bill is a man) *)

Theorem every_man_walks_inst_bill : forall i,
  man_den (fun _ => bill_e) i ->
  eval_closed il_every_man_walks_c i ->
  eval_closed il_bill_walks_c i.
Proof.
  intros i Hman H.
  unfold eval_closed in *; simpl in *. auto.
Qed.

(* 3. "the" entails "a" at the denotation level *)

Theorem the_entails_a_sem :
  forall (cn_d : Den ty_cn) (iv_d : Den ty_iv) i,
  (exists y : IndivConcept,
    (forall x, cn_d x i <-> x = y) /\ iv_d y i) ->
  (exists x : IndivConcept, cn_d x i /\ iv_d x i).
Proof.
  intros cn_d iv_d i [y [Huniq Hp]].
  exists y. split; [apply Huniq; reflexivity | exact Hp].
Qed.

(* 4. relative clause restriction:
      every (man that walks) runs -> every man who walks, runs *)

Theorem rel_clause_restricts : forall i,
  eval_closed il_every_man_that_walks_runs_c i ->
  (forall x : IndivConcept, man_den x i -> walk_den x i -> run_den x i).
Proof.
  intros i H.
  unfold eval_closed in H; simpl in H.
  intros x Hm Hw. apply H. auto.
Qed.

(* 5. Nec phi -> phi  (T axiom) *)

Theorem nec_T : forall (phi : ILClosed ty_t) (i : Index),
  eval_closed (nec_ phi) i -> eval_closed phi i.
Proof.
  intros phi i H. unfold eval_closed in *; simpl in *. apply H.
Qed.

(* 6. Nec phi -> Nec (Nec phi)  (S4 axiom) *)

Theorem nec_4 : forall (phi : ILClosed ty_t) (i : Index),
  eval_closed (nec_ phi) i -> eval_closed (nec_ (nec_ phi)) i.
Proof.
  intros phi i H. unfold eval_closed in *; simpl in *. auto.
Qed.

(* 7. extensional collapse: under the meaning postulate,
      quantification over concepts reduces to entities *)

Theorem every_man_walks_ext_collapse : forall i,
  eval_closed (mp2_cn_extensional c_man) i ->
  eval_closed il_every_man_walks_c i ->
  (forall e : Entity, man_den (rigid e) i -> walk_den (rigid e) i).
Proof.
  intros i Hmp H.
  unfold eval_closed in *; simpl in *.
  intros e Hman. apply H. exact Hman.
Qed.

(* 8. temperature puzzle -- non-entailment via countermodel *)

Parameter cm_idx : Index.
Parameter cm_varying : IndivConcept.
Parameter cm_other : Index.
Axiom cm_eq_here    : cm_varying cm_idx = ninety_e.
Axiom cm_diff_there : cm_varying cm_other <> ninety_e.
Axiom cm_nonrigid   : cm_varying <> rigid ninety_e.
Axiom cm_temp_spec  : forall x i, temperature_den x i <-> x = cm_varying.
Axiom cm_rise_var   : forall i, rise_den cm_varying i.
Axiom cm_rise_no    : ~ rise_den (rigid ninety_e) cm_idx.

Theorem temperature_puzzle :
  eval_closed il_temp_rises_c cm_idx /\
  ~ eval_closed il_ninety_rises_c cm_idx.
Proof.
  split.
  - exact (@temp_rises_holds cm_idx cm_varying cm_temp_spec cm_rise_var).
  - exact (@ninety_rises_fails cm_idx cm_rise_no).
Qed.

(* 9. beta-reduction / T4 equivalence *)

Theorem t4_beta_equiv : forall i,
  eval_closed il_every_man_walks_t4 i <->
  eval_closed il_every_man_walks_c i.
Proof.
  intro i. unfold eval_closed. simpl. split; auto.
Qed.

(* 10. down(up(alpha)) = alpha -- extension of intension *)

Theorem up_down_id :
  forall G t (e : IL G t) env i,
    eval (down (up e)) env i = eval e env i.
Proof.
  intros. simpl. reflexivity.
Qed.
