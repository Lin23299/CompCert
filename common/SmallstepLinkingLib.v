Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Smallstep.
Require Import Linking.
Require Import Classical.

(** NB: we assume that all components are deterministic and that their
  domains are disjoint. *)

Ltac subst_dep :=
  subst;
  lazymatch goal with
    | H: existT ?P ?x _ = existT ?P ?x _ |- _ =>
      apply inj_pair2 in H; subst_dep
    | _ =>
      idtac
  end.


Section LINK'.
  Context {li1}{li2} (C: semantics li1 li1) (A: semantics li2 li1).

  (** * Definition *)

  Section WITH_SE.
    Context (se: Genv.symtbl).

    Inductive frame : Type :=
    | caller:  Smallstep.state C -> frame
    | callee:  Smallstep.state A -> frame.

    Notation state := (list frame).

    Inductive step: state -> trace -> state -> Prop :=
      | step_internal_C s t s' k :
          Step (C se) s t s' ->
          step (caller s :: k) t (caller s' :: k)
      | step_internal_A s t s' k :
          Step (A se) s t s' ->
          step (callee s :: k) t (callee s' :: k)
      | step_push s q s' k :
          Smallstep.at_external (C se) s q ->
          valid_query (A se) q = true ->
          Smallstep.initial_state (A se) q s' ->
          step (caller s :: k) E0 (callee s' :: caller s :: k)
      | step_pop s sk r s' k :
          Smallstep.final_state (A se) s r ->
          Smallstep.after_external (C se) sk r s' ->
          step (callee s :: caller sk :: k) E0 (caller s' :: k).

    Inductive initial_state (q: query li1): state -> Prop :=
      | initial_state_intro s :
          valid_query (C se) q = true ->
          Smallstep.initial_state (C se) q s ->
          initial_state q (caller s :: nil).

    Definition li := sum_li li1 li2.

    Inductive at_external: state -> query li -> Prop :=
      | at_external_intro_C s q k:
          Smallstep.at_external (C se) s q ->
          valid_query (A se) q = false ->
          at_external (caller s :: k) (inl q)
      | at_external_intro_A s q k:
          Smallstep.at_external (A se) s q ->
          at_external (callee s :: k) (inr q).

    Inductive after_external: state -> reply li -> state -> Prop :=
      | after_external_intro_C s r s' k:
          Smallstep.after_external (C se) s r s' ->
          after_external (caller s :: k) (inl r) (caller s' :: k)
      | after_external_intro s r s' k:
          Smallstep.after_external (A se) s r s' ->
          after_external (callee s :: k) (inr r) (callee s' :: k).

    Inductive final_state: state -> reply li1 -> Prop :=
      | final_state_intro s r :
          Smallstep.final_state (C se) s r ->
          final_state (caller s :: nil) r.

    Definition valid_query q := valid_query (C se) q.

  End WITH_SE.

  Context (sk: AST.program unit unit).

  Definition semantics_link_lib: semantics li li1 :=
    {|
      activate se :=
        {|
          Smallstep.step ge := step se;
          Smallstep.valid_query := valid_query se;
          Smallstep.initial_state := initial_state se;
          Smallstep.at_external := at_external se;
          Smallstep.after_external := after_external se;
          Smallstep.final_state := final_state se;
          Smallstep.globalenv := tt;
        |};
      skel := sk;
    |}.
(**

       1.c                      lib.asm + wrapper
     C -->> C         ++            A -->> C            =      C + A -->> C


                                                              sum of callconv?

      1.asm                       lib.asm                      vertical composition'  ????

    A -->> A         ++            A -->> A            =      A + A -->> A

                                                                 collapse

              1.asm + lib.asm = out.asm                ->    A -->> A


1. Why wrapper ?

2. Diff mem model -> memory model transformation between the interface -> NMM works!

3. Diff language C + IMP + + + + + + + + + + +

4. Diff 
*)
  (** * Properties *)

  Lemma star_internal_C se s t s' k:
    Star (C se) s t s' ->
    star (fun _ => step se) tt (caller s :: k) t (caller s' :: k).
  Proof.
    induction 1; [eapply star_refl | eapply star_step]; eauto.
    constructor; auto.
  Qed.

  Lemma star_internal_A se s t s' k:
    Star (A se) s t s' ->
    star (fun _ => step se) tt (callee s :: k) t (callee s' :: k).
  Proof.
    induction 1; [eapply star_refl | eapply star_step]; eauto.
    constructor; auto.
  Qed.

  Lemma plus_internal_C se s t s' k:
    Plus (C se) s t s' ->
    plus (fun _ => step se) tt (caller s :: k) t (caller s' :: k).
  Proof.
    destruct 1; econstructor; eauto using step_internal_C, star_internal_C.
  Qed.

  Lemma plus_internal_A se s t s' k:
    Plus (A se) s t s' ->
    plus (fun _ => step se) tt (callee s :: k) t (callee s' :: k).
  Proof.
    destruct 1; econstructor; eauto using step_internal_A, star_internal_A.
  Qed.

  (** * Receptiveness and determinacy *)

  Lemma semantics_receptive:
    receptive A -> receptive C ->
    receptive semantics_link_lib.
  Proof.
    intros RA RC se. unfold receptive in *.
    constructor; cbn.
    - intros s t1 s1 t2 STEP Ht. destruct STEP.
      + edestruct @sr_receptive. apply RC. eauto. eauto. eexists. eapply step_internal_C; eauto.
      + edestruct @sr_receptive. apply RA. eauto. eauto. eexists. eapply step_internal_A; eauto.
      + inversion Ht; clear Ht; subst. eexists. eapply step_push; eauto.
      + inversion Ht; clear Ht; subst. eexists. eapply step_pop; eauto.
    - intros s t s' STEP. destruct STEP; cbn; eauto.
      eapply sr_traces. apply RC. eauto.
      eapply sr_traces. apply RA. eauto.
  Qed.

  Lemma semantics_determinate:
    determinate A -> determinate C ->
    determinate semantics_link_lib.
  Proof.
    intros HA HC se. unfold determinate in *.
        constructor; cbn.
    - destruct 1; inversion 1; subst_dep.
      + edestruct (sd_determ (HC se) s t s' t2 s'0); intuition eauto; congruence.
      + eelim sd_at_external_nostep. apply HC. all: eauto.
      + edestruct (sd_determ (HA se) s t s' t2 s'0); intuition eauto; congruence.
      + eelim sd_final_nostep; eauto.
      + eelim sd_at_external_nostep. apply HC. all: eauto.
      + destruct (sd_at_external_determ (HC se) s q q0); eauto.
        destruct (sd_initial_determ (HA se) q s' s'0); eauto.
        intuition auto. constructor.
      + eelim sd_final_nostep; eauto.
      + edestruct (sd_final_determ (HA se) s r r0); eauto.
        edestruct (sd_after_external_determ (HC se) sk0 r s' s'0); eauto.
        intuition auto. constructor.
    - intros s t s' STEP. destruct STEP; cbn; eauto.
      eapply sd_traces. 2: eauto. eauto.
      eapply sd_traces. 2: eauto. eauto.
    - destruct 1; inversion 1; subst.
      edestruct (sd_initial_determ (HC se) q s s0); eauto.
    - destruct 1.
      + inversion 1; subst_dep.
      eapply sd_at_external_nostep. 2: eauto. 2: eauto. eauto.
      edestruct (sd_at_external_determ (HC se) s q q0); eauto. congruence.
      + inversion 1; subst_dep.
      eapply sd_at_external_nostep; eauto.
      eapply sd_final_noext; eauto.
    - destruct 1.
      + inversion 1; subst_dep. f_equal.
      eapply sd_at_external_determ; eauto.
      + inversion 1; subst_dep. f_equal.
      eapply sd_at_external_determ; eauto.
    - destruct 1. inversion 1; subst_dep.
      edestruct (sd_after_external_determ (HC se) s r s' s'0); eauto.
      inversion 1; subst_dep.
      edestruct (sd_after_external_determ (HA se) s r s' s'0); eauto.
    - destruct 1. inversion 1; subst_dep.
      + eapply sd_final_nostep. 2: eauto. 2: eauto. eauto.
      + eapply sd_final_noext.  2: eauto. 2: eauto. eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_final_noext.  2: eauto. 2: eauto. eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_final_determ. apply HC. eauto. eauto.
Qed.

End LINK'.

Section SUMCC.
  Context {li1}{li1'}{li2}{li2'} (cc1: callconv li1 li1')(cc2: callconv li2 li2').

  Definition li1_sum_li2 := sum_li li1 li2.
  Definition li1'_sum_li2' := sum_li li1' li2'.

  Definition ccworld_sum := sum (ccworld cc1) (ccworld cc2).
  Definition match_senv_sum w se1 se2 : Prop :=
    match w with
      | inl w1 => match_senv cc1 w1 se1 se2
      | inr w2 => match_senv cc2 w2 se1 se2
    end.

  Definition match_query_sum (w:ccworld_sum) (q1: query li1_sum_li2) (q2: query li1'_sum_li2') : Prop :=
    match w,q1,q2 with
      | inl w1, inl q11, inl q12 => match_query cc1 w1 q11 q12
      | inr w2, inr q21, inr q22 => match_query cc2 w2 q21 q22
      | _,_,_ => False
    end.

  Definition match_reply_sum (w:ccworld_sum) (r1: reply li1_sum_li2) (r2: reply li1'_sum_li2') : Prop :=
    match w,r1,r2 with
      | inl w1, inl r11, inl r12 => match_reply cc1 w1 r11 r12
      | inr w2, inr r21, inr r22 => match_reply cc2 w2 r21 r22
      | _,_,_ => False
    end.

  Program Definition sum_cc :=
    mk_callconv _ _ ccworld_sum match_senv_sum match_query_sum match_reply_sum _ _.
  Next Obligation.
    destruct w; simpl in H; eapply match_senv_public_preserved; eauto.
  Qed.
  Next Obligation.
    destruct w; simpl in H; eapply match_senv_valid_for; eauto.
  Qed.

(*  Program Definition sum_cc {li1_sum_li2}{li1'_sum_li2'}: callconv li1_sum_li2 li1'_sum_li2' :=
    {|
      ccworld := unit;
      match_senv := match_senv;
      match_query := match_query;
      match_reply := match_reply;
    |}.
  Next Obligation. *)
End SUMCC.

Section FSIM.
  Context {liC liA} (cc: callconv liC liA).

  Context (C1 : Smallstep.semantics liC liC) (A : Smallstep.semantics liA liC).
  Context (A1 : Smallstep.semantics liA liA) (A': Smallstep.semantics liA liA).
  Context (H1 : fsim_components cc cc C1 A1) (H2: fsim_components cc_id cc A A').
  Context (se1 se2: Genv.symtbl) (w: ccworld cc).
  Context (Hse: match_senv cc w se1 se2).
  Context (Hse1 : Genv.valid_for (skel C1) se1) (Hse2 : Genv.valid_for (skel C1) se2).

  Definition index : Type := (fsim_index H1) + (fsim_index H2).

  Inductive order : index -> index -> Prop :=
    |order_l x y : fsim_order H1 x y -> order (inl x) (inl y)
    |order_r x y : fsim_order H2 x y -> order (inr x) (inr y).

  Inductive match_topframes wk : index -> frame C1 A -> frame A1 A' -> Prop :=
    |match_topframes_C s1 s2 idx:
      match_senv cc wk se1 se2 -> (*????????*)
      Genv.valid_for (skel C1) se1 ->
      fsim_match_states H1 se1 se2 wk idx s1 s2 ->
      match_topframes wk (inl idx) (caller C1 A s1) (caller A1 A' s2)
    |match_topframes_A s1 s2 idx:
      match_senv cc wk se1 se2 -> (*?????*)
      Genv.valid_for (skel A) se1 ->
      fsim_match_states H2 se1 se2 wk idx s1 s2 ->
      match_topframes wk (inr idx) (callee C1 A s1) (callee A1 A' s2).

  Inductive match_contframes wk wk': frame C1 A -> frame A1 A' -> Prop :=
    | match_contframes_C s1 s2:
      match_senv cc wk' se1 se2 ->
      (forall r1 r2 s1', match_reply cc wk r1 r2 ->
       Smallstep.after_external (C1 se1) s1 r1 s1' ->
       exists idx s2',
         Smallstep.after_external (A1 se2) s2 r2 s2' /\
         fsim_match_states H1 se1 se2 wk' idx s1' s2') ->
      match_contframes wk wk'
        (caller C1 A s1)
        (caller A1 A' s2).

  Inductive match_states : index -> list (frame C1 A) -> list (frame A1 A') -> Prop :=
    |match_states_caller wk idx f1 f2 :
      match_topframes wk idx f1 f2 ->
      match_states idx (f1::nil) (f2::nil).
   | match_states_callee wk wk' idx f1 f2 k1 k2:
     

  Variable match_states : index -> list (frame C1 A) -> list (frame A1 A') -> Prop.

  Lemma semantics_simulation sk1 sk2:
    fsim_properties (sum_cc cc cc_id) cc se1 se2 w
      (semantics_link_lib C1 A sk1 se1)
      (semantics_link_lib A1 A' sk2 se2)
      index order match_states.
    Admitted.
End FSIM.


Definition compose {li_C li_A}
           (C: Smallstep.semantics li_C li_C)
           (A: Smallstep.semantics li_A li_C) :=
  option_map (semantics_link_lib C A) (link (skel C) (skel A)).

Lemma compose_simulation {li_C li_A} (cc: callconv li_C li_A)
      (C1 : Smallstep.semantics li_C li_C) (A : Smallstep.semantics li_A li_C)
      (A1 : Smallstep.semantics li_A li_A) (A': Smallstep.semantics li_A li_A)
      (L1 : Smallstep.semantics (sum_li li_C li_A) li_C)
      (L2 : Smallstep.semantics (sum_li li_A li_A) li_A):
  forward_simulation cc cc C1 A1 ->
  forward_simulation cc_id cc A A' ->
  compose C1 A = Some L1 ->
  compose A1 A' = Some L2 ->
  forward_simulation (sum_cc cc cc_id) cc L1 L2.
Proof.
  intros [Ha] [Hb] H1 H2. unfold compose in *. unfold option_map in *.
  destruct (link (skel C1) (skel A)) as [sk1|] eqn:Hsk1; try discriminate. inv H1.
  destruct (link (skel A1) (skel A')) as [sk2|] eqn:Hsk2; try discriminate. inv H2.
  constructor.
(*  eapply Forward_simulation with (order cc L1 L2 HL) (match_states cc L1 L2 HL).
  - destruct Ha, Hb. cbn. congruence.
  - intros se1 se2 w Hse Hse1.
    eapply semantics_simulation; eauto.
    pose proof (link_linkorder _ _ _ Hsk1) as [Hsk1a Hsk1b].
    intros [|]; cbn; eapply Genv.valid_for_linkorder; eauto.
  - clear - HL. intros [i x].
    induction (fsim_order_wf (HL i) x) as [x Hx IHx].
    constructor. intros z Hxz. inv Hxz; subst_dep. eauto. *)
  Admitted.
