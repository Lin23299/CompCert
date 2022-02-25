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

    Inductive frame :Type :=
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

  (* Modeling the linking of "linked C program"(high level program) to asm program. The linked program will not have a C level outgoing interface anymore, because such linking with other C components have been done in the previous stage.  *)
    Inductive at_external: state -> query li -> Prop :=
      | at_external_intro_C s q k:
          Smallstep.at_external (C se) s q ->
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




      1.asm                       lib.asm                        ????

    A -->> A         ++            A -->> A            =      A + A -->> A

                                                                 ????

              1.asm + lib.asm = out.asm                ->    A -->> A

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
    Admitted.

End LINK'.


Section FSIM.
End FSIM.

Definition compose {li_C li_A}
           (C: Smallstep.semantics li_C li_C)
           (A: Smallstep.semantics li_A li_C) :=
  option_map (semantics_link_lib C A) (link (skel C) (skel A)).

Lemma compose_simulation {li_C li_A} (cc: callconv li_C li_A)
      (C1 : Smallstep.semantics li_C li_C) (A : Smallstep.semantics li_A li_C)
      (A1 : Smallstep.semantics li_A li_A) (A': Smallstep.semantics li_A li_A)
      L1 L2:
  forward_simulation cc cc C1 A1 ->
  forward_simulation cc cc A A' ->
  compose C1 A = Some L1 ->
  compose A1 A' = Some L2 ->
  forward_simulation cc_id cc L1 L2.
Proof.
  Admitted.
