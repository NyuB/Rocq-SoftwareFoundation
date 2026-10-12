(** * Equiv: Program Equivalence *)

Set Warnings "-notation-overridden".
From PLF Require Import Maps.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import PeanoNat. Import Nat.
From Stdlib Require Import EqNat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import FunctionalExtensionality.
From PLF Require Export Imp.

(* Helpers *)
Ltac intros_absurd := intros intros_absurd_Contra; discriminate intros_absurd_Contra.
Lemma st_eq_absurd: forall (x: string) n n', n <> n' -> ~ (x !-> n) = (x !-> n').
Proof.
intros x n n' Neq H. assert ((x !-> n) x = (x !-> n') x) as Hf. { rewrite H.  reflexivity. }
rewrite ? t_update_eq in Hf. apply Neq. apply Hf. 
Qed.

(** *** Before You Get Started:

    - Create a fresh directory for this volume. Do not try to mix the
      files from this volume with files from _Logical Foundations_ in
      the same directory: the result will not make you happy.

      You can either start with an empty directory and populate it
      with the files listed below (and others as you go along), or
      else download the whole PLF zip file and unzip it.

    - The new directory should contain at least the following files:
         - [Imp.v] (make sure it is the one from the PLF distribution,
           not the one from LF: they are slightly different);
         - [Maps.v] (ditto)
         - [Equiv.v] (this file)
         - [_CoqProject], containing the following line:

           -Q . PLF

    - If you see errors like this...

           Compiled library PLF.Maps (in file .../plf/Maps.vo)
           makes inconsistent assumptions over library Rocq.Init.Logic

      ... it may mean something went wrong with the above steps.
      Doing "[make clean]" (or manually removing everything except
      [.v] and [_CoqProject] files) may help.

    - If you are using VSCode with the VSCoq extension, you'll then
      want to open a new window in VSCode, click [Open Folder > plf],
      and run [make].  If you get an error like "Cannot find a
      physical path..." error, it may be because you didn't open plf
      directly (you instead opened a folder containing both lf and
      plf, for example). *)

(** *** Advice for Working on Exercises:

    - Most of the Rocq proofs we ask you to do in this chapter are
      similar to proofs that we've provided.  Before starting to work
      on exercises, take the time to work through our proofs (both
      informally and in Rocq) and make sure you understand them in
      detail.  This will save you a lot of effort.

    - The Rocq proofs we're doing now are sufficiently complicated that
      it is more or less impossible to complete them by random
      experimentation or following your nose.  You need to start with
      an idea about why the property is true and how the proof is
      going to go.  The best way to do this is to write out at least a
      sketch of an informal proof on paper -- one that intuitively
      convinces you of the truth of the theorem -- before starting to
      work on the formal one.  Alternately, grab a friend and try to
      convince them that the theorem is true; then try to formalize
      your explanation.

    - Use automation to save work!  The proofs in this chapter can get
      pretty long if you try to write out all the cases explicitly. *)

(* ################################################################# *)
(** * Behavioral Equivalence *)

(** In an earlier chapter, we investigated the correctness of a very
    simple program transformation: the [optimize_0plus] function.  The
    programming language we were considering was the first version of
    the language of arithmetic expressions -- with no variables -- so
    in that setting it was very easy to define what it means for a
    program transformation to be correct: it should always yield a
    program that evaluates to the same number as the original.

    To talk about the correctness of program transformations for the
    full Imp language -- in particular, assignment -- we need to
    consider the role of mutable state and develop a more
    sophisticated notion of correctness, which we'll call _behavioral
    equivalence_. *)

(** For example:
      - [X + 2] is behaviorally equivalent to [1 + X + 1]
      - [X - X] is behaviorally equivalent to [0]
      - [(X - 1) + 1] is _not_ behaviorally equivalent to [X]   *)

(* ================================================================= *)
(** ** Definitions *)

(** For [aexp]s and [bexp]s with variables, the definition we want is
    clear: Two [aexp]s or [bexp]s are "behaviorally equivalent" if
    they evaluate to the same result in every state. *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

(** Here are some simple examples of equivalences of arithmetic
    and boolean expressions. *)

Theorem aequiv_example:
  aequiv
    <{ X - X }>
    <{ 0 }>.
Proof.
  intros st. simpl. lia.
Qed.

Theorem bequiv_example:
  bequiv
    <{ X - X = 0 }>
    <{ true }>.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

(** For commands, the situation is a little more subtle.  We
    can't simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are started in the
    same initial state," because some commands, when run in some
    starting states, don't terminate in any final state at all!

    What we need instead is this: two commands are behaviorally
    equivalent if, for any given starting state, they either (1) both
    diverge or else (2) both terminate in the same final state.  A
    compact way to express this is "if the first one terminates in a
    particular state then so does the second, and vice versa." *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

(* ================================================================= *)
(** ** Simple Examples *)

(** For examples of command equivalence, let's start by looking at
    a trivial equivalence involving [skip]: *)

Theorem skip_left : forall c,
  cequiv
    <{ skip; c }>
    c.
Proof.
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st.
    + apply E_Skip.
    + assumption.
Qed.

(** **** Exercise: 2 stars, standard (skip_right)

    Prove that adding a [skip] _after_ a command also results in an
    equivalent program *)

Theorem skip_right : forall c,
  cequiv
    <{ c; skip }>
    c.
Proof.
intros c. split; intros H.
- inversion H. subst. inversion H5. subst. assumption.
- apply E_Seq with st'.
  + assumption.
  + apply E_Skip.
Qed.
(** [] *)

(** Similarly, here is a simple equivalence that optimizes [if]
    commands: *)

Theorem if_true_simple : forall c1 c2,
  cequiv
    <{ if true then c1 else c2 end }>
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + assumption.
    + discriminate.
  - (* <- *)
    apply E_IfTrue.
    + reflexivity.
    + assumption.  Qed.

(** Of course, no programmer would write a conditional whose condition
    is literally [true].  (At least, no human programmer -- compilers
    and macro preprocessors do this sort of thing internally all the
    time!) But they might write one whose condition is _equivalent_ to
    true: *)

(** _Theorem_: If [b] is equivalent to [true], then [if b then c1
    else c2 end] is equivalent to [c1].
   _Proof_:
     - ([->]) We must show, for all [st] and [st'], that if [st =[
       if b then c1 else c2 end ]=> st'] then [st =[ c1 ]=> st'].

       Proceed by cases on the rules that could possibly have been
       used to show [st =[ if b then c1 else c2 end ]=> st'], namely
       [E_IfTrue] and [E_IfFalse].

       - Suppose the final rule in the derivation of [st =[ if b
         then c1 else c2 end ]=> st'] was [E_IfTrue].  We then have,
         by the premises of [E_IfTrue], that [st =[ c1 ]=> st'].
         This is exactly what we set out to prove.

       - On the other hand, suppose the final rule in the derivation
         of [st =[ if b then c1 else c2 end ]=> st'] was [E_IfFalse].
         We then know that [beval st b = false] and [st =[ c2 ]=> st'].

         Recall that [b] is equivalent to [true], i.e., forall [st],
         [beval st b = beval st <{true}> ].  In particular, this means
         that [beval st b = true], since [beval st <{true}> = true].  But
         this is a contradiction, since [E_IfFalse] requires that
         [beval st b = false].  Thus, the final rule could not have
         been [E_IfFalse].

     - ([<-]) We must show, for all [st] and [st'], that if
       [st =[ c1 ]=> st'] then
       [st =[ if b then c1 else c2 end ]=> st'].

       Since [b] is equivalent to [true], we know that [beval st b] =
       [beval st <{true}> ] = [true].  Together with the assumption that
       [st =[ c1 ]=> st'], we can apply [E_IfTrue] to derive
       [st =[ if b then c1 else c2 end ]=> st'].  []

   Here is the formal version of this proof: *)

Theorem if_true: forall b c1 c2,
  bequiv b <{true}>  ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b evaluates to true *)
      assumption.
    + (* b evaluates to false (contradiction) *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      discriminate.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    apply Hb. Qed.

(** **** Exercise: 2 stars, standard, especially useful (if_false) *)
Theorem if_false : forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
intros b c1 c2 BFalse. unfold bequiv in BFalse. split; intros H.
- inversion H; subst.
  + rewrite BFalse in H5. discriminate H5.
  + assumption.
- apply E_IfFalse. { apply (BFalse st). } { assumption. }
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (swap_if_branches)

    Show that we can swap the branches of an [if] if we also negate its
    condition. *)

Lemma negb_neg: forall b b', negb b = b' -> b = negb b'.
Proof.
intros b b' H. destruct b; destruct b'; (try reflexivity); (try discriminate H).
Qed.

Theorem swap_if_branches : forall b c1 c2,
  cequiv
    <{ if b   then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
intros b c1 c2. split; intros H.
- inversion H; subst; [apply E_IfFalse | apply E_IfTrue];
    try (assumption);
    simpl; rewrite H5; reflexivity.
- inversion H; subst; [apply E_IfFalse | apply E_IfTrue];
    try (assumption);
    simpl in *;
    apply negb_neg in H5; simpl in H5; apply H5.
Qed.
(** [] *)

(** For [while] loops, we can give a similar pair of theorems.  A loop
    whose guard is equivalent to [false] is equivalent to [skip],
    while a loop whose guard is equivalent to [true] is equivalent to
    [while true do skip end] (or any other non-terminating program). *)

(** The first of these facts is easy. *)

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileFalse *)
      apply E_Skip.
    + (* E_WhileTrue *)
      rewrite Hb in H2. discriminate.
  - (* <- *)
    inversion H. subst.
    apply E_WhileFalse.
    apply Hb.  Qed.

(** **** Exercise: 2 stars, advanced, optional (while_false_informal)

    Write an informal proof of [while_false].

(* FILL IN HERE *)
*)
(** [] *)

(** To prove the second fact, we need an auxiliary lemma stating that
    [while] loops whose guards are equivalent to [true] never
    terminate. *)

(** _Lemma_: If [b] is equivalent to [true], then it cannot be
    the case that [st =[ while b do c end ]=> st'].

    _Proof_: Suppose that [st =[ while b do c end ]=> st'].  We show,
    by induction on a derivation of [st =[ while b do c end ]=> st'],
    that this assumption leads to a contradiction. The only two cases
    to consider are [E_WhileFalse] and [E_WhileTrue]; the others
    are contradictory.

    - Suppose [st =[ while b do c end ]=> st'] is proved using rule
      [E_WhileFalse].  Then by assumption [beval st b = false].  But
      this contradicts the assumption that [b] is equivalent to
      [true].

    - Suppose [st =[ while b do c end ]=> st'] is proved using rule
      [E_WhileTrue].  We must have:

      1. [beval st b = true], and
      2. there is some [st0] such that [st =[ c ]=> st0] and
         [st0 =[ while b do c end ]=> st'].
      3. Also, we are given an induction hypothesis saying that
         [st0 =[ while b do c end ]=> st'] leads to a contradiction,

      We obtain a contradiction by 2 and 3. [] *)

Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> ->
  ~( st =[ while b do c end ]=> st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember <{ while b do c end }> as cw eqn:Heqcw.
  induction H;
  (* Most rules don't apply; we rule them out by inversion: *)
  inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for while loops: *)
  - (* E_WhileFalse *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. discriminate.
  - (* E_WhileTrue *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.

(** **** Exercise: 2 stars, standard, optional (while_true_nonterm_informal)

    Explain what the lemma [while_true_nonterm] means in English.

(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (while_true)

    Prove the following theorem. _Hint_: You'll want to use
    [while_true_nonterm] here. *)

Theorem while_true : forall b c,
  bequiv b <{true}>  ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.
intros b c BT. split; intros H.
- exfalso. apply (while_true_nonterm b c st st'); assumption.
- exfalso.
  assert (bequiv BTrue BTrue). { split; reflexivity. }
  apply (while_true_nonterm BTrue CSkip st st'); assumption.
Qed.
(** [] *)

(** A more interesting fact about [while] commands is that any number
    of copies of the body can be "unrolled" without changing meaning.

    Loop unrolling is an important transformation in any real
    compiler, so its correctness is of more than just academic
    interest! *)

Theorem loop_unrolling : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
Proof.
  (* WORKED IN CLASS *)
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* loop doesn't run *)
      apply E_IfFalse.
      * assumption.
      * apply E_Skip.
    + (* loop runs *)
      apply E_IfTrue.
      * assumption.
      * apply E_Seq with (st' := st'0).
        -- assumption.
        -- assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* loop runs *)
      inversion H5; subst.
      apply E_WhileTrue with (st' := st'0).
      * assumption.
      * assumption.
      * assumption.
    + (* loop doesn't run *)
      inversion H5; subst. apply E_WhileFalse. assumption.  Qed.

(** **** Exercise: 2 stars, standard, optional (seq_assoc) *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>.
Proof.
intros c1 c2 c3. split; intros H.
- inversion H. subst. inversion H2. subst. apply E_Seq with (st':=st'1).
  + assumption.
  + apply E_Seq with (st' := st'0); assumption.
- inversion H. subst. inversion H5. subst. apply E_Seq with (st' := st'1).
  + apply E_Seq with (st' := st'0); assumption.
  + assumption.
Qed.
(** [] *)

(** Proving program properties involving assignments is one place
    where the fact that we are treating equality on program states
    extensionally (e.g., [x !-> m x ; m] and [m] are equal maps) comes
    in handy. *)

Theorem identity_assignment : forall x,
  cequiv
    <{ x := x }>
    <{ skip }>.
Proof.
  intros.
  split; intro H; inversion H; subst; clear H.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x := x ]=> (x !-> st' x ; st')).
    { apply E_Asgn. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (assign_aequiv) *)
Theorem assign_aequiv : forall (X : string) (a : aexp),
  aequiv <{ X }> a ->
  cequiv <{ skip }> <{ X := a }>.
Proof.
intros X a HA. split; intros H.

- rewrite <- (t_update_same _ st' X).
  inversion H. subst.
  apply (E_Asgn st' a (st' X) X).
  unfold aequiv in HA.
  specialize HA with st'.
  simpl in HA. rewrite HA. reflexivity.
- inversion H. subst.
  unfold aequiv in HA.
  specialize HA with st. simpl in HA. rewrite <- HA.
  rewrite t_update_same. apply E_Skip.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (equiv_classes) *)

(** Given the following programs, group together those that are
    equivalent in Imp. Your answer should be given as a list of lists,
    where each sub-list represents a group of equivalent programs. For
    example, if you think programs (a) through (h) are all equivalent
    to each other, but not to (i), your answer should look like this:

       [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
         [prog_i] ]

    Write down your answer below in the definition of
    [equiv_classes]. *)

Definition prog_a : com :=
  <{ while X > 0 do
       X := X + 1
     end }>.

Definition prog_b : com :=
  <{ if (X = 0) then
       X := X + 1;
       Y := 1
     else
       Y := 0
     end;
     X := X - Y;
     Y := 0 }>.

Definition prog_c : com :=
  <{ skip }> .

Definition prog_d : com :=
  <{ while X <> 0 do
       X := (X * Y) + 1
     end }>.

Definition prog_e : com :=
  <{ Y := 0 }>.

Definition prog_f : com :=
  <{ Y := X + 1;
     while X <> Y do
       Y := X + 1
     end }>.

Definition prog_g : com :=
  <{ while true do
       skip
     end }>.

Definition prog_h : com :=
  <{ while X <> X do
       X := X + 1
     end }>.

Definition prog_i : com :=
  <{ while X <> Y do
       X := Y + 1
     end }>.

Definition equiv_classes : list (list com) :=
[
  (* terminate doing nothing iff X = 0 *)
  [prog_a; prog_d];
  (* non terminating *)
  [prog_f; prog_g; prog_i];
  (*  Y := 0
      for prog_b:
      if X := 0 then X := 0; Y := 0
      else X := X; Y := 0
      <=> X := X; Y := 0
      <=> Y := 0    
  *)
  [prog_b; prog_e];
  (* skip *)
  [prog_c; prog_h]
].

(* Do not modify the following line: *)
Definition manual_grade_for_equiv_classes : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Properties of Behavioral Equivalence *)

(** We next consider some fundamental properties of program
    equivalence. *)

(* ================================================================= *)
(** ** Behavioral Equivalence is an Equivalence *)

(** First, let's verify that the equivalences on [aexps], [bexps], and
    [com]s really are _equivalences_ -- i.e., that they are reflexive,
    symmetric, and transitive.  The proofs are all easy. *)

Lemma refl_aequiv : forall (a : aexp),
  aequiv a a.
Proof.
  intros a st. reflexivity.  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp),
  bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com),
  cequiv c c.
Proof.
  unfold cequiv. intros c st st'. reflexivity.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  rewrite H. reflexivity.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  rewrite H12. apply H23.
Qed.

(* ================================================================= *)
(** ** Behavioral Equivalence Is a Congruence *)

(** Less obviously, behavioral equivalence is also a _congruence_.
    That is, the equivalence of two subprograms implies the
    equivalence of the larger programs in which they are embedded:

                 aequiv a a'
         -------------------------
         cequiv (x := a) (x := a')

              cequiv c1 c1'
              cequiv c2 c2'
         --------------------------
         cequiv (c1;c2) (c1';c2')

    ... and so on for the other forms of commands. *)

(** (Note that we are using the inference rule notation here not
    as part of an inductive definition, but simply to write down some
    valid implications in a readable format. We prove these
    implications below.) *)

(** We will see a concrete example of why these congruence
    properties are important in the following section (in the proof of
    [fold_constants_com_sound]), but the main idea is that they allow
    us to replace a small part of a large program with an equivalent
    small part and know that the whole large programs are equivalent
    _without_ doing an explicit proof about the parts that didn't
    change -- i.e., the "proof burden" of a small change to a large
    program is proportional to the size of the change, not the
    program! *)

Theorem CAsgn_congruence : forall x a a',
  aequiv a a' ->
  cequiv <{x := a}> <{x := a'}>.
Proof.
  intros x a a' Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Asgn.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Asgn.
    rewrite Heqv. reflexivity.  Qed.

(** The congruence property for loops is a little more interesting,
    since it requires induction.

    _Theorem_: Equivalence is a congruence for [while] -- that is, if
    [b] is equivalent to [b'] and [c] is equivalent to [c'], then
    [while b do c end] is equivalent to [while b' do c' end].

    _Proof_: Suppose [b] is equivalent to [b'] and [c] is
    equivalent to [c'].  We must show, for every [st] and [st'], that
    [st =[ while b do c end ]=> st'] iff [st =[ while b' do c'
    end ]=> st'].  We consider the two directions separately.

      - ([->]) We show that [st =[ while b do c end ]=> st'] implies
        [st =[ while b' do c' end ]=> st'], by induction on a
        derivation of [st =[ while b do c end ]=> st'].  The only
        nontrivial cases are when the final rule in the derivation is
        [E_WhileFalse] or [E_WhileTrue].

          - [E_WhileFalse]: In this case, the form of the rule gives us
            [beval st b = false] and [st = st'].  But then, since
            [b] and [b'] are equivalent, we have [beval st b' =
            false], and [E_WhileFalse] applies, giving us
            [st =[ while b' do c' end ]=> st'], as required.

          - [E_WhileTrue]: The form of the rule now gives us [beval st
            b = true], with [st =[ c ]=> st'0] and [st'0 =[ while
            b do c end ]=> st'] for some state [st'0], with the
            induction hypothesis [st'0 =[ while b' do c' end ]=>
            st'].

            Since [c] and [c'] are equivalent, we know that [st =[
            c' ]=> st'0].  And since [b] and [b'] are equivalent,
            we have [beval st b' = true].  Now [E_WhileTrue] applies,
            giving us [st =[ while b' do c' end ]=> st'], as
            required.

      - ([<-]) Similar. [] *)

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  (* WORKED IN CLASS *)

  (* We will prove one direction in an "assert"
     in order to reuse it for the converse. *)
  assert (A: forall (b b' : bexp) (c c' : com) (st st' : state),
             bequiv b b' -> cequiv c c' ->
             st =[ while b do c end ]=> st' ->
             st =[ while b' do c' end ]=> st').
  { unfold bequiv,cequiv.
    intros b b' c c' st st' Hbe Hc1e Hce.
    remember <{ while b do c end }> as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite <- Hbe. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite <- Hbe. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity. }

  intros. split.
  - apply A; assumption.
  - apply A.
    + apply sym_bequiv. assumption.
    + apply sym_cequiv. assumption.
Qed.

(** **** Exercise: 3 stars, standard, optional (CSeq_congruence) *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
intros c1 c1' c2 c2'. intros H1 H2.
split; intros H; inversion H; subst;
apply H1 in H4; apply H2 in H7;
apply E_Seq with (st':=st'0); assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (CIf_congruence) *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
Proof.
intros b b' c1 c1' c2 c2'. intros Hb Hc1 Hc2. split; intros H; inversion H; subst.
- rewrite Hb in H5. apply Hc1 in H6. apply E_IfTrue; assumption.
- rewrite Hb in H5. apply Hc2 in H6. apply E_IfFalse; assumption.
- rewrite <- Hb in H5. apply Hc1 in H6. apply E_IfTrue; assumption.
- rewrite <- Hb in H5. apply Hc2 in H6. apply E_IfFalse; assumption.
Qed.
(** [] *)

(** For example, here are two programs and a proof of their
    equivalence using these congruence theorems... *)

Example congruence_example:
  cequiv
    (* Program 1: *)
    <{ X := 0;
       if X = 0 then Y := 0
       else Y := 42 end }>
    (* Program 2: *)
    <{ X := 0;
       if X = 0 then Y := X - X   (* <--- Changed here *)
       else Y := 42 end }>.
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAsgn_congruence. unfold aequiv. simpl.
      symmetry. apply sub_diag.
    + apply refl_cequiv.
Qed.

(** **** Exercise: 3 stars, advanced (not_congr)

    We've shown that the [cequiv] relation is both an equivalence and
    a congruence on commands.  Can you think of a relation on commands
    that is an equivalence but _not_ a congruence?  Write down the
    relation (formally), together with an informal sketch of a proof
    that it is an equivalence and a counterexample showing it is not a
    congruence. *)

(* FILL IN HERE *)
(* Do not modify the following line: *)
Definition manual_grade_for_not_congr : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Program Transformations *)

(** A _program transformation_ is a function that takes a program as
    input and produces a modified program as output.  Compiler
    optimizations such as constant folding are canonical examples,
    but there are many others. *)

(** A program transformation is _sound_ if it preserves the
    behavior of the original program. *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ================================================================= *)
(** ** The Constant-Folding Transformation *)

(** An expression is _constant_ if it contains no variable references.

    Constant folding is an optimization that finds constant
    expressions and replaces them by their values. *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | <{ a1 + a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp <{ (1 + 2) * X }>
  = <{ 3 * X }>.
Proof. reflexivity. Qed.

(** Note that this version of constant folding doesn't do other
    "obvious" things like eliminating trivial additions (e.g.,
    rewriting [0 + X] to just [X]).: we are focusing on a single
    optimization for the sake of simplicity.

    It is not hard to incorporate other ways of simplifying
    expressions -- the definitions and proofs just get longer.  We'll
    consider some in the exercises. *)

Example fold_aexp_ex2 :
  fold_constants_aexp <{ X - ((0 * 6) + Y) }> = <{ X - (0 + Y) }>.
Proof. reflexivity. Qed.

(** Not only can we lift [fold_constants_aexp] to [bexp]s (in the
    [BEq], [BNeq], and [BLe] cases); we can also look for constant
    _boolean_ expressions and evaluate them in-place as well. *)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}>        => <{true}>
  | <{false}>       => <{false}>
  | <{ a1 = a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if negb (n1 =? n2) then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <> a2' }>
      end
  | <{ a1 <= a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end
  | <{ a1 > a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{false}> else <{true}>
      | (a1', a2') =>
          <{ a1' > a2' }>
      end
  | <{ ~ b1 }>  =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }>  =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp <{ true && ~(false && true) }>
  = <{ true }>.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp <{ (X = Y) && (0 = (2 - (1 + 1))) }>
  = <{ (X = Y) && true }>.
Proof. reflexivity. Qed.

(** To fold constants in a command, we simply apply the
    appropriate folding functions on all embedded expressions. *)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }>  =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}>  => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    <{ X := 4 + 5;
       Y := X - 3;
       if (X - Y) = (2 + 4) then skip
       else Y := 0 end;
       if 0 <= (4 - (2 + 1)) then Y := 0
       else skip end;
       while Y = 0 do
         X := X + 1
       end }>
  = (* After constant folding: *)
    <{ X := 9;
       Y := X - 3;
       if (X - Y) = 6 then skip
       else Y := 0 end;
       Y := 0;
       while Y = 0 do
         X := X + 1
       end }>.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Soundness of Constant Folding *)

(** Now we need to show that what we've done is correct. *)

(** Here's the proof for arithmetic expressions: *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (<{ a1 + a2 }>)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(** **** Exercise: 3 stars, standard, optional (fold_bexp_Eq_informal)

    Here is an informal proof of the [BEq] case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the [BLe] case of the formal proof (without looking at the
    [BEq] case, if possible).

   _Theorem_: The constant folding function for booleans,
   [fold_constants_bexp], is sound.

   _Proof_: We must show that [b] is equivalent to [fold_constants_bexp b],
   for all boolean expressions [b].  Proceed by induction on [b].  We
   show just the case where [b] has the form [a1 = a2].

   In this case, we must show

       beval st <{ a1 = a2 }>
     = beval st (fold_constants_bexp <{ a1 = a2 }>).

   There are two cases to consider:

     - First, suppose [fold_constants_aexp a1 = ANum n1] and
       [fold_constants_aexp a2 = ANum n2] for some [n1] and [n2].

       In this case, we have

           fold_constants_bexp <{ a1 = a2 }>
         = if n1 =? n2 then <{true}> else <{false}>

       and

           beval st <{a1 = a2}>
         = (aeval st a1) =? (aeval st a2).

       By the soundness of constant folding for arithmetic
       expressions (Lemma [fold_constants_aexp_sound]), we know

           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1

       and

           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,

       so

           beval st <{a1 = a2}>
         = (aeval a1) =? (aeval a2)
         = n1 =? n2.

       Also, it is easy to see (by considering the cases [n1 = n2] and
       [n1 <> n2] separately) that

           beval st (if n1 =? n2 then <{true}> else <{false}>)
         = if n1 =? n2 then beval st <{true}> else beval st <{false}>
         = if n1 =? n2 then true else false
         = n1 =? n2.

       So

           beval st (<{ a1 = a2 }>)
         = n1 =? n2.
         = beval st (if n1 =? n2 then <{true}> else <{false}>),

       as required.

     - Otherwise, one of [fold_constants_aexp a1] and
       [fold_constants_aexp a2] is not a constant.  In this case, we
       must show

           beval st <{a1 = a2}>
         = beval st (<{ (fold_constants_aexp a1) =
                         (fold_constants_aexp a2) }>),

       which, by the definition of [beval], is the same as showing

           (aeval st a1) =? (aeval st a2)
         = (aeval st (fold_constants_aexp a1)) =?
                   (aeval st (fold_constants_aexp a2)).

       But the soundness of constant folding for arithmetic
       expressions ([fold_constants_aexp_sound]) gives us

         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),

       completing the case.  [] *)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* true and false are immediate *)
    try reflexivity.
  - (* BEq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BNeq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BLe *)
    simpl. rewrite fold_constants_aexp_sound with (a := a1). rewrite fold_constants_aexp_sound with (a := a2). 
    remember (fold_constants_aexp a1) as a1' eqn:Ea1. destruct a1';
    try reflexivity;
    remember (fold_constants_aexp a2) as a2' eqn:Ea2. destruct a2';
    try reflexivity;
    try (solve [destruct (n <=? n0) eqn:EqLe; apply EqLe]).
  - (* BGt, same as BLe*)
    simpl. rewrite fold_constants_aexp_sound with (a := a1). rewrite fold_constants_aexp_sound with (a := a2). 
    remember (fold_constants_aexp a1) as a1' eqn:Ea1. destruct a1';
    try reflexivity;
    remember (fold_constants_aexp a2) as a2' eqn:Ea2. destruct a2';
    simpl;
    try reflexivity;
    try (solve [destruct (n <=? n0); reflexivity]).
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (fold_constants_com_sound)

    Complete the [while] case of the following proof. *)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* skip *) apply refl_cequiv.
  - (* := *) apply CAsgn_congruence.
              apply fold_constants_aexp_sound.
  - (* ; *) apply CSeq_congruence; assumption.
  - (* if *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          [fold_constants_bexp_sound].) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply if_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply if_false; assumption.
  - (* while *)
    assert (bequiv b (fold_constants_bexp b)) as HBfold. { apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Eqb;
    try (apply CWhile_congruence; assumption).
    + intros st st'.
      split.
      * intros Nonterm. exfalso. apply (while_true_nonterm b c st st'); assumption.
      * intros Nonterm. exfalso. apply (while_true_nonterm <{true}> <{skip}> st st').
        -- apply refl_bequiv.
        -- assumption.
    + apply while_false. assumption.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Soundness of (0 + n) Elimination, Redux *)

(** **** Exercise: 4 stars, standard, optional (optimize_0plus_var)

    Recall the definition [optimize_0plus] from the [Imp] chapter
    of _Logical Foundations_:

    Fixpoint optimize_0plus (a:aexp) : aexp :=
      match a with
      | ANum n =>
          ANum n
      | <{ 0 + a2 }> =>
          optimize_0plus a2
      | <{ a1 + a2 }> =>
          <{ (optimize_0plus a1) + (optimize_0plus a2) }>
      | <{ a1 - a2 }> =>
          <{ (optimize_0plus a1) - (optimize_0plus a2) }>
      | <{ a1 * a2 }> =>
          <{ (optimize_0plus a1) * (optimize_0plus a2) }>
      end.

   Note that this function is defined over the old version of [aexp]s,
   without states.

   Write a new version of this function that deals with variables (by
   leaving them alone), plus analogous ones for [bexp]s and commands:

     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com
*)

Fixpoint optimize_0plus_aexp (a : aexp) : aexp :=
  let recurse := optimize_0plus_aexp in
  match a with
  | ANum n =>
      ANum n
  | <{ 0 + a2 }> =>
      recurse a2
  | <{ a1 + a2 }> =>
      <{ (recurse a1) + (recurse a2) }>
  | <{ a1 - a2 }> =>
      <{ (recurse a1) - (recurse a2) }>
  | <{ a1 * a2 }> =>
      <{ (recurse a1) * (recurse a2) }>
  | AId x => AId x
  end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  let recurse := optimize_0plus_bexp in
  let recurse_aexp := optimize_0plus_aexp in
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a b => BEq (recurse_aexp a) (recurse_aexp b)
  | BNeq a b => BNeq (recurse_aexp a) (recurse_aexp b)
  | BLe a b => BLe (recurse_aexp a) (recurse_aexp b)
  | BGt a b => BGt (recurse_aexp a) (recurse_aexp b)
  | BNot b => BNot (recurse b)
  | BAnd a b => BAnd (recurse a) (recurse b)
  end.


Print com.

Fixpoint optimize_0plus_com (c : com) : com :=
  let recurse := optimize_0plus_com in
  let recurse_aexp := optimize_0plus_aexp in
  let recurse_bexp := optimize_0plus_bexp in
  match c with
  | CSkip => CSkip
  | CAsgn x a => CAsgn x (recurse_aexp a)
  | CSeq a b => CSeq (recurse a) (recurse b)
  | CIf cond t f => CIf (recurse_bexp cond) (recurse t) (recurse f)
  | CWhile cond body => CWhile (recurse_bexp cond) (recurse body)
  end.

Example test_optimize_0plus:
    optimize_0plus_com
       <{ while X <> 0 do X := 0 + X - 1 end }>
  =    <{ while X <> 0 do X := X - 1 end }>.
Proof. reflexivity. Qed.

(** Prove that these three functions are sound, as we did for
    [fold_constants_*].  Make sure you use the congruence lemmas in the
    proof of [optimize_0plus_com] -- otherwise it will be _long_! *)

Theorem optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
intros a st. induction a; simpl;
try (reflexivity).
(* APlus*)
- remember (optimize_0plus_aexp a1) as Oa1. destruct a1 eqn:Eqa1;
  try (simpl; rewrite <- IHa2; simpl in IHa1; rewrite IHa1; reflexivity).
  + destruct n; simpl; rewrite IHa2; (try rewrite HeqOa1); reflexivity.
(* AMinus*)
- remember (optimize_0plus_aexp a1) as Oa1. destruct a1 eqn:Eqa1;
  try (simpl; rewrite <- IHa2; simpl in IHa1; rewrite IHa1; reflexivity).
(* AMult *)
- remember (optimize_0plus_aexp a1) as Oa1. destruct a1 eqn:Eqa1;
  try (simpl; rewrite <- IHa2; simpl in IHa1; rewrite IHa1; reflexivity).
Qed.

Theorem optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.  
intros b st. induction b; simpl;
try reflexivity;
(* trivial rewrites of the induction hypotheses *)
try congruence;
(* try trivial outcomes of 0plus' aexp_soundness *)
try (rewrite <- optimize_0plus_aexp_sound; rewrite <- optimize_0plus_aexp_sound; reflexivity).
Qed.

Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
intros c. induction c; intros st st'; simpl.
- reflexivity.
- apply CAsgn_congruence. apply optimize_0plus_aexp_sound.
- apply CSeq_congruence; assumption.
- apply CIf_congruence; (try assumption); apply optimize_0plus_bexp_sound.
- apply CWhile_congruence; [apply optimize_0plus_bexp_sound | assumption].
Qed.

(** Finally, let's define a compound optimizer on commands that first
    folds constants (using [fold_constants_com]) and then eliminates
    [0 + n] terms (using [optimize_0plus_com]). *)

Definition optimizer (c : com) := optimize_0plus_com (fold_constants_com c).

(** Prove that this optimizer is sound. *)

Definition compose {X: Type} (f g: X -> X) := (fun x => f (g x)).  
Lemma ctrans_sound_compose: forall t1 t2, ctrans_sound t1 -> ctrans_sound t2 -> ctrans_sound (compose t1 t2).
Proof.
intros t1 t2 H1 H2. unfold compose. intros c st st'.
unfold ctrans_sound in H1. unfold cequiv in H1.
unfold ctrans_sound in H2. unfold cequiv in H2.
split; simpl; intros H.
- apply -> H1. apply -> H2. assumption.
- apply H1 in H. apply H2 in H. apply H.
Qed.

Theorem optimizer_sound :
  ctrans_sound optimizer.
Proof.
unfold ctrans_sound. unfold optimizer. apply ctrans_sound_compose.
- apply optimize_0plus_com_sound.
- apply fold_constants_com_sound.
Qed.
(** [] *)

(* ################################################################# *)
(** * Proving Inequivalence *)

(** Next, let's look at some programs that are _not_ equivalent. *)

(** Suppose that [c1] is a command of the form

       X := a1; Y := a2

    and [c2] is the command

       X := a1; Y := a2'

    where [a2'] is formed by substituting [a1] for all occurrences
    of [X] in [a2].

    For example, [c1] and [c2] might be:

       c1  =  (X := 42 + 53;
               Y := Y + X)
       c2  =  (X := 42 + 53;
               Y := Y + (42 + 53))

    Clearly, this _particular_ [c1] and [c2] are equivalent.  Is this
    true in general? *)

(** We will see in a moment that it is not, but it is worthwhile
    to pause, now, and see if you can find a counter-example on your
    own. *)

(** More formally, here is the function that substitutes an arithmetic
    expression [u] for each occurrence of a given variable [x] in
    another expression [a]: *)

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId x'       =>
      if String.eqb x x' then u else AId x'
  | <{ a1 + a2 }>  =>
      <{ (subst_aexp x u a1) + (subst_aexp x u a2) }>
  | <{ a1 - a2 }> =>
      <{ (subst_aexp x u a1) - (subst_aexp x u a2) }>
  | <{ a1 * a2 }>  =>
      <{ (subst_aexp x u a1) * (subst_aexp x u a2) }>
  end.

Example subst_aexp_ex :
  subst_aexp X <{42 + 53}> <{Y + X}>
  = <{ Y + (42 + 53)}>.
Proof. simpl. reflexivity. Qed.

(** And here is the property we are interested in, expressing the
    claim that commands [c1] and [c2] as described above are
    always equivalent.  *)

Definition subst_equiv_property : Prop := forall x1 x2 a1 a2,
  cequiv <{ x1 := a1; x2 := a2 }>
         <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.

(** Sadly, the property does _not_ always hold.

    Here is a counterexample:

       X := X + 1; Y := X

    If we perform the substitution, we get

       X := X + 1; Y := X + 1

    which clearly isn't equivalent. *)

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that [subst_equiv_property]
     holds allows us to prove that these two programs are
     equivalent... *)
  remember <{ X := X + 1;
              Y := X }>
      as c1.
  remember <{ X := X + 1;
              Y := X + 1 }>
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).
  clear Contra.

  (* ... allows us to show that the command [c2] can terminate
     in two different final states:
        st1 = (Y !-> 1 ; X !-> 1)
        st2 = (Y !-> 2 ; X !-> 1). *)
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1);
  assert (H2 : empty_st =[ c2 ]=> st2);
  try (subst;
       apply E_Seq with (st' := (X !-> 1));
       apply E_Asgn; reflexivity).
  clear Heqc1 Heqc2.

  apply H in H1.
  clear H.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
  clear H1 H2.

  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. discriminate. Qed.

(** **** Exercise: 4 stars, standard, optional (better_subst_equiv)

    The equivalence we had in mind above was not complete nonsense --
    in fact, it was actually almost right.  To make it correct, we
    just need to exclude the case where the variable [X] occurs in the
    right-hand side of the first assignment statement. *)

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 + a2 }>)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 - a2 }>)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 * a2 }>).

Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
intros x st a ni. induction a; intros NotUsed; inversion NotUsed; subst.
- reflexivity.
- apply t_update_neq. assumption.
- simpl. rewrite (IHa1 H1). rewrite (IHa2 H2). reflexivity.
- simpl. rewrite (IHa1 H1). rewrite (IHa2 H2). reflexivity.
- simpl. rewrite (IHa1 H1). rewrite (IHa2 H2). reflexivity.
Qed.

Lemma APlus_congruence: forall a1 a1' a2 a2', aequiv a1 a1' -> aequiv a2 a2' -> aequiv <{a1 + a2}> <{a1' + a2'}>.
Proof.
intros a1 a1' a2 a2' H1 H2. intros st. simpl. congruence.
Qed.

Lemma AMinus_congruence: forall a1 a1' a2 a2', aequiv a1 a1' -> aequiv a2 a2' -> aequiv <{a1 - a2}> <{a1' - a2'}>.
Proof.
intros a1 a1' a2 a2' H1 H2. intros st. simpl. congruence.
Qed.

Lemma AMul_congruence: forall a1 a1' a2 a2', aequiv a1 a1' -> aequiv a2 a2' -> aequiv <{a1 * a2}> <{a1' * a2'}>.
Proof.
intros a1 a1' a2 a2' H1 H2. intros st. simpl. congruence.
Qed.

Lemma aequiv_weakening: forall x xa a, var_not_used_in_aexp x a -> aequiv a (subst_aexp x xa a).
Proof.
intros x xa a. induction a; intros NotUsed; inversion NotUsed; subst.
- simpl. apply refl_aequiv.
- simpl. (destruct (String.eqb_spec x x0)).
  + exfalso. auto.
  + apply refl_aequiv.
- simpl. apply IHa1 in H1. apply IHa2 in H2. apply APlus_congruence; assumption.
- simpl. apply IHa1 in H1. apply IHa2 in H2. apply AMinus_congruence; assumption.
- simpl. apply IHa1 in H1. apply IHa2 in H2. apply AMul_congruence; assumption.
Qed.

Lemma aeval_subst_same: forall x v a st, var_not_used_in_aexp x v -> aeval (x !-> aeval st v; st) (subst_aexp x v a) = aeval (x !-> aeval st v; st) a.
Proof.
intros x v a. induction a; intros st; intros NotUsed; simpl.
- reflexivity.
- destruct (String.eqb_spec x x0).
  + subst. rewrite aeval_weakening.
    * rewrite t_update_eq. reflexivity.
    * assumption.
  + reflexivity.
- rewrite IHa1; (try assumption). rewrite IHa2; (try assumption). reflexivity.
- rewrite IHa1; (try assumption). rewrite IHa2; (try assumption). reflexivity.
- rewrite IHa1; (try assumption). rewrite IHa2; (try assumption). reflexivity.
Qed.

(** Using [var_not_used_in_aexp], formalize and prove a correct version
    of [subst_equiv_property]. *)

Theorem subst_equiv_property_correct : forall x1 x2 a1 a2,
  var_not_used_in_aexp x1 a1 ->
  cequiv <{ x1 := a1; x2 := a2 }>
         <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.
Proof.
intros x1 x2. intros a1. induction a2; intros NotUsed; simpl.
- apply refl_cequiv.
- destruct (String.eqb_spec x1 x).
  + subst. intros st st'. split; intros H; inversion H; subst; eapply E_Seq;
    try apply H2;
    try (inversion H2; inversion H5; subst; simpl; apply E_Asgn; simpl; rewrite t_update_eq; rewrite aeval_weakening);
    try reflexivity;
    try assumption.
  + apply refl_cequiv.

(* The three binary cases have the same proof *)
- intros st st'. split; intros H; inversion H; subst;
  eapply E_Seq; 
  try apply H2;
  try (
    inversion H2; inversion H5; subst; simpl; apply E_Asgn; 
    simpl; 
    rewrite aeval_subst_same; (try assumption);
    rewrite aeval_subst_same; (try assumption);
    reflexivity
  ).


- intros st st'. split; intros H; inversion H; subst;
  eapply E_Seq; 
  try apply H2;
  try (
    inversion H2; inversion H5; subst; simpl; apply E_Asgn; 
    simpl; 
    rewrite aeval_subst_same; (try assumption);
    rewrite aeval_subst_same; (try assumption);
    reflexivity
  ).

- intros st st'. split; intros H; inversion H; subst;
  eapply E_Seq; 
  try apply H2;
  try (
    inversion H2; inversion H5; subst; simpl; apply E_Asgn; 
    simpl; 
    rewrite aeval_subst_same; (try assumption);
    rewrite aeval_subst_same; (try assumption);
    reflexivity
).
Qed.

(** **** Exercise: 3 stars, standard (inequiv_exercise)

    Prove that an infinite loop is not equivalent to [skip] *)

Theorem inequiv_exercise:
  ~ cequiv <{ while true do skip end }> <{ skip }>.
Proof.
unfold not. intros H. unfold cequiv in H. specialize H with empty_st empty_st. destruct H as [_ HR].
apply (while_true_nonterm BTrue CSkip empty_st empty_st).
- apply refl_bequiv.
- apply HR. apply E_Skip.
Qed.
(** [] *)

(* ################################################################# *)
(** * Extended Exercise: Nondeterministic Imp *)

(** As we have seen (in theorem [ceval_deterministic] in the [Imp]
    chapter), Imp's evaluation relation is deterministic.  However,
    _non_-determinism is an important part of the definition of many
    real programming languages. For example, in many imperative
    languages (such as C and its relatives), the order in which
    function arguments are evaluated is unspecified: the program
    fragment

      x = 0;
      f(++x, x)

    might call [f] with arguments [(1, 0)] or [(1, 1)], depending how
    the compiler chooses to order things.  This can be a little
    confusing for programmers, but it gives compiler writers useful
    freedom.

    In this exercise, we will extend Imp with a simple
    nondeterministic command and study how this change affects
    program equivalence.  The new command has the syntax [HAVOC X],
    where [X] is an identifier. The effect of executing [HAVOC X] is
    to assign an _arbitrary_ number to the variable [X],
    nondeterministically. For example, after executing the program:

      HAVOC Y;
      Z := Y * 2

    the value of [Y] can be any number, while the value of [Z] is
    twice that of [Y] (so [Z] is always even). Note that we are not
    saying anything about the _probabilities_ of the outcomes -- just
    that there are (infinitely) many different outcomes that can
    possibly happen after executing this nondeterministic code.

    In a sense, a variable on which we do [HAVOC] roughly corresponds
    to an uninitialized variable in a low-level language like C.  After
    the [HAVOC], the variable holds a fixed but arbitrary number.  Most
    sources of nondeterminism in language definitions are there
    precisely because programmers don't care which choice is made (and
    so it is good to leave it open to the compiler to choose whichever
    will run faster).

    We call this new language _Himp_ ("Imp extended with [HAVOC]"). *)

Module Himp.

(** To formalize Himp, we first add a clause to the definition of
    commands. *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.                (* <--- NEW *)

Notation "'havoc' l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).
Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99,
    format "'[v' 'while'  x  'do' '/  ' y '/' 'end' ']'") : com_scope.

(** **** Exercise: 2 stars, standard (himp_ceval)

    Now, we must extend the operational semantics. We have provided
   a template for the [ceval] relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of [ceval]
   to formalize the behavior of the [HAVOC] command? *)

Reserved Notation
         "st0 '=[' c ']=>' st1"
         (at level 40, c custom com at level 99,
          st0 constr, st1 constr at next level,
          format "'[hv' st0  =[ '/  ' '[' c ']' '/' ]=>  st1 ']'").

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_Havoc : forall st n x,
    st =[ havoc x ]=> (x !-> n; st)
  where "st =[ c ]=> st'" := (ceval c st st').

(** As a sanity check, the following claims should be provable for
    your definition: *)

Example havoc_example1 : empty_st =[ havoc X ]=> (X !-> 0).
Proof. apply E_Havoc. Qed.

Example havoc_example2 :
  empty_st =[ skip; havoc Z ]=> (Z !-> 42).
Proof. eapply E_Seq. apply E_Skip. apply E_Havoc. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_Check_rule_for_HAVOC : option (nat*string) := None.
(** [] *)

(** Finally, we repeat the definition of command equivalence from above: *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

(** Let's apply this definition to prove some nondeterministic
    programs equivalent / inequivalent. *)

(** **** Exercise: 3 stars, standard (havoc_swap)

    Are the following two programs equivalent? *)

Definition pXY :=
  <{ havoc X ; havoc Y }>.

Definition pYX :=
  <{ havoc Y; havoc X }>.

(** If you think they are equivalent, prove it. If you think they are
    not, prove that. *)

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof.
  (* Hint: You may want to use [t_update_permute] at some point,
     in which case you'll probably be left with [X <> Y] as a
     hypothesis. You can use [discriminate] to discharge this. *)
left. unfold pYX. unfold pXY. intros st st'. split; intros H; inversion H; subst;
  inversion H2; inversion H5; subst; rewrite t_update_permute;
  try (intros_absurd);
  eapply E_Seq;
  try (apply (E_Havoc _ n0 _));
  try (apply E_Havoc).
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (havoc_copy)

    Are the following two programs equivalent? *)

Definition ptwice :=
  <{ havoc X; havoc Y }>.

Definition pcopy :=
  <{ havoc X; Y := X }>.

(** If you think they are equivalent, then prove it. If you think they
    are not, then prove that.  (Hint: You may find the [assert] tactic
    useful.) *)

Lemma st_eq: forall (st st': total_map nat) x, st = st' -> st x = st' x. 
Proof.
intros. rewrite H. reflexivity.
Qed.

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof.
(* pcopy will always assign the same value (albeit among an infinity of possible values) to X and Y,
   whereas ptwice can assign two different values
   Havoc lets us pick any value to build a counter example,
   any two different values can do, here we choose (admittedly boringly) 1 and 2
*)
right. unfold not. unfold cequiv. intros H. specialize H with empty_st (Y !-> 2; X !-> 1).
assert (empty_st =[ ptwice ]=> (Y !-> 2; X !-> 1)) as H'.
{ eapply E_Seq. apply E_Havoc. apply E_Havoc. }
apply H in H'. unfold pcopy in H'. inversion H'. subst. inversion H2. inversion H5. subst. simpl in H9.
rewrite t_update_eq in H9.

assert (n = 1) as N1.
{ apply st_eq with (x := X) in H9. rewrite t_update_neq in H9. rewrite t_update_neq with (x1 := Y) in H9.
  - rewrite t_update_eq in H9. rewrite t_update_eq in H9. apply H9.
  - intros_absurd.
  - intros_absurd.
}
assert (n = 2) as N2.
{ apply st_eq with (x := Y) in H9. rewrite t_update_eq in H9. rewrite t_update_eq in H9. apply H9. }
rewrite N1 in N2. discriminate N2.

Qed.
(** [] *)

(** The definition of program equivalence we are using here has some
    subtle consequences on programs that may loop forever.  What
    [cequiv] says is that the set of possible _terminating_ outcomes
    of two equivalent programs is the same. However, in a language
    with nondeterminism, like Himp, some programs always terminate,
    some programs always diverge, and some programs can
    nondeterministically terminate in some runs and diverge in
    others. The final part of the following exercise illustrates this
    phenomenon.
*)

(** **** Exercise: 4 stars, advanced (p1_p2_term)

    Consider the following commands: *)

Definition p1 : com :=
  <{ while ~ (X = 0) do
       havoc Y;
       X := X + 1
     end }>.

Definition p2 : com :=
  <{ while ~ (X = 0) do
       skip
     end }>.

(** Intuitively, [p1] and [p2] have the same termination behavior:
    either they loop forever, or they terminate in the same state they
    started in.  We can capture the termination behavior of [p1] and
    [p2] individually with these lemmas: *)

Lemma p1_body_increases_x: forall st st', st =[ havoc Y; X := X + 1]=> st' -> st' X <> 0.
Proof.
intros st st' H. inversion H. subst. inversion H2. inversion H5. subst.
rewrite t_update_eq. simpl. rewrite t_update_neq.
{ destruct (st X); intros_absurd. }
{ intros_absurd. }
Qed.

Lemma p2_body_leaves_x: forall st st', st X <> 0 -> st =[ skip ]=> st' -> st' X <> 0.
Proof.
intros st st' HX H. inversion H. subst. assumption.
Qed.

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p1 ]=> st'.
Proof.
intros st st' HX.
intros H. remember p1 as P1 eqn: EqP1. induction H;
 try (discriminate EqP1).
 - inversion EqP1. subst. inversion H. apply negb_false_iff in H1. destruct (Nat.eqb_spec (st X) 0) as [HX' | HX'].
   + apply (HX HX').
   + discriminate H1.
 - inversion EqP1. subst. apply IHceval2.
   * apply p1_body_increases_x with (st := st). assumption.
   * assumption.
Qed.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p2 ]=> st'.
Proof.
intros st st' HX H. remember p2 as P2 eqn:EqP2. induction H;
(try discriminate EqP2).
- inversion EqP2. subst. simpl in H. destruct (Nat.eqb_spec (st X) 0) as [HX' | HX'].
  + apply (HX HX').
  + discriminate H.
- inversion EqP2. subst. apply IHceval2.
  + apply p2_body_leaves_x with (st := st); assumption.
  + assumption.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (p1_p2_equiv)

    Use these two lemmas to prove that [p1] and [p2] are actually
    equivalent. *)

Theorem p1_p2_equiv : cequiv p1 p2.
Proof.
intros st st'. 
destruct (Nat.eqb_spec (st X) 0) as [HX | HX]; split; intros H; inversion H; subst;
(* Trivial cases where X := 0 and both programs exit their loop immediatly *)
try( unfold p1; apply E_WhileFalse; assumption);
try( unfold p2; apply E_WhileFalse; assumption);

(* Trivial contradictory cases where the st X = 0 equality is the opposite of the inversion hypothesis *)
try (inversion H2; rewrite HX in H1; simpl in H1; discriminate H1).

(* Remaining cases deduced directly from the above lemmas *)
- exfalso. apply p1_may_diverge in H.
  + apply H.
  + assumption.
- exfalso. apply p2_may_diverge in H.
  + apply H.
  + assumption.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (p3_p4_inequiv)

    Prove that the following programs are _not_ equivalent.  (Hint:
    What should the value of [Z] be when [p3] terminates?  What about
    [p4]?) *)

Definition p3 : com :=
  <{ Z := 1;
     while X <> 0 do
       havoc X;
       havoc Z
     end }>.

Definition p4 : com :=
  <{ X := 0;
     Z := 1 }>.

Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof.

(* p4 always assign 0 and 1 to X and Z then terminates,
   whereas p3, when terminating after executing the loop at least once, can assign an arbitrary value to Z.
   We build a counter example where Z := 2 / 1 in p3 / p4.
   We must start from a state where X <> 0 to enter the p3 loop at least once.
*)
Definition st_X1 := ( X!-> 1).

unfold cequiv. intros H. specialize H with st_X1 (Z !-> 2; X !-> 0; Z !-> 1; st_X1).
destruct H as [HL HR]. 
assert (st_X1 =[ p4 ]=> (Z !-> 2; X !-> 0; Z !-> 1; st_X1)) as Contra.
{
  apply HL. eapply E_Seq.
  - apply E_Asgn with (n:=1). reflexivity.
  - eapply E_WhileTrue.
    + reflexivity.
    + eapply E_Seq.
      * apply E_Havoc with (n := 0).
      * apply E_Havoc with (n := 2).
    + apply E_WhileFalse. reflexivity.
}
inversion Contra. subst. inversion H1. inversion H4. subst. simpl in H10.
remember (Z !-> 1; X !-> 0; st_X1) as Z1.
remember (Z !-> 2; X !-> 0; Z !-> 1; st_X1) as Z2.
assert (Z1 Z = Z2 Z) as ContraZ. { rewrite H10. reflexivity. }
rewrite HeqZ1 in ContraZ. rewrite HeqZ2 in ContraZ.
rewrite t_update_eq in ContraZ. rewrite t_update_eq in ContraZ.
discriminate ContraZ.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (p5_p6_equiv)

    Prove that the following commands are equivalent.  (Hint: As
    mentioned above, our definition of [cequiv] for Himp only takes
    into account the sets of possible terminating configurations: two
    programs are equivalent if and only if the set of possible terminating
    states is the same for both programs when given a same starting state
    [st].  If [p5] terminates, what should the final state be? Conversely,
    is it always possible to make [p5] terminate?) *)

Definition p5 : com :=
  <{ while X <> 1 do
       havoc X
     end }>.

Definition p6 : com :=
  <{ X := 1 }>.

Theorem p5_p6_equiv : cequiv p5 p6.
Proof.
unfold cequiv. intros st st'. split; intros H.
- remember p5 as P5 eqn:HP5. induction H; subst;
  try (discriminate HP5). 
  + inversion HP5. subst. inversion H. 
    apply negb_neg in H1. simpl in H1. apply Nat.eqb_eq in H1.
    assert (st =[ p6 ]=> (X !-> 1; st)) as HSame. { apply E_Asgn. reflexivity. } 
    rewrite <- H1 in HSame. rewrite t_update_same in HSame. apply HSame.
  + inversion HP5. subst. inversion H0. subst. 
    apply IHceval2 in HP5. inversion HP5. subst.
    rewrite t_update_shadow. simpl. apply E_Asgn. reflexivity.
- inversion H. subst. simpl in *.
  (* Split the proof between wether X = 1 or not in the initial state *)
  destruct (Nat.eqb_spec (st X) 1) as [X1 | X1].
  + rewrite <- t_update_same with (m := st) (x := X) at 1. rewrite X1.
    apply E_WhileFalse.
    reflexivity.
  + apply E_WhileTrue with (st' := (X !-> 1; st)).
    * simpl. apply Nat.eqb_neq in X1. rewrite X1. reflexivity.
    * apply E_Havoc.
    * apply E_WhileFalse. reflexivity.
Qed.
(** [] *)

End Himp.

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, optional (swap_noninterfering_assignments)

    (Hint: You may or may not -- depending how you approach it -- need
    to use [functional_extensionality] explicitly for this one.) *)

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    <{ l1 := a1; l2 := a2 }>
    <{ l2 := a2; l1 := a1 }>.
Proof.
intros l1 l2 a1 a2.
intros H12.
intros HLA12 HLA21.
intros st st'. split; intros H.
(* `t_update_permute` is the key lemma for this one *)
- inversion H. subst. inversion H2. subst. inversion H5. subst.
  rewrite (aeval_weakening); try assumption.
  rewrite t_update_permute; try congruence.
  eapply E_Seq.
  + apply E_Asgn. reflexivity.
  + apply E_Asgn. rewrite aeval_weakening; try assumption. reflexivity.
(* Exact same proof for the other side *)
- inversion H. subst. inversion H2. subst. inversion H5. subst.
  rewrite (aeval_weakening); try assumption.
  rewrite t_update_permute; try congruence.
  eapply E_Seq.
  + apply E_Asgn. reflexivity.
  + apply E_Asgn. rewrite aeval_weakening; try assumption. reflexivity. 
Qed.

(** [] *)

(** **** Exercise: 4 stars, standard, optional (for_while_equiv)

    This exercise extends the optional [add_for_loop] exercise from
    the [Imp] chapter, where you were asked to extend the language
    of commands with C-style [for] loops.  Prove that the command:

      for (c1; b; c2) {
          c3
      }

    is equivalent to:

       c1;
       while b do
         c3;
         c2
       end
*)

Module ForLoop.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CFor (init: com) (test: bexp) (incr: com) (body: com).

Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99,
    format "'[v' 'while'  x  'do' '/  ' y '/' 'end' ']'") : com_scope.
Notation "'for' init ',' test ',' incr 'do' body 'end'" := (CFor init test incr body)
  (in custom com at level 89, init at level 99, test at level 99,
  format "'[v' 'for'  init ',' test ',' incr  'do' '/  ' body '/' 'end' ']'") : com_scope.

Reserved Notation
         "st0 '=[' c ']=>' st1"
         (at level 40, c custom com at level 99,
          st0 constr, st1 constr at next level,
          format "'[hv' st0  =[ '/  ' '[' c ']' '/' ]=>  st1 ']'").

Example for_notation :
<{ for (X := 0), (X <= 2), (X := X + 1) do Y := Y + 1 end }> =
  CFor (CAsgn "X" (ANum 0)) 
       (BLe (AId "X") (ANum 2)) 
       (CAsgn "X" (APlus (AId "X") (ANum 1))) 
       (CAsgn "Y" (APlus (AId "Y") (ANum 1))).
Proof. reflexivity. Qed.

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  (* This is almost too easy for this exercise since I already defined the for loop in terms of a while,
     but hey I'll consider it fair game
  *)
  | E_ForLoop : forall st st' st'' init test incr body,
    st =[ init ]=> st' ->
    st' =[ while test do body; incr end ]=> st'' ->
    st =[ for init, test, incr do body end]=> st''
  where "st =[ c ]=> st'" := (ceval c st st').

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

Theorem for_equiv_while: forall init cond incr body, cequiv 
<{ init; while cond do body; incr end  }>
<{ for (init), (cond), (incr) do body end  }>.
Proof.
(* Eeverything just falls from the definition of E_ForLoop *)
intros init cond incr body. intros st st'. split ;intros H; inversion H; subst.
- eapply E_ForLoop.
  + apply H2.
  + apply H5.
- eapply E_Seq.
  + apply H6.
  + apply H7.
Qed.
End ForLoop.

(** **** Exercise: 4 stars, advanced, optional (capprox)

    In this exercise we define an asymmetric variant of program
    equivalence we call _program approximation_. We say that a
    program [c1] _approximates_ a program [c2] when, for each of
    the initial states for which [c1] terminates, [c2] also terminates
    and produces the same final state. Formally, program approximation
    is defined as follows: *)

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  st =[ c1 ]=> st' -> st =[ c2 ]=> st'.

(** For example, the program

  c1 = while X <> 1 do
         X := X - 1
       end

    approximates [c2 = X := 1], but [c2] does not approximate [c1]
    since [c1] does not terminate when [X = 0] but [c2] does.  If two
    programs approximate each other in both directions, then they are
    equivalent. *)

(** Find two programs [c3] and [c4] such that neither approximates
    the other. *)

Definition c3 : com := <{ X := 3 }>.
Definition c4 : com := <{ X := 4 }>.

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.
Proof.
split; unfold capprox; intros H.
- specialize H with empty_st (X !-> 3).
  assert (empty_st =[ c3 ]=> (X !-> 3)) as C3. { apply E_Asgn. reflexivity. }
  apply H in C3. inversion C3. subst. simpl in H4. apply (st_eq_absurd X 4 3). { intros_absurd. } { assumption. }
- specialize H with empty_st (X !-> 4).
  assert (empty_st =[ c4 ]=> (X !-> 4)) as C4. { apply E_Asgn. reflexivity. }
  apply H in C4. inversion C4. subst. simpl in H4. apply (st_eq_absurd X 3 4). { intros_absurd. } { assumption. }
Qed.

(** Find a program [cmin] that approximates every other program. *)

Definition cmin := <{ while true do skip end }>.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof.
intros c. unfold capprox. unfold cmin. intros st st' H. exfalso. apply (while_true_nonterm BTrue CSkip st st').
- apply refl_bequiv.
- apply H.
Qed.

(** Finally, find a non-trivial property which is preserved by
    program approximation (when going from left to right). *)

(* First attempt: 
'c does not modify X'
this is not preserved since a non-terminating program can approximate a terminating one,
thus 'while true skip' approximates 'X := 1', falsifying the property *)
Definition zprop_first_attempt (c : com) : Prop := forall st st', st =[ c ]=> st' -> st X = st' X.

(* c terminates *)
Definition zprop (c : com) : Prop := forall st, exists st', st =[ c ]=> st'.

(* If c always terminates and c approximates c' then c' terminates *)
Theorem zprop_preserving : forall c c',
  zprop c -> capprox c c' -> zprop c'.
Proof.
intros c c' Z C. unfold zprop in *. unfold capprox in *.
intros st. specialize Z with st. inversion Z as [st' HZ]. apply C in HZ.
exists st'. apply HZ.
Qed.
(** [] *)

(* 2026-08-24 09:57 *)
