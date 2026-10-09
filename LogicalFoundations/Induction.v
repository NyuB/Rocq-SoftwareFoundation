(** * Induction: Proof by Induction *)

(* ################################################################# *)
(** * Separate Compilation *)

(** Before getting started on this chapter, we need to import
    all of our definitions from the previous chapter: *)

From LF Require Export Basics.

(** For this [Require] command to work, Rocq needs to be able to
    find a compiled version of the previous chapter ([Basics.v]).
    This compiled version, called [Basics.vo], is analogous to the
    [.class] files compiled from [.java] source files and the [.o]
    files compiled from [.c] files.

    To compile [Basics.v] and obtain [Basics.vo], first make sure that
    the files [Basics.v], [Induction.v], and [_CoqProject] are in
    the current directory.

    The [_CoqProject] file should contain just the following line:

      -Q . LF

    This maps the current directory ("[.]", which contains [Basics.v],
    [Induction.v], etc.) to the prefix (or "logical directory")
    "[LF]". Proof General, CoqIDE, and VSCoq read [_CoqProject]
    automatically, to find out to where to look for the file
    [Basics.vo] corresponding to the library [LF.Basics].

    Once the files are in place, there are various ways to build
    [Basics.vo] from an IDE, or you can build it from the command
    line.  From an IDE...

     - In Proof General: The compilation can be made to happen
       automatically when you submit the [Require] line above to PG, by
       setting the emacs variable [coq-compile-before-require] to [t].
       This can also be found in the menu: "Coq" > "Auto Compilation" >
       "Compile Before Require".

     - In CoqIDE: One thing you can do on all platforms is open
       [Basics.v]; then, in the "Compile" menu, click on "Compile Buffer".

     - For VSCode users, open the terminal pane at the bottom and then
       follow the command line instructions below.  (If you downloaded
       the project setup .tgz file, just doing `make` should build all
       the code.)

    To compile [Basics.v] from the command line...

     - First, generate a [Makefile] using the [rocq makefile] utility,
       which comes installed with Rocq. (If you obtained the whole volume as
       a single archive, a [Makefile] should already exist and you can
       skip this step.)

         rocq makefile -f _CoqProject *.v -o Makefile

       You should rerun that command whenever you add or remove
       Rocq files in this directory.

     - Now you can compile [Basics.v] by running [make] with the
       corresponding [.vo] file as a target:

         make Basics.vo

       All files in the directory can be compiled by giving no
       arguments:

         make

     - Under the hood, [make] uses the Rocq compiler, [rocq compile].  You can
       also run [rocq compile] directly:

         rocq compile -Q . LF Basics.v

     - Since [make] also calculates dependencies between source files
       to compile them in the right order, [make] should generally be
       preferred over running [rocq compile] explicitly.  But as a last (but
       not terrible) resort, you can simply compile each file manually
       as you go.  For example, before starting work on the present
       chapter, you would need to run the following command:

        rocq compile -Q . LF Basics.v

       Then, once you've finished this chapter, you'd do

        rocq compile -Q . LF Induction.v

       to get ready to work on the next one.  If you ever remove the
       .vo files, you'd need to give both commands again (in that
       order).

    Troubleshooting:

     - For many of the alternatives above you need to make sure that
       the [rocq] executable is in your [PATH].

     - If you get complaints about missing identifiers, it may be
       because the "load path" for Rocq is not set up correctly.  The
       [Print LoadPath.] command may be helpful in sorting out such
       issues.

     - When trying to compile a later chapter, if you see a message like

        Compiled library Induction makes inconsistent assumptions over
        library Basics

       a common reason is that the library [Basics] was modified and
       recompiled without also recompiling [Induction] which depends
       on it.  Recompile [Induction], or everything if too many files
       are affected (for instance by running [make] and if even this
       doesn't work then [make clean; make]).

     - If you get complaints about missing identifiers later in this
       file it may be because the "load path" for Rocq is not set up
       correctly.  The [Print LoadPath.] command may be helpful in
       sorting out such issues.

       In particular, if you see a message like

           Compiled library Foo makes inconsistent assumptions over
           library Bar

       check whether you have multiple installations of Rocq on your
       machine.  It may be that commands (like [rocq compile]) that you execute
       in a terminal window are getting a different version of Rocq than
       commands executed by Proof General or CoqIDE.

     - One more tip for CoqIDE users: If you see messages like [Error:
       Unable to locate library Basics], a likely reason is
       inconsistencies between compiling things _within CoqIDE_ vs _using
       [rocq] from the command line_.  This typically happens when there
       are two incompatible versions of Rocq installed on your
       system (one associated with CoqIDE, and one associated with [rocq]
       from the terminal).  The workaround for this situation is
       compiling using CoqIDE only (i.e. choosing "make" from the menu),
       and avoiding using [rocq] directly at all. *)

(* ################################################################# *)
(** * Proof by Induction *)

(** We can prove that [0] is a neutral element for [+] on the _left_
    using just [reflexivity].  But the proof that it is also a neutral
    element on the _right_ ... *)

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ... can't be done in the same simple way.  Just applying
  [reflexivity] doesn't work, since the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(** And reasoning by cases using [destruct n] doesn't get us much
    further: the branch of the case analysis where we assume [n = 0]
    goes through just fine, but in the branch where [n = S n'] for
    some [n'] we get stuck in exactly the same way. *)

Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* ...but here we are stuck again *)
Abort.

(** We could use [destruct n'] to get a bit further, but,
    since [n] can be arbitrarily large, we'll never get all the way
    there if we just go on like this. *)

(** To prove interesting facts about numbers, lists, and other
    inductively defined sets, we often need a more powerful reasoning
    principle: _induction_.

    Recall (from a discrete math course, probably) the _principle of
    induction over natural numbers_: If [P(n)] is some proposition
    involving a natural number [n] and we want to show that [P] holds for
    all numbers [n], we can reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Rocq, the steps are the same, except we typically encounter them
    in reverse order: we begin with the goal of proving [P(n)] for all
    [n] and apply the [induction] tactic to break it down into two
    separate subgoals: one where we must show [P(O)] and another where
    we must show [P(n') -> P(S n')].  Here's how this works for the
    theorem at hand... *)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  Since there are two subgoals, the [as...] clause
    has two parts, separated by a vertical bar, [|].  (Strictly
    speaking, we can omit the [as...] clause and Rocq will choose names
    for us.  In practice, this is a bad practice, as Rocq's automatic
    choices tend to be confusing.)

    In the first subgoal, [n] is replaced by [0].  No new variables
    are introduced (so the first part of the [as...] is empty), and
    the goal becomes [0 = 0 + 0], which follows easily by simplification.

    In the second subgoal, [n] is replaced by [S n'], and the
    assumption [n' + 0 = n'] is added to the context with the name
    [IHn'] (i.e., the Induction Hypothesis for [n']).  These two names
    are specified in the second part of the [as...] clause.  The goal
    in this case becomes [S n' = (S n') + 0], which simplifies to
    [S n' = S (n' + 0)], which in turn follows from [IHn']. *)

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** (The use of the [intros] tactic in these proofs is actually
    redundant.  When applied to a goal that contains quantified
    variables, the [induction] tactic will automatically move them
    into the context as needed.) *)

(** **** Exercise: 2 stars, standard, especially useful (basic_induction)

    Prove the following using induction. You might need previously
    proven results. *)

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
induction n as [|n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
induction n as [|n' IHn'].
- intros m. reflexivity.
- intros m. simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
induction n as [|n' IHn'].
- intros m. rewrite -> add_0_r. reflexivity.
- intros m. simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
induction n as [|n' IHn'].
- intros m p. reflexivity.
- intros m p. simpl. rewrite -> IHn'. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (double_plus)

    Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
induction n as [|n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (eqb_refl)

    The following theorem relates the computational equality [=?] on
    [nat] with the definitional equality [=] on [bool]. *)

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
induction n as [|n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (even_S)

    One inconvenient aspect of our definition of [even n] is the
    recursive call on [n - 2]. This makes proofs about [even n]
    harder when done by induction on [n], since we may need an
    induction hypothesis about [n - 2]. The following lemma gives an
    alternative characterization of [even (S n)] that works better
    with induction: *)

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
induction n as [|n' IHn].
- reflexivity.
- rewrite -> IHn. rewrite -> negb_involutive. reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Proofs Within Proofs *)

(** In Rocq, as in informal mathematics, large proofs are often
    broken into a sequence of theorems, with later proofs referring to
    earlier theorems.  But sometimes a proof will involve some
    miscellaneous fact that is too trivial and of too little general
    interest to bother giving it its own top-level name.  In such
    cases, it is convenient to be able to simply use the required fact
    "in place" and then prove it as a separate step.  The [replace]
    tactic allows us to do this. *)

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  replace (n + 0 + 0) with n.
  - reflexivity.
  - rewrite add_comm. simpl. rewrite add_comm. reflexivity.
Qed.

(** The tactic [replace e1 with e2] tactic introduces two subgoals.

    The first subgoal is the same as the one at the point where we
    invoke [replace], except that [e1] is replaced by [e2].  The
    second subgoal is the equality [e1 = e2] itself.  *)

(** As another example, suppose we want to prove that [(n + m)
    + (p + q) = (m + n) + (p + q)]. The only difference between the
    two sides of the [=] is that the arguments [m] and [n] to the
    first inner [+] are swapped, so it seems we should be able to use
    the commutativity of addition ([add_comm]) to rewrite one into the
    other.  However, the [rewrite] tactic is not very smart about
    _where_ it applies the rewrite.  There are three uses of [+] here,
    and it turns out that doing [rewrite -> add_comm] will affect only
    the _outer_ one... *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
    like add_comm should do the trick! *)
  rewrite add_comm.
  (* Doesn't work... Rocq rewrites the wrong plus! :-( *)
Abort.

(** To use [add_comm] at the point where we need it, we can rewrite
    [n + m] to [m + n] using [replace] and then prove [n + m = m + n]
    using [add_comm]. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite add_comm. reflexivity.
Qed.

(* ################################################################# *)
(** * Formal vs. Informal Proof *)

(** "Informal proofs are algorithms; formal proofs are code." *)

(** What constitutes a successful proof of a mathematical claim?

    The question has challenged philosophers for millennia, but a
    rough and ready answer could be this: A proof of a mathematical
    proposition [P] is a written (or spoken) text that instills in the
    reader or hearer the certainty that [P] is true -- an unassailable
    argument for the truth of [P].  That is, a proof is an act of
    communication.

    Acts of communication may involve different sorts of readers.  On
    one hand, the "reader" can be a program like Rocq, in which case
    the "belief" that is instilled is that [P] can be mechanically
    derived from a certain set of formal logical rules, and the proof
    is a recipe that guides the program in checking this fact.  Such
    recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will probably be written in English or some other natural
    language and will thus necessarily be _informal_.  Here, the
    criteria for success are less clearly specified.  A "valid" proof
    is one that makes the reader believe [P].  But the same proof may
    be read by many different readers, some of whom may be convinced
    by a particular way of phrasing the argument, while others may not
    be. Some readers may be particularly pedantic, inexperienced, or
    just plain thick-headed; the only way to convince them will be to
    make the argument in painstaking detail.  Other readers, more
    familiar in the area, may find all this detail so overwhelming
    that they lose the overall thread; all they want is to be told the
    main ideas, since it is easier for them to fill in the details for
    themselves than to wade through a written presentation of them.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that will convince every
    conceivable reader.

    In practice, however, mathematicians have developed a rich set of
    conventions and idioms for writing about complex mathematical
    objects that -- at least within a certain community -- make
    communication fairly reliable.  The conventions of this stylized
    form of communication give a reasonably clear standard for judging
    proofs good or bad.

    Because we are using Rocq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can
    completely forget about informal ones!  Formal proofs are useful
    in many ways, but they are _not_ very efficient ways of
    communicating ideas between human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity.  Qed.

(** Rocq is perfectly happy with this.  For a human, however, it
    is difficult to make much sense of it.  We can use comments and
    bullets to show the structure a little more clearly... *)

Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity.   Qed.

(** ... and if you're used to Rocq you might be able to step
    through the tactics one after the other in your mind and imagine
    the state of the context and goal stack at each point, but if the
    proof were even a little bit more complicated this would be next
    to impossible.

    A (pedantic) mathematician might write the proof something like
    this: *)

(** - _Theorem_: For any [n], [m] and [p],

      n + (m + p) = (n + m) + p.

    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show that

        0 + (m + p) = (0 + m) + p.

      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where

        n' + (m + p) = (n' + m) + p.

      We must now show that

        (S n') + (m + p) = ((S n') + m) + p.

      By the definition of [+], this follows from

        S (n' + (m + p)) = S ((n' + m) + p),

      which is immediate from the induction hypothesis.  _Qed_. *)

(** The overall form of the proof is basically similar, and of
    course this is no accident: Rocq has been designed so that its
    [induction] tactic generates the same sub-goals, in the same
    order, as the bullet points that a mathematician would usually
    write.  But there are significant differences of detail: the
    formal proof is much more explicit in some ways (e.g., the use of
    [reflexivity]) but much less explicit in others (in particular,
    the "proof state" at any given point in the Rocq proof is
    completely implicit, whereas the informal proof reminds the reader
    several times where things stand). *)

(** **** Exercise: 2 stars, advanced, optional (add_comm_informal)

    Translate your solution for [add_comm] into an informal proof:

    Theorem: Addition is commutative.

    Proof: (* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_add_comm_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (eqb_refl_informal)

    Write an informal proof of the following theorem, using the
    informal proof of [add_assoc] as a model.  Don't just
    paraphrase the Rocq tactics into English!

    Theorem: [(n =? n) = true] for any [n].

    Proof: (* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_eqb_refl_informal : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * More Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (mul_comm)

    Use [replace] to help prove [add_shuffle3].  You don't need to
    use induction yet. *)

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros n m p. rewrite add_assoc. rewrite add_assoc. replace (n+m) with (m+n).
 - reflexivity.
 - rewrite add_comm. reflexivity. 
Qed.



(** Now prove commutativity of multiplication.  You will probably want
    to look for (or define and prove) a "helper" theorem to be used in
    the proof of this one. Hint: what is [n * (1 + k)]? *)

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
induction m as [|m' IHm].
- simpl. intros n. rewrite -> mul_0_r. reflexivity.
- simpl. intros n. rewrite <- mult_n_Sm. rewrite -> IHm. rewrite -> add_comm. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (more_exercises)

    Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before you hack!) *)

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
induction n as [|n' IHn].
- reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
intros b. rewrite andb_commutative.
reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
intros n. rewrite mul_comm. rewrite mult_n_1. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
intros [|] [|].
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

Lemma mult_Sn_m : forall n m : nat, S n * m = n * m + m.
Proof.
intros n m. rewrite mul_comm. rewrite <- mult_n_Sm. rewrite mul_comm. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
induction n as [|n' IHn].
- reflexivity.
- intros m p.
  (* Arranging left part to introduce induction hypothesis *)
  rewrite add_comm. rewrite <- plus_n_Sm.
  rewrite add_comm. rewrite mult_Sn_m.
  rewrite -> IHn.
  (* Arranging right part to match *)
  rewrite mult_Sn_m.
  rewrite <- (add_assoc (n' * p) p (m * p)). rewrite (add_comm p (m * p)).
  rewrite add_assoc.
  (* Done *)
  reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
induction n as [|n' IHn].
- reflexivity.
- intros m p.
  (* Arranging left part to introduce induction hypothesis *)
  rewrite mult_Sn_m. rewrite IHn. 
  (* Arranging right part to match *)
  rewrite mult_Sn_m. rewrite mult_plus_distr_r.
  (* Done *)
  reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Nat to Bin and Back to Nat *)

(** Recall the [bin] type we defined in [Basics]: *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin)
.
(** Before you start working on the next exercise, replace the stub
    definitions of [incr] and [bin_to_nat], below, with your solution
    from [Basics].  That will make it possible for this file to
    be graded on its own. *)

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 b => B1 b
  | B1 b => B0 (incr b)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
match m with
| Z => O
| B0 b => 2 * (bin_to_nat b)
| B1 b => 1 + 2 * (bin_to_nat b)
end.

(** In [Basics], we did some unit testing of [bin_to_nat], but we
    didn't prove its correctness. Now we'll do so. *)

(** **** Exercise: 3 stars, standard, especially useful (binary_commute)

    Prove that the following diagram commutes:

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    That is, incrementing a binary number and then converting it to
    a (unary) natural number yields the same result as first converting
    it to a natural number and then incrementing.

    If you want to change your previous definitions of [incr] or [bin_to_nat]
    to make the property easier to prove, feel free to do so! *)

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
induction b as [|b1 IH1|b2 IH2].
- reflexivity.
- reflexivity.
- simpl. rewrite <- !plus_n_O. rewrite !IH2.
  rewrite <- add_assoc. rewrite plus_1_l.
  rewrite add_assoc. rewrite (add_comm (bin_to_nat b2) 1).
  rewrite <- add_assoc. rewrite (plus_1_l (bin_to_nat b2 + bin_to_nat b2)).
  reflexivity.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (nat_bin_nat) *)

(** Write a function to convert natural numbers to binary numbers. *)

Fixpoint nat_to_bin (n:nat) : bin :=
match n with
| O => Z
| S n => incr (nat_to_bin n)
end.

(** Prove that, if we start with any [nat], convert it to [bin], and
    convert it back, we get the same [nat] which we started with.

    Hint: This proof should go through smoothly using the previous
    exercise about [incr] as a lemma. If not, revisit your definitions
    of the functions involved and consider whether they are more
    complicated than necessary: the shape of a proof by induction will
    match the recursive structure of the program being verified, so
    make the recursions as simple as possible. *)

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
induction n as [|n' IHn].
- reflexivity.
- simpl. rewrite bin_to_nat_pres_incr. rewrite IHn. reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Bin to Nat and Back to Bin (Advanced) *)

(** The opposite direction -- starting with a [bin], converting to [nat],
    then converting back to [bin] -- turns out to be problematic. That
    is, the following theorem does not hold. *)

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

(** Let's explore why that theorem fails, and how to prove a modified
    version of it. We'll start with some lemmas that might seem
    unrelated, but will turn out to be relevant. *)

(** **** Exercise: 2 stars, advanced (double_bin) *)

(** Prove this lemma about [double], which we defined earlier in the
    chapter. *)

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
reflexivity.
Qed.

(** Now define a similar doubling function for [bin]. *)

Definition double_bin (b:bin) : bin :=
match b with
| Z => Z
| b' => B0 b'
end.

(** Check that your function correctly doubles zero. *)

Example double_bin_zero : double_bin Z = Z.
reflexivity. Qed.

(** Prove this lemma, which corresponds to [double_incr]. *)

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
intros [|b0|b1].
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

(** [] *)

(** Let's return to our desired theorem: *)

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

(** The theorem fails because there are some [bin] such that we won't
    necessarily get back to the _original_ [bin], but instead to an
    "equivalent" [bin].  (We deliberately leave that notion undefined
    here for you to think about.)

    Explain in a comment, below, why this failure occurs. Your
    explanation will not be graded, but it's important that you get it
    clear in your mind before going on to the next part. If you're
    stuck on this, think about alternative implementations of
    [double_bin] that might have failed to satisfy [double_bin_zero]
    yet otherwise seem correct. *)

Definition double_bin_correct_but_failing (b:bin) : bin :=
match b with
| Z => B0 Z (* Still equal to 0 but fails [double_bin_zero] *)
| b' => B0 b'
end.

(** To solve that problem, we can introduce a _normalization_ function
    that selects the simplest [bin] out of all the equivalent
    [bin]. Then we can prove that the conversion from [bin] to [nat] and
    back again produces that normalized, simplest [bin]. *)

(** **** Exercise: 4 stars, advanced (bin_nat_bin) *)

(** Define [normalize]. You will need to keep its definition as simple
    as possible for later proofs to go smoothly. Do not use
    [bin_to_nat] or [nat_to_bin], but do use [double_bin].

    Hint: Structure the recursion such that it _always_ reaches the
    end of the [bin] and _only_ processes each bit only once. Do not
    try to "look ahead" at future bits. *)

Fixpoint normalize (b:bin) : bin :=
match b with
| Z => Z
| B0 b' => double_bin (normalize b')
| B1 b' => B1 (normalize b')
end.

(** It would be wise to do some [Example] proofs to check that your definition of
    [normalize] works the way you intend before you proceed. They won't be graded,
    but fill them in below. *)

Example normalize_zero : normalize Z = Z. reflexivity. Qed.
Example normalize_zeroes_1 : normalize (B0 Z) = Z. reflexivity. Qed.
Example normalize_zeroes_2 : normalize (B0 (B0 Z)) = Z. reflexivity. Qed.
Example normalize_trailing_zero : normalize (B1 (B0 Z)) = B1 Z. reflexivity. Qed.
Example normalize_leading_zero : normalize (B0 (B1 Z)) = B0 (B1 Z). reflexivity. Qed.

(** Finally, prove the main theorem. The inductive cases could be a
    bit tricky.

    Hint: Start by trying to prove the main statement, see where you
    get stuck, and see if you can find a lemma -- perhaps requiring
    its own inductive proof -- that will allow the main proof to make
    progress. We have one lemma for the [B0] case (which also makes
    use of [double_incr_bin]) and another for the [B1] case. *)

Lemma nat_to_bin_nn_double_bin : forall n : nat, nat_to_bin (n + n) = double_bin (nat_to_bin n).
Proof.
induction n as [|n' IHn].
- reflexivity.
- simpl. rewrite add_comm. simpl. rewrite IHn. rewrite double_incr_bin. reflexivity.
Qed.

Lemma incr_double_b1 : forall b : bin, incr (double_bin b) = B1 b.
Proof.
induction b as [|b0 IH0|b1 IH1].
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
induction b as [|b0 IH0|b1 IH1].
- reflexivity.
- simpl. rewrite add_0_r. rewrite nat_to_bin_nn_double_bin. rewrite IH0. reflexivity.
- simpl. rewrite add_0_r. rewrite nat_to_bin_nn_double_bin. rewrite IH1. rewrite incr_double_b1. reflexivity.
Qed.

(** [] *)

(* 2026-01-07 13:17 *)
