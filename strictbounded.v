Require Import Bool.
Require Import Peano.
Require Import Omega.           (* I use this to handle a bunch of mundane index calculations*)

(* Summary:
We have the following notions of finiteness:

Definition Eaf (f: nat -> bool) := {n | forall m, m>=n -> f m = false}.
Definition StrictlyBounded (f: nat -> bool ):= {n | ((forall k, NrOfTrue k <= n) /\
                                    (forall np, (np< n) -> (not ((forall k, NrOfTrue k <= np) ))))}.
Definition Bounded (f: nat -> bool) := {n | ((forall k, NrOfTrue k <= n))}.

And we also have the following properties:
Definition Markovs_Principle:= forall P, DecidableP nat P ->  (({n: nat| P n} -> False)-> False) -> {n: nat| P n}. 
Definition WLPO := forall g:nat->bool, {forall n,g n=false} + {not (forall n,g n=false)}.


It is straightforward to see that we have: Eaf->StrictlyBounded->Bounded
 
In this file we prove the following:
(StrictlyBounded->Eaf) <-> Markovs_principle
(Bounded->StrictlyBounded) <-> WLPO.

These are shown as Theorem, everything else is lemma.
 *)

  Definition WLPO := forall g:nat->bool, {forall n,g n=false} + {not (forall n,g n=false)}.

  Definition WLPOInv := forall g:nat->bool, {forall n,g n=true} + {not (forall n,g n=true)}.

    
  (* Markovs_Principle *)
  Definition DecidableP (A: Set)(P: A -> Prop) := forall a: A, {(P a)} + {~(P a)}.
    
  Definition Markovs_Principle:= forall P, DecidableP nat P ->  (({n: nat| P n} -> False)-> False) -> {n: nat| P n}. 
  (* A formalization of Markovs principle using streams instead of predicates*)
  Definition  MP:= (forall g:nat->bool,  (({ n: nat | g n = true} -> False)-> False) -> { n: nat | g n = true}).

  
  Lemma WLPOImplWPOAlt: WLPO -> WLPOInv.
  Proof.
    intro.
    unfold WLPO in H.
    set (gneg :=  (fun x=> negb x )).
    intro.
    assert ({(forall n : nat, negb (g n) = false)} + {~ (forall n : nat, negb (g n) = false)});auto.
    elim H0;intros;auto.
    left;simpl;auto.
    intro.
    assert ( negb (g n) = false);auto.
    assert (true = negb false);auto.
    rewrite H2.
    rewrite<- H1;auto.
    assert (negb (negb (g n)) = g n);auto.
    apply negb_involutive.
    right;simpl;auto.
    intro.
    apply b.
    intro.
    assert (g n = true);auto.
    assert (false = negb true);auto.
    rewrite H3.
    rewrite H2.
    auto.
  Qed.


  Lemma WLPOAltImplWPO: WLPOInv ->  WLPO.
  Proof.
    intro.
    unfold WLPOInv in H.
    set (gneg :=  (fun x=> negb x )).
    intro.
    assert ({(forall n : nat, negb (g n) = true)} + {~ (forall n : nat, negb (g n) = true)});auto.
    elim H0;intros;auto with bool.
    left;simpl;auto with bool.
    intro.
    assert ( negb (g n) = true);auto with bool.
    assert (false = negb true);auto with bool.
    rewrite H2.
    rewrite<- H1;auto with bool.
    assert (negb (negb (g n)) = g n);auto with bool.
    apply negb_involutive.
    right;simpl;auto with bool.
    intro.
    apply b.
    intro.
    assert (g n = false);auto with bool.
    assert (true = negb false);auto with bool.
    rewrite H3.
    rewrite H2.
    auto.
  Qed.
 
  Lemma MarkPrinImplMP: Markovs_Principle -> MP.
  Proof.
    intros.
    intro.
    intro.
    apply X;auto.
    intro.
    destruct (g a);auto.
  Qed.

  Lemma MPImplMarkPrinciple(mp:MP): Markovs_Principle .
    Proof.
      unfold MP in mp.
      unfold Markovs_Principle.
      intros.
      unfold DecidableP in H.
      set (decider := (fun x => if (H x) then true else false)).
      assert ((({n : nat | decider n = true} -> False) -> False) -> {n :nat | decider n = true});auto.
      assert (forall a, (P a) <-> (decider a = true));auto.
      intros.
      split;intros;auto.
      unfold decider;elim (H a);auto.
      unfold decider in H2.
      induction (H a);auto.
      contradict H2;auto.
      assert ((({n : nat | decider n = true} -> False) -> False)).
      firstorder.
      assert ({n :nat | decider n = true});auto.
      elim H4;intros.
      exists x.
      apply H2;auto.       
    Qed.

 Section notionsOfFiniteness.
  Variable f: nat -> bool.
  
  (* Counts the nr of n s.t n<=m and f n = true *) 
  Fixpoint NrOfTrue (m : nat) : nat :=
    match m with
      | 0 => if (f 0) then 1 else 0
      | S n => if (f (S n)) then (S (NrOfTrue n) ) else (NrOfTrue n)
    end.


  Definition Eaf := {n | forall m, m>=n -> f m = false}.
  
  Definition StrictlyBounded := {n | ((forall k, NrOfTrue k <= n) /\
                                    (forall np, (np< n) -> (not ((forall k, NrOfTrue k <= np) ))))}.

  Definition StrictlyBoundedPred := {n | ((forall k, NrOfTrue k <= n) /\
                                        (n<>0-> (not ((forall k, NrOfTrue k <= pred(n))))))}.

  (* Sigma n. all k. #{i | 0 <= i <= k & f(i)=1} <= n *)
  Definition Bounded := {n| ((forall k, NrOfTrue k <= n))}.


  Lemma decidableF: forall n:nat, f n = true \/ f n = false.
  Proof.
    intros.
    induction (f n);auto.
  Qed.

  
  Lemma NrOfTrueIsMonotoneOneStep:  forall m:nat,   (NrOfTrue  m ) <= (NrOfTrue  (S m)).
    intros.
    assert (forall n:nat, f n = true \/ f n = false).
    apply decidableF;auto.
    induction m;auto.
    unfold NrOfTrue.
    assert (f 0 = true \/ f 0 = false);auto.
    assert (f 1 = true \/ f 1 = false);auto.
    simpl.
    case H0;intro;case H1;auto;intros;rewrite H2;auto;simpl;auto with arith;rewrite H3;auto.    
    assert (f (S m) = true \/ f (S m)=false);auto.
    assert (f (S (S m)) = true \/ f (S (S m))=false);auto.
    case H0;intro;case H1;auto;intros. simpl.
    rewrite H2;rewrite H3;auto.
    unfold NrOfTrue.
    rewrite H2;rewrite H3;auto.    
    unfold NrOfTrue.
    rewrite H2;rewrite H3;auto.    
    unfold NrOfTrue.
    rewrite H2;rewrite H3;auto.    
  Qed.

  Hint Resolve   NrOfTrueIsMonotoneOneStep.

  Lemma NrOfTrueIsMonotone:  forall m n :nat, m <=n ->  (NrOfTrue  m ) <= (NrOfTrue  n).
  Proof.
    intros.
    induction n;auto with arith.
    inversion H;auto.
    elim (eq_nat_dec m n);intros;auto.
    rewrite a;auto.
    elim (eq_nat_dec m (S(n)));intros;auto.
    rewrite a;auto.
    assert (m<n);auto with arith.
    omega. 
    assert (NrOfTrue m <= NrOfTrue n);auto.
    apply IHn.
    omega.
    assert (NrOfTrue n <= NrOfTrue (S(n)));auto.
    firstorder.
  Qed.
  Hint Resolve   NrOfTrueIsMonotone.

  
  Lemma NrOfTrueIsMonotoneConverse:  forall m n :nat, m <=n -> (NrOfTrue  n)  >= (NrOfTrue  m ).
  Proof.
    intros.
    firstorder.
  Qed.
  Hint Resolve   NrOfTrueIsMonotoneConverse.
    
  
  Lemma StrictlyBoundedSTBPredEQ: (StrictlyBounded -> StrictlyBoundedPred) * (StrictlyBoundedPred -> StrictlyBounded).
  Proof.
    split;intros.
    unfold StrictlyBounded in H.
    unfold StrictlyBoundedPred.
    elim H;intros x p.
    exists x.
    inversion p;auto.
    split;auto.
    intro.
    apply  (H1 (pred x)).
    omega.
    unfold StrictlyBoundedPred in H.
    unfold StrictlyBounded.
    elim H;intros x p.
    elim p;intros H0 H1.
    exists x.
    split;auto.
    intros.
    elim (eq_nat_dec x 0);intros;auto.
    omega.
    assert ( ~ (forall k : nat, NrOfTrue k <= pred x));auto.
    unfold not in  H3.
    unfold not.
    assert ((forall k : nat, NrOfTrue k <= np) ->(forall k : nat, NrOfTrue k <= pred x) );auto.
    intros.
    assert (NrOfTrue k <= np);auto.
    omega.
  Qed.
  
     
  (* We introduce the x-limit such the nrOfTrue is always smaller than it. 
     We then proceed to show that there is an index such that nrOfTrue is exactly x-limit. For this we use MP. 
     So we need to get a contradiction from the assumption ~ (exists n : nat, NrOfTrue n = x)
     This assumption lets us proof that forall n : nat, NrOfTrue n <> x, and then forall n : nat, NrOfTrue n < x
     Then we branch on wether x is 0 or S(p). In the first case it is easy. In the other case we have p<x, giving 
      ~ (forall k : nat, NrOfTrue k <= p), contradicting  forall n : nat, NrOfTrue n < x.
     
     Then we let the index be that number + 1, and we need to show that every element of f after this is false. This is proved by induction, and the fact that NrOfTrue is monotone.
      
     *)
  Lemma MarkovsPAndSTBImplEaf:  Markovs_Principle -> (StrictlyBounded -> Eaf).
  Proof.
    intro mp.
    intro sd.
    unfold Markovs_Principle in mp.
    unfold StrictlyBounded in sd.
    unfold Eaf.
    elim sd;intros x p.
    elim p.
    intro xlim.
    intro xsmallest.     
    assert ({index | NrOfTrue index = x});auto.
    apply mp.
    intro.
    apply eq_nat_dec.
    intro.
    assert (forall  n : nat, not (NrOfTrue n = x));auto.
    intro.
    intro.
    apply H.
    exists n;auto.
    assert (forall n : nat, NrOfTrue n < x);auto.
    intros.
    assert (NrOfTrue n <= x);auto.
    assert (NrOfTrue n <> x);auto.
    omega.
    assert (x=0\/ exists p,S(p)=x).
    induction x;auto with arith.
    right.
    exists ( x).
    auto.
    elim H2.
    intro.
    rewrite H3 in H1.
    assert (NrOfTrue 0 < 0);auto. (* Contradiction *)
    omega.
    intro.
    elim H3.
    intros.
    assert (x0 < x);auto.
    
    rewrite<- H4.
    auto.
    assert (~ (forall k : nat, NrOfTrue k <= x0));auto.
    assert (forall n : nat, NrOfTrue n <= x0).
    intro.
    assert (NrOfTrue n < x);auto.
    
    omega.      
    auto.

  
    elim H.
    intros x0 p0.
    exists (S(x0)).
    intros.
    
    assert (f m = false \/ f m = true);auto.
    induction (f m);auto.
    elim H1;auto.
    intros.

    assert (NrOfTrue m <= x);auto.
    inversion H0.
    intros.
    rewrite<- H4 in H2.
    assert ( NrOfTrue  (S(x0)) <= NrOfTrue  m);auto.
    assert (m <= S x0);auto.
    rewrite H4;auto.
   
    assert ( NrOfTrue (S x0) = S(x));auto.
    rewrite<- p0.  
    simpl.
    rewrite H2.  
    omega.
    rewrite H2.
    omega.
    assert ((S x0) < m);auto.
    omega.
    assert (x0 < m);auto.
    assert (NrOfTrue x0 <= NrOfTrue m);auto.
    apply NrOfTrueIsMonotone.
    omega.
    assert (NrOfTrue m = x);auto.
    rewrite p0 in H8.
    eauto.
    omega.
    assert (exists p, m = S(p));auto.
    exists (pred m).
    omega.
    elim H10.
    intro p1.
    intros.
    assert (NrOfTrue m = S(NrOfTrue p1));auto.
    compute;simpl;auto.
    rewrite H11;auto;simpl;auto.
    rewrite<- H11.
    rewrite H2.
    auto.
    assert ((NrOfTrue p1) < NrOfTrue m);auto.
    rewrite H12;auto.
    assert ((NrOfTrue p1) < x);auto.
    rewrite<- H9;auto.
    assert (x <= NrOfTrue m);auto.
    rewrite p0 in H8;auto.
    assert (p1>=x0);auto.
    omega.
    inversion H16.
    omega.
    assert (x0 < p1).
    omega.
    assert (NrOfTrue x0 <= NrOfTrue p1);auto.
    assert (NrOfTrue x0 < NrOfTrue m);auto.
    omega.
    firstorder.
  Qed.  

  End notionsOfFiniteness.

  

(* If there exists a positive index in the stream for which the predicate holds, there is a smallest*)
Lemma FindingSmallestInBoundedRange: forall P:nat->bool, {n:nat | P n = true}-> (P 0)=false
                                                         -> {n | P n = true /\ P (pred n) = false}.
Proof.
  intros.
  elim H.
  intro upperlimit.
  intros.
  induction upperlimit;auto.
  congruence.
  assert ({P upperlimit=true} + {P upperlimit = false});auto.
  elim (P upperlimit);auto.
  elim H1;intro;auto.
  exists (S upperlimit);auto.    
Qed.
Hint Resolve   FindingSmallestInBoundedRange.

 

Lemma FindingSmallestInBoundedRangePred (P:nat->Prop)(decidable: forall n, {P n}+{not (P n)}):  ({ n | P n}) ->  not (P 0) -> {n | P n  /\ not( P (pred n))}.
Proof.
  intros.
  elim H.
  intro upperlimit.
  intros.
  induction upperlimit;auto.
  congruence.
  assert ({P upperlimit} + {not (P upperlimit)});auto.
  elim H1;intro;auto.
  exists (S upperlimit);auto.    
Qed.
Hint Resolve FindingSmallestInBoundedRangePred.



Lemma trueOrFalse(a b :bool) : {a = b} + {a=negb b}.
Proof.
  compute.
  elim a;elim b;intros;auto.
 Qed.
Hint Resolve   trueOrFalse.
 
Lemma inBoundedRangeDecidable (g:nat->bool)(limit:nat)(value:bool):{x | x<=limit /\ g x = value} + {(forall x, x<=limit -> not (g x = value))}.
Proof.
  pose (trueOrFalse (g limit) value) as H.
  pose (trueOrFalse (g 0) value) as H0.
  elim H;intro limval;elim H0; intro valval;try (rewrite hval);try (rewrite valval).
  left; exists limit;auto.
  left; exists limit;auto.
  left; exists 0;auto.  
  split;auto.
  omega.
  induction limit;auto.
  right;auto.
  intros.
  assert (x=0).
  omega.
  rewrite H2.
  rewrite valval.
  apply no_fixpoint_negb.
  assert ({g limit =  value} + {g limit = negb value});auto.
  elim H1;intros.
  left.
  exists limit;auto. 
  assert (            {x : nat| x <= limit /\ g x = value} +
            {(forall x : nat, x <= limit -> g x <> value)});auto.
  elim H2;intros;auto.
  left.
  elim a;intros x H3;auto.
  elim H3.
  exists x;auto.  
  assert ({g (S limit) =  value} + {g (S limit) = negb value});auto.
  elim H3;intros;auto.
  left.
  exists (S limit);auto.
  right.  
  intros.
  assert ({x <= limit} + {limit < x}).
  apply(le_lt_dec x limit);auto.
  elim H5;auto;intros;auto.
  assert (x = S limit);auto.
  omega.
  rewrite H6;auto.
  rewrite b1;apply no_fixpoint_negb.
Qed.
Hint Resolve   inBoundedRangeDecidable.



Lemma NrOfTrueWithConstantNegFunction (trues lim:nat )(f : nat-> bool) :  ((NrOfTrue f lim)=trues /\ forall x, x>lim -> f x = false) -> forall y, y>lim -> (NrOfTrue f y )=trues. 
    Proof.
      intros.
      elim H;intros.
      induction y;auto.
      contradict H0.
      omega.
      assert (f (S y) = false);auto.
      assert (NrOfTrue f y = trues);auto.
      elim (eq_nat_dec y lim);intro.
      rewrite a;auto.
      apply IHy.
      omega.
      unfold NrOfTrue.
      rewrite H3.
      auto.
    Qed.


Fixpoint trueOnFirst (g:nat-> bool) (n:nat):  (bool):=
  match n with
    | 0 => (g 0)
    | S n =>  if (g (S n)) then if (inBoundedRangeDecidable g n true ) then false else true   else false
  end.


Lemma nrOftrueIntrueIsLimitedByfalse(g:nat->bool): forall k, (forall x, x<=k ->  g x = false) <->  NrOfTrue  g k=0.
Proof.
intros.
induction k;auto.
split.
intros.
assert (g 0 =false);auto.
compute.
rewrite H0;auto.
intros.
assert (x=0).
omega.
rewrite H1.
unfold NrOfTrue in H.
induction (g 0);auto.
contradict H.  
omega.

split.
intros.
assert ( NrOfTrue g k = 0);auto.
apply IHk.
intros.
apply H;auto.
assert (g ( S k) = false);auto.
compute;auto.
rewrite H1.
simpl.
assert ({k<=0} + {0<k}).
apply (le_lt_dec).
elim H2;auto.
intros.
assert (NrOfTrue g k = 0);auto.
assert (NrOfTrue g k <= NrOfTrue g (S k));auto.
apply NrOfTrueIsMonotone.
omega.
omega.
assert ((forall x : nat, x <= k -> g x = false));auto.
apply IHk;auto.

assert ({S k<=x} + {x<S k}).
apply (le_lt_dec).
elim H3;intros;auto.
assert (x = S k);auto.
omega.
rewrite H4.
unfold NrOfTrue in H.
induction (g (S k));auto.
contradict H.
omega.
apply H2.
omega.
Qed.
Hint Resolve   nrOftrueIntrueIsLimitedByfalse.



Lemma trueOnFirstImplTrueForG(g:nat->bool): (forall x, (trueOnFirst g) x = true -> (g x)=true).
Proof.
intros.
induction x;auto.
unfold trueOnFirst in H.
induction (g (S x));auto.
Qed.

Hint Resolve trueOnFirstImplTrueForG.

Lemma trueOnFirstAlwaysFalseAfter(g:nat->bool): (forall x, (trueOnFirst g) x = true -> forall y, y>x ->(trueOnFirst g) y = false).
Proof.
  intro.
  intro.
  intro.
  induction y;intros;auto.
  contradict H0.
  omega.

   
  assert ({x=y}+{x<>y});auto.
  apply (eq_nat_dec x y);auto.
  induction H1;intros;auto.
  assert (g x = true);auto.
  unfold trueOnFirst.
  induction (g (S y));auto.
  induction (inBoundedRangeDecidable g y);auto.
  intros.
  assert (x <= y -> g x <> true);auto.
  rewrite a in H2.
  assert ( g y <> true);auto.
  rewrite<- a in H3. 
  contradict H3;auto.

  assert (x < y);auto.
  omega.  
  assert (trueOnFirst g y = false);auto.
  unfold trueOnFirst.
  induction (g ( S y));auto.
  induction (inBoundedRangeDecidable g y);auto.
  intros.
  assert ( g x <> true).
  apply b0;auto.
  omega.
  contradict H3.
  apply trueOnFirstImplTrueForG;auto.  
Qed.
Hint Resolve trueOnFirstAlwaysFalseAfter.


Lemma trueOnFirstConstantFalseImplConstantFalseHelper(g:nat->bool)(lim:nat):(forall x : nat,x<=lim ->  trueOnFirst g x = false) -> ((forall n : nat,n<=lim ->  g n = false)).
Proof.
  induction lim;intros.
  assert (n=0).
  omega.
  assert (trueOnFirst g 0 = false);auto.
  rewrite H1.
  auto.
  elim (eq_nat_dec n (S lim));intros;auto.
  rewrite a.
  assert (trueOnFirst g (S lim) = false);auto.
  unfold trueOnFirst in H1.
  induction (g (S lim));auto.
  induction (inBoundedRangeDecidable g lim true);auto.
  elim a0;intros x H2;auto.
  elim H2;intros.
  assert (g x = false).
  apply IHlim;intros;auto.
  rewrite<- H4.
  rewrite<- H5.
  auto.
  assert (n<=lim);auto.
  omega.
Qed.
Hint Resolve trueOnFirstConstantFalseImplConstantFalseHelper.

Lemma trueOnFirstConstantFalseImplConstantFalse(g:nat->bool):(forall x : nat, trueOnFirst g x = false) -> ((forall n : nat, g n = false)).
Proof.
  intro.
  intro lim.  
  assert (((forall n : nat,n<=lim ->  g n = false)));auto.
  apply trueOnFirstConstantFalseImplConstantFalseHelper;auto.  
Qed.

   
Lemma nrOftrueIntrueOnFirstStays1Succ(g:nat->bool): forall k, NrOfTrue (trueOnFirst g) k=1->NrOfTrue (trueOnFirst g) (S k)=1.
  Proof.
    intros.
    apply (NrOfTrueWithConstantNegFunction 1 k  );auto.
    split;auto.
    intros.
    assert ({x : nat | x <= k /\ (trueOnFirst g ) x = true} +
            {(forall x : nat, x <= k -> (trueOnFirst g ) x <> true)});auto.
    
    elim H1;intros;auto.
    elim a.
    intros x0 H2.
    elim H2;intros.
    apply (trueOnFirstAlwaysFalseAfter g x0);auto.
    omega.
    assert (forall x : nat, x <= k -> trueOnFirst g x =false );auto.
    intros.
    assert (trueOnFirst g x0 <> true);auto.
    apply (not_true_iff_false);auto.
    assert (trueOnFirst g 0 = false);auto.
    apply H2;auto.
    omega.
    assert (NrOfTrue (trueOnFirst g) 0 = 0);auto.
    unfold NrOfTrue.
    rewrite H3;auto.
    assert (NrOfTrue (trueOnFirst g) k = 0);auto.
    apply nrOftrueIntrueIsLimitedByfalse;intros;auto.
    contradict H;auto.
    omega.
  Qed.
Hint Resolve nrOftrueIntrueOnFirstStays1Succ.
  
Lemma nrOftrueIntrueOnFirstIs1or0(g:nat->bool): forall k, NrOfTrue (trueOnFirst g) k<=1.
Proof.
  intro.
  induction k;auto.
  unfold NrOfTrue.
  elim (trueOnFirst g 0);auto.
  elim (lt_eq_lt_dec (NrOfTrue (trueOnFirst g) k) 1 );intro.
  elim a;auto;intros;auto.
  assert (NrOfTrue (trueOnFirst g) k=0);auto.
  omega.
  unfold NrOfTrue.
  elim (trueOnFirst g (S k));auto.
  assert (NrOfTrue (trueOnFirst g) (S k) = 1).
  apply nrOftrueIntrueOnFirstStays1Succ;auto.
  omega.
  contradict IHk.
  omega.
Qed.  


Theorem EafAndSTBImplMarkovsP (arrow: forall f,  StrictlyBounded f -> Eaf f) : Markovs_Principle.
    Proof.
      apply MPImplMarkPrinciple;auto.
      unfold MP.
      unfold StrictlyBounded in arrow.
      unfold Eaf in arrow.
      intros.
      assert ( ~ (forall n : nat, not (g n = true)));auto.
      intro.
      firstorder.
      assert ( ~ (forall n : nat, g n = false));auto.
      intro.
      apply H0;intros;auto.
      assert (g n = false);auto.
      rewrite H2.
      congruence.

      assert {n : nat | forall m : nat, m >= n -> (trueOnFirst g) m = false};auto.
      apply arrow;auto.
      exists 1;intros;auto.
      split;intros;auto.
      apply (nrOftrueIntrueOnFirstIs1or0).
      assert (np =0);auto.
      omega.
      rewrite H3.
      intro.
      assert (forall k : nat, NrOfTrue (trueOnFirst g) k = 0);intros;auto.
      assert (NrOfTrue (trueOnFirst g) k <= 0);auto.
      omega.
      assert (forall k, (forall x : nat, x <= k -> (trueOnFirst g) x = false));auto.
      intro.
      apply nrOftrueIntrueIsLimitedByfalse;auto.
      assert (forall x, g x = false);auto.
      apply trueOnFirstConstantFalseImplConstantFalse;auto.
      intro.
      assert (forall y : nat, y <= x -> trueOnFirst g y = false);auto.
      apply H6.
      
            
      
      elim H2.
      intro limit.
      intros H3.
      assert {y | (trueOnFirst g y) = true};auto.
      assert ({x : nat | ( x <= limit /\ (trueOnFirst g x) = true)} +
              {(forall x : nat, x <= limit -> (trueOnFirst g x) <> true)}).
      apply inBoundedRangeDecidable. 
      elim H4;auto.
       intros.
       elim a;intros.
       exists x;auto.
       firstorder.
       intros.
       assert (forall x : nat, x <= limit -> trueOnFirst g x = false);auto.
       intros.
       assert (trueOnFirst g x <> true);auto.
       apply not_true_iff_false;auto.
       assert (forall x : nat,  trueOnFirst g x = false);auto.
       intros.
       elim (lt_eq_lt_dec x limit);intros;auto.
       elim a;intros;auto.
       apply H5;auto.
       omega.
       apply H5;auto.
       omega.
       apply H3;auto.
       omega.
       assert (forall n : nat, g n = false);auto.
       apply trueOnFirstConstantFalseImplConstantFalse;auto.
       contradict H7;auto.   
       elim H4.
       intros.
       exists x;auto.
    Qed.


    
Theorem MarkovsPAndSTBImplEafOuter:  Markovs_Principle ->forall f:nat->bool,  (StrictlyBounded f) -> (Eaf f).
  intros M f.
  apply (MarkovsPAndSTBImplEaf f M).
Qed.


Lemma WLPOImplBoundedImplSTBPred:  WLPO -> (forall f:nat->bool,  (Bounded f) -> (StrictlyBoundedPred f)).
Proof.
  intros.
  unfold WLPO in H.
  unfold Bounded in H0.
  unfold StrictlyBoundedPred.
  elim H0.
  intro upperlimit.
  intro H1.


  assert(forall g : nat -> bool,
           {(forall n : nat, g n = true)} + {~ (forall n : nat, g n = true)});auto.
  apply  WLPOImplWPOAlt;auto.

  assert (forall pl, (forall n : nat,
                        ((NrOfTrue f n)<=pl) <->
                        ((Compare_dec.leb (NrOfTrue f n) pl) = true))).

  intro;auto.
  split;intros.
  assert (NrOfTrue f n <= pl);auto.
  apply leb_correct;auto.
  assert(Compare_dec.leb (NrOfTrue f n) pl = true);auto.
  apply leb_complete;auto.

  set (fixer:=(fun pl k=>  (Compare_dec.leb (NrOfTrue f k) pl))).
  (* Lets try 0 first. *)
    
  assert ((forall k : nat, NrOfTrue f k <= 0) +
          ~ (forall k : nat, NrOfTrue f k <=  0));auto.
  
  elim (H2 (fixer 0));auto;intros.
  left;auto.
  intro.
  assert (fixer 0 k = true);auto.
  unfold fixer in H4.
  apply H3;auto.
  right.
  unfold not in b.
  unfold not.
  unfold fixer in b.
  intro.
  apply b.
  intros.
  assert (NrOfTrue f n <= 0);auto.
  apply H3;auto.
  
  elim H4.
  intro.
  exists 0;auto.
  intro notZero.
  clear H4.

  assert ({n: nat|
            (forall k : nat, NrOfTrue f k <= n) /\
            (~ (forall k : nat, NrOfTrue f k <= pred n))}).

  apply FindingSmallestInBoundedRangePred.
  intros pl.
  elim (H2 (fixer pl));auto;intros.
  left;auto.
  intro.
  assert (fixer pl k = true);auto.
  unfold fixer in H4.
  apply H3;auto.
  right.
  unfold not in b.
  unfold not.
  intro.
  apply b.
  intro.
  unfold fixer.
  assert (NrOfTrue f n <= pl);auto.
  apply H3;auto.
  exists upperlimit.
  auto.
  intro.
  apply notZero;auto. 
  elim H4.
  intros x H5.
  exists x.
  elim H5.
  intros.
  split;auto.
Qed.


Theorem WLPOImplBoundedImplSTB:  WLPO -> (forall f:nat->bool,  (Bounded f) -> (StrictlyBounded f)).
Proof.
  intros  wlpo f bounded.
  apply (snd (StrictlyBoundedSTBPredEQ f)).
  apply WLPOImplBoundedImplSTBPred;auto.
Qed.
    
Theorem BoundedImplSTBImplWLPO:  (forall f:nat->bool,  (Bounded f) -> (StrictlyBounded f)) -> WLPO.
Proof.
  intro arrow.
  unfold Bounded in arrow.
  unfold StrictlyBounded in arrow.

    (* The idea: Lets make a function which is true only on the exactly first
  place where g n = true, and false everywhere else. This has a limit of 1. But
  is has a limit on exactly 1 iff {~ (forall n : nat, g n = false)} and 0 iff
  {(forall n : nat, g n = false)}. *)

unfold  WLPO.
intro g.


assert {n : nat |
            (forall k : nat, NrOfTrue (trueOnFirst g) k <= n) /\
            (forall np : nat,
               np < n -> ~ (forall k : nat, NrOfTrue (trueOnFirst g) k <= np))};auto.

apply arrow;auto.
exists 1;auto.
intros;auto.
apply nrOftrueIntrueOnFirstIs1or0.

elim H.
assert (forall (g : nat -> bool) (k : nat), NrOfTrue (trueOnFirst g) k <= 1);auto.
apply nrOftrueIntrueOnFirstIs1or0.
intro lim.
intro H1.

elim H1.
intros.
assert (lim <= 1).
assert (forall k : nat, NrOfTrue (trueOnFirst g) k <=1).
apply nrOftrueIntrueOnFirstIs1or0.
elim (le_lt_dec lim 1).
intros.
auto.
intro.
assert ( ~ (forall k : nat, NrOfTrue (trueOnFirst g) k <= 1)).
apply H3.
auto.
contradiction.

elim (lt_eq_lt_dec lim 1 );auto;intros;auto.
elim a;intros;auto.
assert (lim=0).
omega.
assert ( forall k : nat, NrOfTrue (trueOnFirst g) k <= 0).
rewrite H5 in H2.
apply H2.
left.
intro n.
assert (NrOfTrue (trueOnFirst g) n <= 0);auto.
assert (NrOfTrue (trueOnFirst g) n = 0);auto.
omega.
assert ((forall x : nat, x <= n -> trueOnFirst g x = false) );auto.
apply nrOftrueIntrueIsLimitedByfalse;auto.
apply (trueOnFirstConstantFalseImplConstantFalseHelper g n);auto.
right.
intro.
assert (forall k, NrOfTrue  g k=0).
intro.
apply (nrOftrueIntrueIsLimitedByfalse g).
intros.
apply H5.
assert (~ (forall k : nat, NrOfTrue (trueOnFirst g) k <= 0));auto.
apply H3.
omega.
apply H7.
intro.

assert ( forall x : nat,   trueOnFirst g x = false);auto.
intro.
assert (g x = false);auto.
assert (trueOnFirst g x = true \/ trueOnFirst g x =false);auto.
elim (trueOnFirst g x);auto.
elim H9;intros;auto.
assert (g x = true);auto.
rewrite H8 in H11.
contradict H11.
auto.
assert (NrOfTrue (trueOnFirst g) k = 0);auto.
apply nrOftrueIntrueIsLimitedByfalse.
intros;auto.
omega.
assert False.
omega.
contradict H5.
Qed.
