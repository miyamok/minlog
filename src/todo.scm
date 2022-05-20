;; 2022-05-11.  todo.scm

;; 2022-05-11.  For simplified simultaneous (co)recursion the types
;; should be differen (email by Jan Belle, 2020-08-26; see
;; examples/test/pconst.scm).  For the tree, tlist example the type
;; of (Rec tree=>alpha) is tree=>alpha=>alpha=>alpha, but it should
;; be tree=>alpha=>(list=>alpha)=>alpha.  This problem shows up at
;; simplified corecursion when formulating the computation rules.

;; 2022-05-10.  (use "GenRead") does not work (MATCH-TREE-BOUND reached).
;; However (intro 1) works.  Why? (see edamplesanalysissdrw.scm)

;; 2021-11-13.  Replace NatToPos by a pconst ntp with 3 computation rules,
;; using PosS in the last.  This is faster than NatToPos when computing
;; the normal form of ntp(PosToNat 100000)  (0.42s rather than 0.66s).
;; Also the trick with cNatPos becomes superfluous.

;; 2018-09-03.  search and auto should get an optional ignore-deco-flag

;; 2017-04-01.  Adapt the proofs of AllTotalIntroSound and
;; AllTotalElimSound to use CoEqPNc rather than EqD.  Add transitivity
;; of CoEqPNc as an axiom.

;; 2016-10-16.  formula-and-falsity-avar-to-efq-proof needs to be
;; adapted to the general form of clauses, for instance
;; allnc n^(TotalNat n^ -> allnc m^(TotalNat m^ -> TotalLam(Thrd n^ m^)))

;; 2016-10-16.  Adapt all-formula-to-mr-ind-proof to invariance axioms.

;; 2016-08-12.  In the dev branch examples/classical/gcd.scm gives an
;; error at (proof-to-extracted-d-term (theorem-name-to-proof "GcdAnd"))
;; mk-term-in-app-form
;; applicable type expected
;; nat

;; 2016-06-09.  Replace axiom mr-intro-mr-aconst by a theorem

;; 2016-06-09.  Parsing of (i) cases display (ii) predicates

;; 2016-04-17.  Prove axioms of an ordered field for rat, with RatEqv
;; == as equality.  Define RatUDiv.

;; 2015-06-07.  axiom-to-soundness-proof has problems at intro and
;; elim axioms for idpcs with parameters (already in the unnested case).

;; 2015-04-28.  Axioms InhabTotal and InhabTotalMR should be removed
;; since we do not require any more that each type has a total
;; element.  This is a consequence of allowing algebras without
;; nullary constructors (like typeIntv).

;; 2015-03-22.  In add-co and should use decorated connectives only
;; when necessary.  Presently we have for instance
;; (add-ids
;;  (list (list "G" (make-arity (py "r")) "lr"))
;;  '("G(Z r)" "InitG")
;;  '("allnc x^ all b(G x^ -> G(inv b***(x^ av Lft)))" "GenGLR")
;;  '("allnc x^((CoD(cterm (x^) G x^))x^ -> G(x^ av Mid))" "GenGM"))
;; (add-co "G")
;; (pp "CoGClause")
;; allnc x^(
;;  CoG x^ -> 
;;  x^ eqd(Z r) orr 
;;  exr x^0 ex b(CoG x^0 andl x^ eqd inv b***(x^0 av Lft)) ord 
;;  exr x^0((CoD (cterm (x^1) CoG x^1))x^0 andl x^ eqd x^0 av Mid))
;; Here the primitive & should be used rather than andl

;; 2015-02-09.  In temp/examplesarithdickson.scm.  Error in
;; term-to-scheme-expr.  
;; (ev expr)
;; ExOne
;; number expected
;; ((testsum (quote (if ((((natRec ...))))))))
;; Other errors in terms-to-haskell-program: (i)
;; natGrecGuard n7836 a = (natGrecGuard n7836 a) (non terminating) is
;; generated.  (ii) After (set! HASKELL-GREC-MEASURE-FLAG #t) get
;; PARSE ERROR : undefined-token int

;; 2014-10-18.
;; Check expand-theorems

;; 2014-10-13.
;; Should we always use general variables in inductive definitions?
;; Problem: when proving that a competitor satisfies the clauses we
;; then have to prove all xs^ ... without knowing STotalList xs^ .
;; This can block applications of necessary lemmas.  Example:

;; (add-ids
;;  (list (list "RevI" (make-arity (py "list alpha") (py "list alpha"))))
;;  '("RevI(Nil alpha)(Nil alpha)" "InitRev")
;;  '("all x^,xs^,ys^(RevI xs^ ys^ -> RevI(xs^ ++x^ :)(x^ ::ys^))" "GenRev"))

;; RevIUnique
;; (set-goal "all xs,ys(RevI xs ys -> ys eqd Rev xs)")
;; (assume "xs" "ys" "Rxsys")
;; (elim "Rxsys")
;; (use "InitEqD")
;; (assume "x^" "xs^1" "ys^1" "Rxsys1" "ys1=Rxs1")

;;   xs  ys  Rxsys:RevI xs ys
;;   x^  xs^1  ys^1  Rxsys1:RevI xs^1 ys^1
;;   ys1=Rxs1:ys^1 eqd Rev xs^1
;; -----------------------------------------------------------------------------
;; ?_5:(x^ ::ys^1)eqd Rev(xs^1++x^ :)

;; (simp "ListRevAppdPartial")
;; is applicable, but requires STotalList xs^1 which we don't have.

;; Cure: use STotalList xs^ as additional assumptions

;; (add-ids
;;  (list (list "RevI" (make-arity (py "list alpha") (py "list alpha"))))
;;  '("RevI(Nil alpha)(Nil alpha)" "InitRev")
;;  '("all x^,xs^(STotalList xs^ -> 
;;     all ys^(STotalList ys^ -> 
;;             RevI xs^ ys^ -> RevI(xs^ ++x^ :)(x^ ::ys^)))" "GenRev"))

;; add-ids
;; non-computational-invariant clause expected

;; (add-ids
;;  (list (list "RevI" (make-arity (py "list alpha") (py "list alpha"))))
;;  '("RevI(Nil alpha)(Nil alpha)" "InitRev")
;;  '("allnc x^,xs^(STotalList xs^ -> 
;;     allnc ys^(STotalList ys^ -> 
;;             RevI xs^ ys^ -> RevI(xs^ ++x^ :)(x^ ::ys^)))" "GenRev"))

;; add-ids
;; non-computational-invariant clause expected
;; This has to be corrected.

;; 2014-01-15.  Replace min-excl-proof? by a property of the proven
;; formula.   (Done 2014-01)

;; 2014-01-07.  Insert readme-parens.txt in tutor.

;; 2014-01-05.  More display functions in tutor: ppc pp
;; proof-to-aconsts pp-subst search-about pp for names of aconsts dp
;; dnp proof-to-expr proof-to-expr-with-formulas
;; proof-to-expr-with-aconsts display-tokens display-pconst
;; display-current-goal dcg

;; 2014-01-05.  (e, Total, RTotal) ~ (=, Equal, REqual).  add-equality
;; and add-requality to be defined.  The predconst Equal_{\alpha}
;; should have type alpha.  Example: CoREqualList, bisimilarity.

;; 2013-06-06.  In psym.scm delete the comment saying that we need
;; inductively defined predicates with object parameters.  This is not
;; necessary: take them as extra arguments.  Done 2014-01-05

;; 2013-05-16.  Formulate ex-expartial-aconst and expartial-ex-aconst
;; with exnc rather than with exr (to keep the primitive existentials
;; ex and exnc separate from the inductively defined ones).  Introduce
;; aconsts and theorems for abbreviations:

;; AllTotalIntro (was AllPartial-All)
;; AllTotalElim (was All-AllPartial)
;; ExTotalIntro (was ExPartial-Ex)
;; ExTotalElim (was Ex-ExPartial)

;; ExDTotalIntro
;; ExLTotalIntro
;; ExRTotalIntro
;; ExUTotalIntro
;; ExDTotalElim
;; ExLTotalElim
;; ExRTotalElim
;; ExUTotalElim

; 2012-12-27.  Avoid #|...|# commenting syntax (it does not work
; e.g. for guile).  Use ordinary line commenting sytax ;; instead.
; When it is desired to check matching parentheses, use '(...).

; 2012-09-07.  check-formula should check predicates.  Need:
; check-predicate and within that check-idpredconst and check-cterm.

; 2011-05-13.  msplit needs to be adapted to right associativity of
; conjunction.

; 2011-05-13.  In lib/natinf.scm provide the missing proofs for
; correctness of the rewrite rules.

; 2011-05-13.  Discourage dot notation by letting token-tree-to-string
; return strings not using the dot notation.  But still the parser
; should be able to read most formulas written in dot notation.
; Exception: T & all boole.T & T .  Remove the global variable
; DOT-NOTATION

; 2011-05-12.  Provide gfp-aconst-and-bound-to-bgfp-proof
; similar to corec-const-and-bound-to-bcorec-term

; 2011-03-27.  Remove impnc-elim and allnc-elim.  imp-elim and
; all-elim suffice.  Hence: impnc-elim to be replaced by imp-elim, and
; allnc-elim to be replaced by all-elim.  Internally imp-form-to and
; impnc-form-to to be replaced by imp-impnc-form-to.  Similarly
; all-form-to and allnc-form-to to be replaced by all-allnc-form-to

; 2011-03-27.  check-and-display-proof-aux should be made more
; tolerant, accordingly.  Moreover, in allnc-intro with A n.c. it is
; allowed to have all x A as conclusion.  Similar in all-intro with A
; n.c. it is allowed to have allnc x A as conclusion.  Correponding
; tolerance should happen for implication introduction.  In addition,
; if the premise A is n.c., then we are allowed to have either A --> B
; or A -> B as conclusion.

; 2011-03-27.  New style: Use allnc and --> only when unavoidable.  In
; particular: c.i. aconsts should use all x for their free parameter
; variables.  Caution: in proof-substitute it is assumed that allnc is
; used for the free parameter variables of aconsts.

; 2011-01-11.  Allow alg-pattern in add-ids.  This is urgent for ExL
; ExR etc.  In remove-idpc-name preexisting algebras should not be
; removed (example: if Even is defined with algebra nat, then removing
; Even should not remove nat).
; Done.

; 2011-01-11.  Change "gind" into "gindguard" and use gind for the
; unguarded form.  Check gind-aconst-to-mr-gind-proof-aux .
; Rename GInd into GIndGuard.  The (proper) GInd then is a theorem
; proved from GIndGuard:
; all h,x((all y(h y<h x -> Q y) -> Q x) -> all boole(boole -> Q x))

; (set-goal (pf "all h,x(all x((all y(h y<h x -> Q y) -> Q x)) -> Q x)"))
; (assume "h" "x" "Prog")
; (use (make-proof-in-aconst-form
;       (all-formula-and-number-to-gindguard-aconst (pf "all x Q x") 1))
;      (pt "h") (pt "True"))
; (use "Prog")
; (use "Truth-Axiom")
; (save "GInd")

; Remove GRec.  It can be replaced by cGInd.

; 2009-10-18.  gind with no argument should act as course-of-values
; induction.  Internally: use a flag cvind?  If true, replace calls to
; the measure function h by just using the argument.

; 2009-10-18.  It can be useful to temporarily switch off computation
; and/or rewrite rules for a program constant.  Coq uses the terms
; opaque and transparent for this.  Possible terminology in Minlog:
; deanimate and animate.

; 2008-06-14.  Some axioms are only there for convenience.  They could
; be proved if the predicate constants Equal and Total are replaced by
; inductively defined predicates, and pair types are defined.  The
; only axioms unprovable from the intro and elimination axioms are
; finalg-to-=-to-e-1-aconst and finalg-to-=-to-e-2-aconst, and the
; (implicit) axioms stating that the constructors are injective and
; have disjoint ranges.  -- Replace the predicate constant Equal by
; the inductively defined EqD, define atom p by p eqd True and falsity
; by False eqd True (partially done in temp/eqd.scm).

; 2008-03-13.  Fine tune the refined A translation by uniformity.

; 2007-07-12.  Change Pvar^' into Pvar.  That is: for pvars ^ (') means
; *no* positive (negative) content.  This is different from the usage
; of ^ for object variables (where x^ is more general than x), but
; seems to be more appropriate for pvars.
; Done.

; 2006-02-16.  Quantification over type variables and predicate
; variables should be admitted.  We remain predicative, if we restrict
; all-elimination to comprehension terms without predicate and type
; quantifiers (see Takeuti: Two applications of Logic to Mathematics).
; For normalization of proofs via terms, we also need type abstraction
; in terms.  -- One benefit: The lemmata for Dickson can be formulated
; and used in their original generality.

; 2006-01-01.  It would be good to have (admit), which admits the
; present goal by adding a corresponding global assumption.
; Done.

; 2005-12-28.  pp gives an incorrect result:
; (pp (pf "boole & (all unit.boole1 -> boole2) & (all unit.boole1 -> boole2)"))
; boole & all unit.boole1 -> boole2 & all unit.boole1 -> boole2
; Done.  Moreover, by setting DOT-NOTATION to #t or #f, one can switch.

; 2005-12-04.  pp does not work for types
; (type-to-string type) ;"nat yplus unit=>alpha3=>alpha3=>alpha3"
; (pp type)
; Error in car: () is not a pair.
; Done.

; 2005-12-04.  When an algebra is created, one should add a
; computation rule sending (Inhab alg) into the first nullary
; constructor, if there is one.  Otherwise, e.g., for the algebra
; "term", one can add a computation rule (pt "(Inhab term)") --> (pt
; "Var 0").  One can also change the canconical inhabitant.  Example:
; (pt "(Inhab boole)") --> (pt "False"), instead of True.
; type-to-canonical-inhabitant gives for a non-algebra ground type the
; term (pt "(Inhab type)"), which may or not normalize to something
; else.  This view should simplify add-ids: there is no need to create
; DummyalgAcc etc.  Done.

; 2005-12-03.  simphyp does not allow to give names to the newly
; introduced hypotheses.  Done: simphyp-with-to expects a string as
; its last argument, which is used (via name-hyp) to name the newly
; introduced simplified hypothesis.

; 2005-12-03.   There are cases when we need to normalize twice.
; Problem: by beta conversion we get terms where an if-term can be
; eta expanded.  Example, using listrev.scm:

(add-var-name "bc" (py "list(boole@@boole)"))
(add-var-name "pq" (py "boole@@boole"))

(define term
  (pt "([bc]([pq]left pq)map bc)
       (([i][if boole (False@False) (True@True)])fbar k)"))

(pp (nt term))
; ([n0]left[if boole (False@False) (True@True)])fbar k
(pp (nt (nt term)))
; ([n0][if boole False True])fbar k

; -- Done, by correction of normalize-term-pi-with-rec-to-if in term.scm

; 2005-12-03.  Naming conventions should be observed generally.  (1) A
; theorem or global assumptions with computational content sould have
; a valid token string as name.  It should start with a capital, to
; make the prefix "c" (for content) readable.  (2) Type qualifiers
; should be either always in front or always at the end.

; 2005-12-01.  use should be made usable for formulas with type and
; predicate variables of non-null arity.  So allow lists of types and
; strings for variables in the arguments.  Match should then infer the
; comprehension terms.

; 2005-12-01.  (pp (pf "all n ex m.T -> F")) => all n.ex m.T -> F with
; an unnecessary dot.
; Done

; 2005-12-01.
; (inst-with-to "WKL!" (pt "Ext t(Up s)") "?" "?" "?" "ExHyp1") =>
; ? illegal for inst-with-to; use inst-with instead.
; Why not give a name to  the resulting instantiated hypothesis?

; 2005-12-01.
; In a goal whose context is without t, executing
; (inst-with "WKL!" (pt "Ext t(Up s)") "?" "?" "?")
; (assert (pf "T")) =>
; unexpected free variables
; t
; Problem: we have produced an incorrect context, which is noticed in
; context-and-cvars-and-formula-to-new-goal
; At least a warning should be given.  Better: forbid it.  The
; drinker formula can be proved using (Inhab alpha)

; Modified x-and-x-list-to-proof-and-new-num-goals-and-maxgoal
; accordingly (In examples/classical/test.scm).  Now tests from
; quant.tac showed problems:

(define all-exca  (pf "all x Q x -> (all x.Q x -> F) -> F"))
(set-goal all-exca)
(assume 1 2)
(use 2 (pt "(Inhab alpha)"))
; attempt to apply all-elim to non-total term
; (Inhab alpha)

(define all-exca  (pf "all x^ Q x^ -> (all x^.Q x^ -> F) -> F"))
(set-goal all-exca)
(assume 1 2)
(use 2 (pt "(Inhab alpha)"))
(use 1)
(dnp)

; However, search finds a proof with a free variable x^ !
(set-goal all-exca)
(search)
(dnp)

; Also cdp thinks that this proof is correct
(cdp (current-proof))

; So both have to be adapted as well.

; 2005-12-01.  Why is boole@@boole not finitary?  Answer: For finitary
; types we have recursion and induction, and this should not be
; duplicated.  Use the tensor algebra instead.

