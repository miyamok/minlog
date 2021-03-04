;; 2021-03-04.  ishihara.scm.

;; Former global assumptions (on real numbers) proved.  Estimates by
;; (1#2**p) rather than (1/2**k).  Instead of program constants
;; BanachTimes etc. (without computation rules, but assumed to be total)
;; we now use variables xSTimes etc.  Then no global assumptions on these
;; pconsts are needed, but rather premises in theorems.

;; 2017-04-21.  Based on seminars/semss13/ishihara.scm and temp/banach.scm.
;; Abstract treatment with (undefined) total program constants in type
;; xi for BanachMinus, BanachTimes and BanachNorm.  Define a partial
;; equivalence relation u~v by norm(u@-v)=0.  BanachMinus, BanachTimes
;; and BanachNorm are compatible with ~.  Instantiation consists in
;; substituting a closed type for xi and total program constants for
;; BanachMinus, BanachTimes and BanachNorm, defined by computation
;; rules.  For BanachZero we can take the generally available Inhab
;; constant, which after instantiation can defined to be the intended
;; one.  The axioms used in the present abstract treatment then need
;; to be proved.

;; 2013-09-22.  examplesanalysisishihara.scm.  Based on
;; seminars/semss13/ishihara.scm and temp/banach.scm.  Abstract
;; treatment with constants for a partial equivalence relation
;; BanachEqv (written ~) to define the Banach space in type xi and
;; constants BanachZero, BanachPlus, BanachMinus, BanachTimes
;; compatible with ~.  Instantiation consists in substituting a closed
;; type for xi and constants (not necessarily total) for BanachZero
;; BanachPlus etc defined by computation rules.  The axioms used in
;; the present abstract treatment then need to be proved.

;; @TechReport{Ishihara90a,
;;   author = 	 {Hajime Ishihara},
;;   title = 	 {A constructive closed graph theorem},
;;   institution =  {Division of Mathematical and Information Sciences,
;;     Faculty of Integrated Arts and Sciences, Hiroshima University},
;;   year = 	 1990,
;;   note = 	 {ccgt.pdf}}

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(libload "pos.scm")
(libload "int.scm")
(libload "rat.scm")
(libload "rea.scm")
;; (set! COMMENT-FLAG #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Additions to rea.scm
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; First we need some general logical facts.

;; StabCases
(set-goal "(((Pvar^2 -> F) -> F) -> Pvar^2) ->
 (Pvar^1 -> Pvar^2) -> ((Pvar^1 -> F) -> Pvar^2) -> Pvar^2")
(assume "StabHyp" "PosCase" "NegCase")
(use "StabHyp")
(assume "NotP2")
(use "NotP2")
(use "NegCase")
(assume "P1")
(use "NotP2")
(use "PosCase")
(use "P1")
;; Proof finished.
;; (cdp)
(save "StabCases")

;; ExcaElim
(set-goal "(((Pvar^ -> F) -> F) -> Pvar^) ->
 (all alpha((Pvar alpha)^ alpha -> F) -> F) ->
 all alpha((Pvar alpha)^ alpha -> Pvar^) -> Pvar^")
(assume "StabHyp" "MainPrem" "SidePrem")
(use "StabHyp")
(assume "NotP")
(use "MainPrem")
(assume "alpha" "Pa")
(use "NotP")
(use "SidePrem" (pt "alpha"))
(use "Pa")
;; Proof finished.
;; (cdp)
(save "ExcaElim")

;; StabAllImpThreeTwo
(set-goal
 "all alpha1,alpha2,alpha3(
  (((Pvar alpha1 alpha2 alpha3)^_3 alpha1 alpha2 alpha3 -> F) -> F) ->
    (Pvar alpha1 alpha2 alpha3)^_3 alpha1 alpha2 alpha3) ->
 ((all alpha1,alpha2,alpha3(
   (Pvar alpha1 alpha2 alpha3)^_1 alpha1 alpha2 alpha3 ->
   (Pvar alpha1 alpha2 alpha3)^_2 alpha1 alpha2 alpha3 ->
   (Pvar alpha1 alpha2 alpha3)^_3 alpha1 alpha2 alpha3) -> F) -> F) ->
 all alpha1,alpha2,alpha3(
  (Pvar alpha1 alpha2 alpha3)^_1 alpha1 alpha2 alpha3 ->
  (Pvar alpha1 alpha2 alpha3)^_2 alpha1 alpha2 alpha3 ->
  (Pvar alpha1 alpha2 alpha3)^_3 alpha1 alpha2 alpha3)")
(assume "StabHyp" "NotNotAllImp" "alpha1" "alpha2" "alpha3" "P1a" "P2a")
(use "StabHyp")
(assume "NotP3a")
(use "NotNotAllImp")
(assume "AllImp")
(use "NotP3a")
(use "AllImp")
(use "P1a")
(use "P2a")
;; Proof finished.
;; (cdp)
(save "StabAllImpThreeTwo")

;; StabRealNNeg
(set-goal "all x(Real x -> ((RealNNeg x -> F) -> F) -> RealNNeg x)")
(cases)
(assume "as" "M" "Rx" "NegNegHyp")
(assert "all p 0<=as(M p)+(1#2**p) -> RealNNeg(RealConstr as M)")
(assume "Hyp")
(intro 0)
(use "Rx")
(assume "p")
(assert "(RealConstr as M)seq((RealConstr as M)mod p)=as(M p)")
(ng #t)
(use "Truth")
(assume "EqHyp")
(simp "EqHyp")
(use "Hyp")
(assume "Assertion1")
(use "Assertion1")
(drop "Assertion1")
(assert "((all p 0<=as(M p)+(1#2**p) -> F) -> F) -> all p 0<=as(M p)+(1#2**p)")
(use-with "StabAll" (py "pos") (make-cterm (pv "p") (pf "0<=as(M p)+(1#2**p)"))
	  "?")
(assume "p")
(use "StabAtom")
;; Assertion proved.
(assume "StabHyp")
(use "StabHyp")
(assume "NotAllHyp")
(use "NegNegHyp")
(assume "RealNNegHyp")
(use "NotAllHyp")
(assert "RealNNeg(RealConstr as M) -> all p 0<=as(M p)+(1#2**p)")
(assume "RNNegx" "p")
(use "RealConstrNNegElim1")
(use "RNNegx")
(assume "Assertion2")
(use "Assertion2")
(drop "Assertion2")
(use "RealNNegHyp")
;; Proof finished.
;; (cdp)
(save "StabRealNNeg")

;; From StabRealNNeg we can prove StabRealLe .

;; StabRealLe
(set-goal "all x,y(Real x -> Real y -> ((x<<=y -> F) -> F) -> x<<=y)")
(assume "x" "y" "Rx" "Ry" "NotNotLeHyp")
(use "RealNNegToLe")
(autoreal)
(use "StabRealNNeg")
(autoreal)
(assume "NotNNegHyp")
(use "NotNotLeHyp")
(assume "x<=y")
(use "NotNNegHyp")
(use "RealLeToNNeg")
(use "x<=y")
;; Proof finished.
;; (cdp)
(save "StabRealLe")

;; 2021-03-03.  Done up to this point.

;; ApproxSplitBoole is used in ivt.scm as well.
;; Move ApproxSplitBoole to rea.scm

;; ApproxSplitBoole
(set-goal "all x1,x2,x3,p(Real x1 -> Real x2 -> Real x3 ->
                    RealLt x1 x2 p -> exl boole(
                    (boole -> x3<<=x2) andi ((boole -> F) -> x1<<=x3)))")
(assume "x1" "x2" "x3" "p" "Rx1" "Rx2" "Rx3" "x1<x2")
(assert "x3<<=x2 oru x1<<=x3")
 (use "ApproxSplit" (pt "p"))
 (use "Rx1")
 (use "Rx2")
 (use "Rx3")
 (use "x1<x2")
(assume "Disj")
(elim "Disj")
(drop "Disj")
(assume "x3<=x2")
(intro 0 (pt "True"))
(split)
(assume "Useless")
(use "x3<=x2")
(assume "Absurd")
(use "EfRealLe")
(use "Absurd")
(use "Truth")
;; 11
(assume "x1<=x3")
(intro 0 (pt "False"))
(split)
(assume "Absurd")
(use "EfRealLe")
(use "Absurd")
(assume "Useless")
(use "x1<=x3")
;; Proof finished.
;; (cdp)
(save "ApproxSplitBoole")

;; ApproxSplitBooleRat
(set-goal "all a,b,x,p(Real x -> (1#2**p)<=b-a -> exl boole(
                    (boole -> x<<=b) andnc ((boole -> F) -> a<<=x)))")
(assume "a" "b" "x" "p" "Rx" "(1#2**b)<=b-a")
(use "ApproxSplitBoole" (pt "p"))
(use "RealRat")
(use "RealRat")
(use "Rx")
(ng #t)
(use "(1#2**b)<=b-a")
;; Proof finished.
;; (cdp)
(save "ApproxSplitBooleRat")

;; RealLePosRatBound
(set-goal "all x,a(Real x -> 0<a -> exl n x<<=n*a)")
(assume "x")
(cases)
(cases)
;; 4-6
(assume "p" "q" "Rx" "Useless")
(drop "Useless")
;; ?_8:exl n x<<=n*(p#q)
(def "m" "cRBd(x seq)(x mod)")
;; Now use RealLeBound
(assert "x<<=2**m")
(simp "mDef")
(use "RealLeBound")
(use "Rx")
;; Assertion proved.
(assume "x<<=2**m")
;; ?_20:exl n x<<=n*(p#q)
(assert "exl n1 (2**m*q#p)<=2**n1")
(use "RatLeBound")
;; Assertion proved.
(assume "n1Ex")
(by-assume "n1Ex" "n1" "n1Prop")
(intro 0 (pt "PosToNat(2**n1)"))
(use "RealLeTrans" (pt "RealConstr([n]2**m)([p]Zero)"))
(use "x<<=2**m")
(use "RatLeToRealLe")
(ng #t)
(ng "n1Prop")
(simp "PosToNatToIntId")
(ng #t)
(use "n1Prop")
;; 5
(assume "p" "Rx" "Absurd")
(intro 0 (pt "Zero"))
(use "EfRealLe")
(use "Absurd")
;; 6
(assume "p" "q" "Rx" "Absurd")
(intro 0 (pt "Zero"))
(use "EfRealLe")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "RealLePosRatBound")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [x,a]
;;  [case a
;;    (k#p -> 
;;    [case k
;;      (p0 -> PosToNat(2**cRatLeBound(2**cRBd x seq x mod*p)p0))
;;      (0 -> Zero)
;;      (IntN p0 -> Zero)])]

;; NatRatRealLeMonTimes
(set-goal "all n,m,a,x(0<<=x -> n<=m -> a<<=x -> n*a<<=m*x)")
(assume "n" "m" "a" "x" "0<=x" "n<=m" "a<<=x")
(use "RealLeTrans" (pt "RealTimes n a"))
;; 3,4
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
;; ?^4:RealTimes n a<<=m*x
(use "RealLeTrans" (pt "n*x"))
;; 7,8
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "a<<=x")
;; 8
(use "RealLeMonTimes")
(use "0<=x")
(use "RealSeqLeToLe" (pt "Zero"))
(autoreal)
(assume "n1" "Useless")
(ng #t)
(use "NatLeToIntLe")
(use "n<=m")
;; Proof finished.
;; (cdp)
(save "NatRatRealLeMonTimes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Banach spaces
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(remove-var-name "x" "y" "z" "xs")
(add-var-name "x" (py "alpha"))
(add-var-name "xs" (py "nat=>alpha"))

(add-pvar-name "xEq" (make-arity (py "alpha") (py "alpha")))
(add-var-name "xPlus" (py "alpha=>alpha=>alpha"))
(add-var-name "xUMinus" (py "alpha=>alpha"))
(add-var-name "xSTimes" (py "rea=>alpha=>alpha"))
(add-var-name "xNorm" (py "alpha=>rea"))
(add-var-name "xLim" (py "(nat=>alpha)=>(pos=>nat)=>alpha"))

(pp (pf "xEq x1 x2"))
(pp (pt "xPlus x1 x2"))
(pp (pt "xUMinus x"))
(pp (pt "xSTimes rea x"))
(pp (pt "xNorm x"))
(pp (pt "xLim xs M"))

(pp (pt "xSTimes n x"))

;; The predicate xB defines membership in the Banachspace X of objects
;; of type alpha.

(add-pvar-name "xB" (make-arity (py "alpha")))

;; The relation xEq^ has xBd as its domain.

;; xEqBLeft
(pp (pf "all x1,x2(xEq^ x1 x2 -> xB^ x1)"))

;; xEqBRight
(pp (pf "all x1,x2(xEq^ x1 x2 -> xB^ x2)"))

;; xEq is an equivalence relation on xB

;; xEqRefl
(pp (pf "all x(xB^ x -> xEq^ x x)"))

;; xEqSym
(pp (pf "all x1,x2(xEq^ x1 x2 -> xEq^ x2 x1)"))

;; xEqTrans
(pp (pf "all x1,x2,x3(xEq^ x1 x2 -> xEq^ x2 x3 -> xEq^ x1 x3)"))

;; The functions xPlus xUMinus xSTimes xNorm xLim are compatible with xEq

;; xPlusCompat
(pp (pf "all x1,x2,x3,x4(xEq^ x1 x2 -> xEq^ x3 x4 ->
 xEq^(xPlus x1 x3) (xPlus x2 x4))"))

;; xUMinusCompat
(pp (pf "all x1,x2(xEq^ x1 x2 -> xEq^(xUMinus x1)(xUMinus x2))"))

;; xSTimesCompat
(pp (pf "all rea1,rea2,x1,x2(rea1===rea2 ->
 xEq^ x1 x2 -> xEq^(xSTimes rea1 x1)(xSTimes rea2 x2))")) 

;; xNormCompat
(pp (pf "all x1,x2(xEq^ x1 x2 -> xNorm x1===xNorm x2)"))

;; xLimCompat
(pp (pf "all xs1,xs2,M(all n xEq^(xs1 n)(xs2 n) ->
 xEq^(xLim xs1 M)(xLim xs2 M))"))

;; Closure properties

;; xPlus maps xB arguments in xB
(pp (pf "all x1,x2(xB^ x1 -> xB^ x2 -> xB^(xPlus x1 x2))"))

;; xUMinus maps xB^ arguments in xB
(pp (pf "all x(xB^ x -> xB^(xUMinus x))"))

;; xSTimes maps reals and xB^ into xB
(pp (pf "all rea,x(Real rea -> xB^ x -> xB^(xSTimes rea x))"))

;; xNorm maps xB^ into Real
;; RealxNorm
(pp (pf "all x(xB^ x -> Real(xNorm x))"))

;; xLim maps sequences of xB objects and moduli into xB
(pp (pf "all xs,M(all n xB^(xs n) -> xB^(xLim xs M))"))

;; The first three are provable from compatibility and xEqRefl.

;; Inhab axioms

;; InhabBanach
(add-global-assumption
 "InhabBanach"
 "Total(Inhab alpha)")

(remove-global-assumption "InhabBanach")

(pp (pf "xB^(Inhab alpha)"))

;; Group axioms

;; xPlusAssoc
(pp (pf "all x1,x2,x3(xB^ x1 -> xB^ x2 -> xB^ x3 ->
 xEq^(xPlus(xPlus x1 x2)x3)(xPlus x1(xPlus x2 x3)))"))

;; xPlusNeutralLeft
(pp (pf "all x(xB^ x ->  xEq^(xPlus(Inhab alpha)x)x)"))

;; xPlusUMinusLeft
(pp (pf "all x(xB^ x -> xEq^(xPlus(xUMinus x)x)(Inhab alpha))"))

;; xPlusComm
(pp (pf "all x1,x2(xB^ x1 -> xB^ x2 -> xEq^(xPlus x1 x2)(xPlus x2 x1))"))

;; Derived properties.  The proofs can be simplified by first proving
;; some rewrite rules.

;; LeftUMinusRightUMinus
;; LeftNeutralRightNeutral
;; NeutralUnique
;; UMinusUnique
;; NeutralCrit

;; Linear space axioms

;; xSTimesDistrLeft
(pp (pf "all rea1,rea2,x(Real rea1 -> Real rea2 -> xB^ x ->
 xEq^(xSTimes(rea1+rea2)x)(xPlus(xSTimes rea1 x)(xSTimes rea2 x)))"))

;; xSTimesDistrRight
(pp (pf "all rea,x1,x2(Real rea -> xB^ x1 -> xB^ x2 ->
 xEq^(xSTimes rea(xPlus x1 x2))(xPlus(xSTimes rea x1)(xSTimes rea x2)))"))

;; xSTimesAssoc
(pp (pf "all rea1,rea2,x(Real rea1 -> Real rea2 -> xB^ x ->
 xEq^(xSTimes rea1(xSTimes rea2 x))(xSTimes(rea1*rea2)x))"))

;; xSTimesOne
(pp (pf "all x(xB^ x -> xEq^(xSTimes 1 x)x)"))

;; Norm axioms

;; RealNNegxNorm
;; BanachNormNNeg
(pp (pf "all x(xB^ x -> RealNNeg(xNorm x))"))

;; xNormSTimes
;; BanachNormTimes
(pp (pf "all rea,x(Real rea -> xB^ x ->
 xNorm(xSTimes rea x)===abs rea*xNorm x)"))

;; Triangle inequality
(pp (pf "all x1,x2(xB^ x1 -> xB^ x2 -> xNorm(xPlus x1 x2)<<=xNorm x1+xNorm x2)"))

;; Then one can derive
(pp (pf "xNorm(Inhab alpha)===0"))
(pp (pf "all x(xB^ x -> xNorm(xUMinus x)===xNorm x)"))

;; Completeness axiom for Banach spaces.

(pp (pf "all xs,M(
 all n xB^(xs n) ->
 all p,n,m(M p<=n -> n<m -> xNorm(xPlus(xs n)(xUMinus(xs m)))<<=(1#2**p)) ->
 all p,n(M p<=n -> xNorm(xPlus(xLim xs M)(xUMinus(xs n)))<<=(1#2**p)))"))

;; We do the same for the normed linear space of values y

(add-var-name "y" (py "beta"))

(add-pvar-name "yEq" (make-arity (py "beta") (py "beta")))
(add-var-name "yPlus" (py "beta=>beta=>beta"))
(add-var-name "yUMinus" (py "beta=>beta"))
(add-var-name "ySTimes" (py "rea=>beta=>beta"))
(add-var-name "yNorm" (py "beta=>rea"))

(pp (pf "yEq^ y1 y2"))
(pp (pt "yPlus y1 y2"))
(pp (pt "yUMinus y"))
(pp (pt "ySTimes rea y"))
(pp (pt "yNorm y"))

(pp (pt "ySTimes n y"))

;; The predicate yN defines membership in the normed linear space Y of
;; objects of type beta.

(add-pvar-name "yN" (make-arity (py "beta")))

;; The relation yEq^ has yNd as its domain.

;; yEqBLeft
(pp (pf "all y1,y2(yEq^ y1 y2 -> yN^ y1)"))

;; yEqBRight
(pp (pf "all y1,y2(yEq^ y1 y2 -> yN^ y2)"))

;; yEq^ is an equivalence relation on yN

;; yEqRefl
(pp (pf "all y(yN^ y -> yEq^ y y)"))

;; yEqSym
(pp (pf "all y1,y2(yEq^ y1 y2 -> yEq^ y2 y1)"))

;; yEqTrans
(pp (pf "all y1,y2,y3(yEq^ y1 y2 -> yEq^ y2 y3 -> yEq^ y1 y3)"))

;; The functions yPlus yUMinud ySTimes yNorm yLim are compatible with yEq

;; yPlusCompat
(pp (pf "all y1,y2,y3,y4(yEq^ y1 y2 -> yEq^ y3 y4 ->
 yEq^(yPlus y1 y3) (yPlus y2 y4))"))

;; yUMinusCompat
(pp (pf "all y1,y2(yEq^ y1 y2 -> yEq^(yUMinus y1)(yUMinus y2))"))

;; ySTimesCompat
(pp (pf "all rea1,rea2,y1,y2(rea1===rea2 ->
 yEq^ y1 y2 -> yEq^(ySTimes rea1 y1)(ySTimes rea2 y2))")) 

;; yNormCompat
(pp (pf "all y1,y2(yEq^ y1 y2 -> yNorm y1===yNorm y2)"))

;; Closure properties

;; yPlus maps yN arguments in yN
(pp (pf "all y1,y2(yN^ y1 -> yN^ y2 -> yN^(yPlus y1 y2))"))

;; yUMinus maps yN arguments in yN
(pp (pf "all y(yN^ y -> yN^(yUMinus y))"))

;; ySTimes maps reals and yN^ into yN
(pp (pf "all rea,y(Real rea -> yN^ y -> yN^(ySTimes rea y))"))

;; yNorm maps yN^ into Real
(pp (pf "all y(yN^ y -> Real(yNorm y))"))

;; These three are proveble from compatibility and yEqRef.

;; Inhab axioms

(pp (pf "Total(Inhab beta)"))

(pp (pf "yN^(Inhab beta)"))

;; Group axioms

;; yPlusAssoc
(pp (pf "all y1,y2,y3(yN^ y1 -> yN^ y2 -> yN^ y3 ->
 yEq^(yPlus(yPlus y1 y2)y3)(yPlus y1(yPlus y2 y3)))"))

;; yPlusNeutralLeft
(pp (pf "all y(yN^ y ->  yEq^(yPlus(Inhab beta)y)y)"))

;; yPlusUMinusLeft
(pp (pf "all y(yN^ y -> yEq^(yPlus(yUMinus y)y)(Inhab beta))"))

;; yPlusComm
(pp (pf "all y1,y2(yN^ y1 -> yN^ y2 -> yEq^(yPlus y1 y2)(yPlus y2 y1))"))

;; Derived properties.  The proofs can be simplified by first proving
;; some rewrite rules.

;; LeftUMinusRightUMinus
;; LeftNeutralRightNeutral
;; NeutralUnique
;; UMinusUnique
;; NeutralCrit

;; Linear space axioms

;; ySTimesDistrLeft
(pp (pf "all rea1,rea2,y(Real rea1 -> Real rea2 -> yN^ y ->
 yEq^(ySTimes(rea1+rea2)y)(yPlus(ySTimes rea1 y)(ySTimes rea2 y)))"))

;; ySTimesDistrRight
(pp (pf "all rea,y1,y2(Real rea -> yN^ y1 -> yN^ y2 ->
 yEq^(ySTimes rea(yPlus y1 y2))(yPlus(ySTimes rea y1)(ySTimes rea y2)))"))

;; ySTimesAssoc
(pp (pf "all rea1,rea2,y(Real rea1 -> Real rea2 -> yN^ y ->
 yEq^(ySTimes rea1(ySTimes rea2 y))(ySTimes(rea1*rea2)y))"))

;; ySTimesOne
(pp (pf "all y(yN^ y -> yEq^(ySTimes 1 y)y)"))

;; Norm axioms

;; RealNNegyNorm
(pp (pf "all y(yN^ y -> RealNNeg(yNorm y))"))

;; yNormSTimes
(pp (pf "all rea,y(Real rea -> yN^ y ->
 yNorm(ySTimes rea y)===abs rea*yNorm y)"))

;; Triangle inequality
(pp (pf "all y1,y2(yN^ y1 -> yN^ y2 -> yNorm(yPlus y1 y2)<<=yNorm y1+yNorm y2)"))

;; Then one can derive
(pp (pf "yNorm(Inhab beta)===0"))
(pp (pf "all y(yN^ y -> yNorm(yUMinus y)===yNorm y)"))

(add-var-name "f" (py "alpha=>beta"))

;; fCompat
(pp (pf "all x1,x2(xEq^ x1 x2 -> yEq^(f x1)(f x2))"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-var-name "K" (py "nat=>nat"))

(add-var-name "g" (py "nat=>boole"))
(add-var-name "h" (py "nat=>nat"))

(add-program-constant "Hit" (py "nat=>nat=>nat"))

(add-computation-rules
 "Hit m n" "[if (m<n) (m+2) Zero]")

;; HitTotal
(set-totality-goal "Hit")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "m")
(ng #t)
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

(add-program-constant "HitHere" (py "(nat=>boole)=>nat=>nat=>nat"))

(add-computation-rules
 "HitHere g n0 n1" "Hit(NatLeastUp n0 n1 g)n1")

;; HitHereTotal
(set-totality-goal "HitHere")
(fold-alltotal)
(assume "g")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "m")
(ng #t)
(use "NatTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant
 "HitPast" (py "(nat=>boole)=>(nat=>nat)=>nat=>nat=>nat"))

(add-computation-rules
 "HitPast g K n0 n" "[if (NatLeast n0 g<n0) (Succ Zero)
                         (HitHere g n0(K(Succ n)))]")

;; HitPastTotal
(set-totality-goal "HitPast")
(fold-alltotal)
(assume "g")
(fold-alltotal)
(assume "K")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "m")
(ng #t)
(use "NatTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant "H" (py "(nat=>boole)=>(nat=>nat)=>nat=>nat"))

(add-computation-rules "H g K n" "HitPast g K(K n)n")

;; HTotal
(set-totality-goal "H")
(fold-alltotal)
(assume "g")
(fold-alltotal)
(assume "K")
(fold-alltotal)
(assume "n")
(ng #t)
(use "NatTotalVar")
;; Proof finished.
(save-totality)

;; We prove properties of H that will be needed in the proof of
;; Ishihara's trick.

;; HDef
(set-goal "all g,K,n H g K n=HitPast g K(K n)n")
(strip)
(use "Truth")
;; Proof finished.
(save "HDef")

;; HitPastDef
(set-goal "all g,K,n0,n HitPast g K n0 n=
 [if (NatLeast n0 g<n0) (Succ Zero) (HitHere g n0(K(Succ n)))]")
(strip)
(use "Truth")
;; Proof finished.
(save "HitPastDef")

;; HitPastDef1
(set-goal  "all g,K,n0,n(NatLeast n0 g<n0 -> HitPast g K n0 n=Succ Zero)")
(assume "g" "K" "n0" "n" "m<n")
(ng #t)
(simp "m<n")
(ng #t)
(use "Truth")
;; Proof finished.
(save "HitPastDef1")

;; HitHereDef
(set-goal "all g,n0,n1 HitHere g n0 n1=Hit(NatLeastUp n0 n1 g)n1")
(strip)
(ng #t)
(use "Truth")
;; Proof finished.
(save "HitHereDef")

;; HitDef
(set-goal "all m,n Hit m n=[if (m<n) (m+2) Zero]")
(strip)
(use "Truth")
;; Proof finished.
(save "HitDef")

;; HitPastDef1Cor
(set-goal "all g,K,n0,n(HitPast g K n0 n=Zero -> n0<=NatLeast n0 g)")
(assume "g" "K" "n0" "n" "hn=0")
(use "NatNotLtToLe")
(assume "m<n0")
(assert "HitPast g K n0 n=Succ Zero")
 (use "HitPastDef1")
 (use "m<n0")
(assume "hn=1")
(simphyp-with-to "hn=1" "hn=0" "Absurd")
(use "Absurd")
;; Proof finished.
(save "HitPastDef1Cor")

;; HProp01
(set-goal "all g,K,n(H g K n=Zero -> K n<=NatLeast(K n)g)")
(assume "g" "K" "n")
(simp "HDef")
(assume "hn=0")
(use "HitPastDef1Cor" (pt "K") (pt "n"))
(use "hn=0")
;; Proof finished.
(save "HProp01")

;; HProp01Cor
(set-goal "all g,K,n,m(H g K n=Zero -> m<K n -> g m -> F)")
(assume "g" "K" "n" "m" "hn=0")
(assert "K n=NatLeast(K n)g")
 (use "NatLeAntiSym")
 (use "HProp01")
 (use "hn=0")
 (use "NatLeastBound")
(assume "EqHyp")
(simp "EqHyp")
(assume "m<NatLeast(K n)g" "gm")
(assert "m<m")
 (use "NatLtLeTrans" (pt "NatLeast(K n)g"))
 (use "m<NatLeast(K n)g")
 (use "NatLeastLeIntro")
 (use "gm")
(assume "m<m")
(use "m<m")
;; Proof finished.
(save "HProp01Cor")

;; HProp02
(set-goal "all g,K,n(H g K n=Zero -> K(Succ n)<=NatLeastUp(K n)(K(Succ n))g)")
(assume "g" "K" "n")
(simp "HDef")
(simp "HitPastDef")
(cases (pt "NatLeast(K n)g<K n"))
(assume "Useless")
(ng #t)
(use "Efq")
(simp "HitHereDef")
(simp "HitDef")
(cases (pt "NatLeastUp(K n)(K(Succ n))g<K(Succ n)"))
(assume "Useless1" "Useless2")
(ng #t)
(use "Efq")
(assume "NatLeastUp(K n)(K(Succ n))g<K(Succ n) -> F" "Useless1" "Useless2")
(use "NatNotLtToLe")
(use "NatLeastUp(K n)(K(Succ n))g<K(Succ n) -> F")
;; Proof finished.
(save "HProp02")

;; HProp02Cor
(set-goal "all g,K,n,m(H g K n=Zero -> K n<=m -> m<K(Succ n) -> g m -> F)")
(assume "g" "K" "n" "m" "hn=0")
(assert "K(Succ n)=NatLeastUp(K n)(K(Succ n))g")
 (use "NatLeAntiSym")
 (use "HProp02")
 (use "hn=0")
 (use "NatLeastUpBound")
(assume "EqHyp")
(simp "EqHyp")
(assume "K n<=m" "m<NatLeastUp(K n)(K(Succ n))g" "gm")
(assert "m<m")
 (use "NatLtLeTrans" (pt "NatLeastUp(K n)(K(Succ n))g"))
 (use "m<NatLeastUp(K n)(K(Succ n))g")
 (use "NatLeastUpLeIntro")
 (use "K n<=m")
 (use "gm")
(assume "m<m")
(use "m<m")
;; Proof finished.
(save "HProp02Cor")

;; HProp0Cor
(set-goal "all g,K,n,m(H g K n=Zero -> m<K(Succ n) -> g m -> F)")
(assume "g" "K" "n" "m" "hn=0")
(use "NatLeLtCases" (pt "K n") (pt "m"))
(use "HProp02Cor")
(use "hn=0")
(assume "m<K n" "Useless")
(use "HProp01Cor" (pt "K") (pt "n"))
(use "hn=0")
(use "m<K n")
;; Proof finished.
(save "HProp0Cor")

;; HProp22
(set-goal "all g,K,n,m(H g K n=Succ(Succ m) ->
 NatLeastUp(K n)(K(Succ n))g<K(Succ n))")
(assume "g" "K" "n" "m")
(simp "HDef")
(simp "HitPastDef")
(cases (pt "NatLeast(K n)g<K n"))
(assume "Useless")
(ng #t)
(use "Efq")
(assume "NatLeast(K n)g<K n -> F")
(simp "HitHereDef")
(simp "HitDef")
(cases (pt "NatLeastUp(K n)(K(Succ n))g<K(Succ n)"))
(strip)
(use "Truth")
(assume "NatLeastUp(K n)(K(Succ n))g<K(Succ n) -> F")
(ng #t)
(use "Efq")
;; Proof finished.
(save "HProp22")

;; HProp1
(set-goal "all g,K,n(H g K n=Succ Zero -> NatLeast(K n)g<K n)")
(assume "g" "K" "n")
(simp "HDef")
(simp "HitPastDef")
(cases (pt "NatLeast(K n)g<K n"))
(strip)
(use "Truth")
(assume "NatLeast(K n)g<K n -> F")
(simp "HitHereDef")
(simp "HitDef")
(cases (pt "NatLeastUp(K n)(K(Succ n))g<K(Succ n)"))
(ng #t)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "NatLeastUp(K n)(K(Succ n))g<K(Succ n) -> F")
(ng #t)
(use "Efq")
;; Proof finished.
(save "HProp1")

;; H0Down
(set-goal "all g,K,n,n1(H g K n=Zero -> K n1<=K(Succ n) -> K n1<=K(Succ n1) ->
 K(Succ n1)<=K(Succ n) -> H g K n1=Zero)")
(assume "g" "K" "n" "n1" "hn=0" "K n1<=K(Succ n)" "K n1<=K(Succ n1)"
	"K(Succ n1)<=K(Succ n)")
(cases (pt "H g K n1"))
(strip)
(use "Truth")
(cases) ;6,7
(assume "hn1=1")
(assert "NatLeast(K n1)g<K n1")
 (use "HProp1")
 (use "hn1=1")
(assume "HitLtKn1")
(assert "g(NatLeast(K n1)g)")
 (use "NatLeastLtElim")
 (use "HitLtKn1")
(use "HProp0Cor" (pt "K") (pt "n"))
(use "hn=0")
(use "NatLtLeTrans" (pt "K n1"))
(use "HitLtKn1")
(use "K n1<=K(Succ n)")
;; 7
(assume "m" "hn1=m+2")
(assert "NatLeastUp(K n1)(K(Succ n1))g<K(Succ n1)")
 (use "HProp22" (pt "m"))
 (use "hn1=m+2")
(assume "NatLeastUp(K n1)(K(Succ n1))g<K(Succ n1)")
(assert "g(NatLeastUp(K n1)(K(Succ n1))g)")
 (use "NatLeastUpLtElim")
 (use "NatLeastUpLBound")
 (use "K n1<=K(Succ n1)")
 (use "NatLeastUp(K n1)(K(Succ n1))g<K(Succ n1)")
(use-with "HProp0Cor" (pt "g") (pt "K") (pt "n")
	  (pt "NatLeastUp(K n1)(K(Succ n1))g") "hn=0" "?")
(use "NatLtLeTrans" (pt "K(Succ n1)"))
(use "NatLeastUp(K n1)(K(Succ n1))g<K(Succ n1)")
(use "K(Succ n1)<=K(Succ n)")
;; Proof finished.
(save "H0Down")

;; H0DownMon
(set-goal "all g,K,n,n1(all n,m(n<=m -> K n<=K m) ->
 H g K n=Zero -> n1<=n -> H g K n1=Zero)")
(assume "g" "K" "n" "n1" "KMon" "hn=0" "n1<=n")
(use "H0Down" (pt "n"))
(use "hn=0")
(use "KMon")
(use "NatLeTrans" (pt "n"))
(use "n1<=n")
(use "Truth")
(use "KMon")
(use "Truth")
(use "KMon")
(use "n1<=n")
;; Proof finished.
(save "H0DownMon")

;; H1Down
(set-goal "all g,K,n(H g K(Succ n)=Succ Zero -> H g K n=Zero -> F)")
(assume "g" "K" "n" "h(n+1)=1" "hn=0")
(assert "NatLeast(K(Succ n))g<K(Succ n)")
 (use "HProp1")
 (use "h(n+1)=1")
(assume "NatLeast(K(Succ n))g<K(Succ n)")
(assert "g(NatLeast(K(Succ n))g)")
 (use "NatLeastLtElim")
 (use "NatLeast(K(Succ n))g<K(Succ n)")
 (use-with "HProp0Cor" (pt "g") (pt "K") (pt "n")
	   (pt "NatLeast(K(Succ n))g") "hn=0" "?")
(use "NatLeast(K(Succ n))g<K(Succ n)")
;; Proof finished.
(save "H1Down")

;; HFind
(set-goal "all g,K,n(
 K Zero=Zero -> (H g K n=Zero -> F) -> exd n1 exl m(n1<=n andnc H g K n1=m+2))")
(assume "g" "K")
(ind) ;3,4
(assume "K0=0" "0<h0")
(assert "H g K Zero=Succ Zero -> F")
(assume "h0=1")
(assert "NatLeast(K Zero)g<K Zero")
(use "HProp1")
(use "h0=1")
(simp "K0=0")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "H g K Zero=Succ Zero -> F")
(intro 0 (pt "Zero"))
(intro 0 (pt "H g K Zero--Succ(Succ Zero)"))
(split)
(use "Truth")
(assert "all n((n=Zero -> F) -> (n=Succ(Zero) -> F) ->
  n=n--Succ(Succ Zero)+Succ(Succ Zero))")
(cases)
(assume "Absurd" "Useless")
 (use "EfAtom")
(use "Absurd")
(use "Truth")
(cases)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(use "Truth")
(ng #t)
(strip)
(use "Truth")
;; Assertion proved.
(assume "Assertion")
(use-with "Assertion" (pt "H g K Zero") "?" "?")
(use "0<h0")
(use "H g K Zero=Succ Zero -> F")
;; 4
(assume "n" "IH" "K0=0" "0<h(n+1)")
(cases (pt "H g K n"))
;; 37,38
(assume "hn=0")
(intro 0 (pt "Succ n"))
(intro 0 (pt "H g K(Succ n)--Succ(Succ Zero)"))
(split)
(use "Truth")
(assert "all n((n=Zero -> F) -> (n=Succ(Zero) -> F) ->
  n=n--Succ(Succ Zero)+Succ(Succ Zero))")
(cases)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(use "Truth")
(cases)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(use "Truth")
(ng #t)
(strip)
(use "Truth")
;; Assertion proved.
(assume "Assertion")
(use-with "Assertion" (pt "H g K(Succ n)") "?" "?")
(use "0<h(n+1)")
(assume "h(n+1)=1")
(use-with "H1Down" (pt "g") (pt "K") (pt "n") "h(n+1)=1" "hn=0")
;; 38
(assume "n1" "hn=n1+1")
(assert "H g K n=Zero -> F")
(simp "hn=n1+1")
(assume "Absurd")
(use "Absurd")
(assume "0<hn")
(inst-with-to "IH" "K0=0" "0<hn" "IHInst")
(drop "IH")
(by-assume "IHInst" "n0" "n0Prop")
(intro 0 (pt "n0"))
(by-assume "n0Prop" "m" "mProp")
(intro 0 (pt "m"))
(split)
(use "NatLeTrans" (pt "n"))
(use "mProp")
(use "Truth")
(use "mProp")
;; Proof finished.
;; (cdp)
(save "HFind")

(define eterm (proof-to-extracted-term))
(remove-computation-rules-for (pt "H g K n"))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [g,K,n]
;;  (Rec nat=>nat yprod nat)n(Zero pair Pred(Pred(H g K Zero)))
;;  ([n0,(nat yprod nat)]
;;    [case (H g K n0)
;;      (Zero -> Succ n0 pair Pred(Pred(H g K(Succ n0))))
;;      (Succ n1 -> (nat yprod nat))])

(add-computation-rules "H g K n" "HitPast g K(K n)n")

;; Further properties of H.

;; HProp2Cor
(set-goal "all g,K,n,m(H g K n=Succ(Succ m) -> K n<=K(Succ n) ->
 g(NatLeastUp(K n)(K(Succ n))g))")
(assume "g" "K" "n" "m" "hn=m+2" "Kn<=K(n+1)")
(use "NatLeastUpLtElim")
(use "NatLeastUpLBound")
(use "Kn<=K(n+1)")
(use "HProp22" (pt "m"))
(use "hn=m+2")
;; Proof finished.
(save "HProp2Cor")

;; HProp2Val
(set-goal "all g,K,n,m(H g K n=Succ(Succ m) -> NatLeastUp(K n)(K(Succ n))g=m)")
(assume "g" "K" "n" "m")
(simp "HDef")
(simp "HitPastDef")
(simp "HitHereDef")
(cases (pt "NatLeast(K n)g<K n"))
(assume "Useless")
(ng #t)
(use "Efq")
(assume "Useless")
(simp "HitDef")
(cases (pt "(NatLeastUp(K n)(K(Succ n))g<K(Succ n))"))
(assume "Useless1" "Hyp")
(use "Hyp")
(assume "Useless1")
(ng #t)
(use "Efq")
;; Proof finished.
(save "HProp2Val")

;; HProp2gVal
(set-goal "all g,K,n,m(H g K n=Succ(Succ m) -> K n<=K(Succ n) -> g m)")
(assume "g" "K" "n" "m" "hn=m+2" "Kn<=K(n+1)")
(simp "<-" "HProp2Val" (pt "g") (pt "K") (pt "n"))
(use "HProp2Cor" (pt "m"))
(use "hn=m+2")
(use "Kn<=K(n+1)")
(use "hn=m+2")
;; Proof finished.
(save "HProp2gVal")

;; H2Succ
(set-goal "all g,K,n,m(H g K n=Succ(Succ m) -> all n,m(n<=m -> K n<=K m) ->
 H g K(Succ n)=Succ Zero)")
(assume "g" "K" "n" "m" "hn=m+2" "KMon")
(assert "g(NatLeastUp(K n)(K(Succ n))g)")
 (use "HProp2Cor" (pt "m"))
 (use "hn=m+2")
 (use "KMon")
 (use "Truth")
(assume "gInst")
(assert "NatLeastUp Zero(K(Succ n))g<=NatLeastUp(K n)(K(Succ n))g")
 (use "NatLeastUpLeIntro")
 (use "Truth")
 (use "gInst")
 (simp "NatLeastUpZero")
(assume "LeHyp")
(assert "NatLeast(K(Succ n))g<K(Succ n)")
 (use "NatLeLtTrans" (pt "NatLeastUp(K n)(K(Succ n))g"))
 (use "LeHyp")
 (use "HProp22" (pt "m"))
 (use "hn=m+2")
(assume "LtHyp")
(assert "H g K(Succ n)=HitPast g K(K(Succ n))(Succ n)")
 (simp "HDef")
 (use "Truth")
(assume "EqHyp")
(simp "EqHyp")
(use "HitPastDef1")
(use "LtHyp")
;; Proof finished.
(save "H2Succ")

;; H1Succ
(set-goal "all g,K,n(H g K n=Succ Zero -> all n,m(n<=m -> K n<=K m) ->
 H g K(Succ n)=Succ Zero)")
(assume "g" "K" "n" "hn=1" "KMon")
(assert "NatLeast(K n)g<K n")
 (use "HProp1")
 (use "hn=1")
(assume "LtHyp")
(assert "g(NatLeast(K n)g)")
 (use "NatLeastLtElim")
 (use "LtHyp")
(assume "gInst")
(assert "NatLeast(K(Succ n))g<K(Succ n)")
 (use "NatLeLtTrans" (pt "NatLeast(K n)g"))
 (use "NatLeastLeIntro")
 (use "gInst")
 (use "NatLtLeTrans" (pt "K n"))
 (use "LtHyp")
 (use "KMon")
 (use "Truth")
(assume "LtHypSucc")
(assert "H g K(Succ n)=HitPast g K(K(Succ n))(Succ n)")
 (simp "HDef")
 (use "Truth")
(assume "EqHyp")
(simp "EqHyp")
(use "HitPastDef1")
(use "LtHypSucc")
;; Proof finished.
(save "H1Succ")

;; H2Up
(set-goal "all g,K,n,m(
 H g K n=Succ(Succ m) -> all n,m(n<=m -> K n<=K m) ->
 all n1 H g K(Succ(n+n1))=Succ Zero)")
(assume "g" "K" "n" "m" "hn=m+2" "KMon")
(ind)
(use "H2Succ" (pt "m"))
(use "hn=m+2")
(use "KMon")
(assume "n1" "IH")
(use "H1Succ")
(use "IH")
(use "KMon")
;; Proof finished.
(save "H2Up")

;; H2Down
(set-goal "all g,K,n,m(
 H g K(Succ n)=Succ(Succ m) -> all n,m(n<=m -> K n<=K m) -> H g K n=Zero)")
(assume "g" "K" "n" "m" "hSn=SSm" "KMon")
(cases (pt "H g K n"))
(strip)
(use "Truth")
(cases)
(assume "hn=1")
(assert "H g K(Succ n)=Succ Zero")
 (use "H1Succ")
 (use "hn=1")
 (use "KMon")
(simp "hSn=SSm")
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "m1" "hn=SSm1")
(assert "H g K(Succ n)=Succ Zero")
 (use "H2Succ" (pt "m1"))
 (use "hn=SSm1")
 (use "KMon")
(simp "hSn=SSm")
(ng #t)
(assume "Absurd")
(use "Absurd")
;; Proof finished.
(save "H2Down")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (V alpha)g K xs n is defined via H and the auxiliary function Seq below,
;; by (Seq alpha)(H g K)(H g K n)xs n.  We define Seq by
;; (Seq alpha)h 0 xs n = 0
;; (Seq alpha)h(Succ(Succ m))xs n = xSTimes n(xs m)
;; (Seq alpha)h(Succ Zero)xs Zero = 0
;; (Seq alpha)h(Succ Zero)xs(Succ n) = (Seq alpha)h(h n)xs n

(add-global-assumption "InhabBanach" "Total(Inhab alpha)")
;; This global assumption is necessary to have Seq and V as total
;; objects.  When substituting alpha by the type tau of the objects in
;; the intended Banach space we must know that tau is inhabited.

(add-program-constant
 "Seq" (py "(rea=>alpha=>alpha)=>(nat=>nat)=>nat=>(nat=>alpha)=>nat=>alpha"))

;; (remove-program-constant "Seq")

(add-computation-rules
 "(Seq alpha)xSTimes h Zero xs n" "(Inhab alpha)"
 "(Seq alpha)xSTimes h(Succ(Succ m))xs n" "xSTimes n(xs m)"
 "(Seq alpha)xSTimes h(Succ Zero)xs Zero" "(Inhab alpha)"
 "(Seq alpha)xSTimes h(Succ Zero)xs(Succ n)" "(Seq alpha)xSTimes h(h n)xs n")

;; SeqTotal
(set-totality-goal "Seq")
(assume "xSTimes^" "TxSTimes")
(fold-alltotal)
(assume "h")
(assert "allnc xs^(all n Total(xs^ n) ->
 all n,m Total((Seq alpha)xSTimes^ h m xs^ n))")
(assume "xs^" "Txs")
(ind)
;; 8,9
;; Base
(cases)
(ng #t)
(use "InhabBanach")
(cases)
(use "InhabBanach")
(assume "m")
(ng #t)
(use "TxSTimes")
(use "TotalReaRealConstr")
(fold-alltotal)
(assume "n0")
(use "RatTotalVar")
(fold-alltotal)
(assume "p")
(use "NatTotalVar")
(use "Txs")
;; 9
;; Step
(assume "n" "IHn")
(cases)
(ng #t)
(use "InhabBanach")
(cases)
(ng #t)
(use "IHn")
(assume "m")
(ng #t)
(use "TxSTimes")
(use "ReaTotalVar")
(use "Txs")
;; 5
;; Assertion proved
(assume "SeqTotalAux")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "xs")
(fold-alltotal)
(assume "m")
(use "SeqTotalAux")
(assume "n1")
(use "TotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; For later use we  show that all Seq values are in xB^

(display-pconst "Seq")

;; SeqB
(set-goal "all xSTimes,h,xs(
 xB^(Inhab alpha) ->
 all n xB^(xs n) ->
 all rea,x(Real rea -> xB^ x -> xB^(xSTimes rea x)) ->
 all n,m(xB^((Seq alpha)xSTimes h m xs n)))")
(assume "xSTimes" "h" "xs" "InhB" "xsB" "BanachxSTimes")
(ind)
;; 3,4
(cases)
(ng #t)
(use "InhB")
(cases)
(ng #t)
(use "InhB")
(assume "m")
(ng #t)
(use "BanachxSTimes")
(use "RealRat")
(use "xsB")
;; 4
(assume "n" "IHn")
(cases)
(ng #t)
(use "InhB")
(cases)
(ng #t)
(use "IHn")
(ng #t)
(assume "m")
(use "BanachxSTimes")
(use "RealRat")
(use "xsB")
;; Proof finished.
;; (cdp)
(save "SeqB")

(add-program-constant
 "V"
 (py "(rea=>alpha=>alpha)=>(nat=>boole)=>(nat=>nat)=>(nat=>alpha)=>nat=>alpha"))

;; (remove-program-constant "V")

(add-computation-rules
 "(V alpha)xSTimes g K xs n" "(Seq alpha)xSTimes(H g K)(H g K n)xs n")

;; VTotal
(set-totality-goal "V")
(assume "xSTimes^" "TxSTimes" "g^" "Tg" "K^" "TK" "xs^" "Txs")
(use "AllTotalElim")
(assume "n")
(use "SeqTotal")
;; 5-8
(use "TxSTimes")
;; 6
(use "HTotal")
(use "Tg")
(use "TK")
;; 7
(use "HTotal")
(use "Tg")
(use "TK")
(use "NatTotalVar")
;; 7
(use "Txs")
;; 8
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; VB
(set-goal "all xSTimes,g,K,xs(
 xB^(Inhab alpha) ->
 all n xB^(xs n) ->
 all rea,x(Real rea -> xB^ x -> xB^(xSTimes rea x)) ->
 all n xB^((V alpha)xSTimes g K xs n))")
(assume "xSTimes" "g" "K" "xs" "InhB" "xsB" "BanachxSTimes" "n")
(use "SeqB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
;; Proof finished.
;; (cdp)
(save "VB")

;; To avoid normalization which leads to unfolding of H (and then
;; HitPast etc) we prove defining equations for V and Seq

;; VDef
(set-goal "allnc xSTimes^,g^,K^,xs^,n^(
 V alpha)xSTimes^ g^ K^ xs^ n^ eqd
 (Seq alpha)xSTimes^(H g^ K^)(H g^ K^ n^)xs^ n^")
(strip)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "VDef")

;; SeqDef2
(set-goal
 "allnc xSTimes^,h^,m^,xs^,n^(
 Seq alpha)xSTimes^ h^(Succ(Succ m^))xs^ n^ eqd xSTimes^ n^(xs^ m^)")
(strip)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "SeqDef2")

;; VIfH0
(set-goal "all xSTimes,g,K,xs,n(
 H g K n=Zero -> (V alpha)xSTimes g K xs n eqd(Inhab alpha))")
(assume "xSTimes" "g" "K" "xs" "n" "hn=0")
(simp "VDef")
(simp "hn=0")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "VIfH0")

;; VIfH2
(set-goal "all xSTimes,g,K,xs,n,m(
 H g K n=Succ(Succ m) -> (V alpha)xSTimes g K xs n eqd xSTimes n(xs m))")
(assume "xSTimes" "g" "K" "xs" "n" "m" "hn=m+2")
(simp "VDef")
(simp "hn=m+2")
(simp "SeqDef2")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "VIfH2")

;; VIfH1
(set-goal "all xSTimes,g,K,xs,n(H g K n=Succ Zero ->
 (V alpha)xSTimes g K xs n eqd(V alpha)xSTimes g K xs(Pred n))")
(assume "xSTimes" "g" "K" "xs")
(cases)
(strip)
(use "InitEqD")
(assume "n" "h(n+1)=1")
(simp "VDef")
(simp "h(n+1)=1")
(simp "VDef")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "VIfH1")

;; VIfH2Up
(set-goal "all xSTimes,g,K,n,m,xs(
 H g K n=Succ(Succ m) ->
 all n,m(n<=m -> K n<=K m) ->
 all n1(V alpha)xSTimes g K xs(n+n1)eqd xSTimes n(xs m))")
(assume "xSTimes"  "g" "K" "n" "m" "xs" "hn=m+2" "KMon")
(ind)
(use "VIfH2")
(use "hn=m+2")
(assume "n1" "IH")
(assert "(V alpha)xSTimes g K xs(Succ(n+n1)) eqd
         (V alpha)xSTimes g K xs(Pred(Succ(n+n1)))")
(use "VIfH1")
(use "H2Up" (pt "m"))
(use "hn=m+2")
(use "KMon")
(assert "Pred(Succ(n+n1))=n+n1")
(use "Truth")
(assume "Pred(Succ(n+n1))=n+n1")
(simp "Pred(Succ(n+n1))=n+n1")
(simp "IH")
(assume "Hyp")
(use "Hyp")
;; Proof finished.
;; (cdp)
(save "VIfH2Up")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; VCauchy
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We will show from these properties that (x_n) is a Cauchy sequence
;; with modulus N(p) := PosToNat(SZero p)

;; From StabRealLe together with StabAllImpThreeTwo prove StabCauchy .

;; StabCauchy
(set-goal "all xNorm,xPlus,xUMinus,xs,N(
 all n,m Real(xNorm(xPlus(xs n)(xUMinus(xs m)))) ->
  ((all p,n,m(N p<=n -> n<m ->
              xNorm(xPlus(xs n)(xUMinus(xs m)))<<=(1#2**p)) -> F) -> F) ->
    all p,n,m(N p<=n -> n<m -> xNorm(xPlus(xs n)(xUMinus(xs m)))<<=(1#2**p)))")
(assume "xNorm" "xPlus" "xUMinus" "xs" "N" "RHyp")
(use "StabAllImpThreeTwo")
(assume "p" "n" "m")
(use "StabRealLe")
(use "RHyp")
(use "RealRat")
;; Proof finished.
;; (cdp)
(save "StabCauchy")

;; NatLtPosNatToExDiff
(set-goal "all q,n(q<n -> exl r q+r=n)")
(assume "q" "n" "q<n")
(assert "Zero<n")
(use "NatLeLtTrans" (pt "PosToNat q"))
(use "Truth")
(use "q<n")
;; Assertion proved.
(assume "0<n")
(assert "NatToPos(PosToNat q)<NatToPos n")
(simp "NatToPosLt")
(use "q<n")
(use "0<n")
(use "NatLtZeroPosToNat")
(assume "<Hyp")
(intro 0 (pt "NatToPos n--q"))
(assert "all r,p(r<p -> r+(p--r)=p)")
(assume "r" "p")
(simp "PosPlusComm")
(use "PosMinusPlusEq")
;; Assertion proved.
(assume "Assertion")
(simp "Assertion")
(use "PosToNatToPosId")
(use "0<n")
(simp "<-" (pf "NatToPos(PosToNat q)=q"))
(use "<Hyp")
(use "NatToPosToNatId")
;; Proof finished.
;; (cdp)
(save "NatLtPosNatToExDiff")

(define eterm (proof-to-extracted-term))
(define neterm (term-to-beta-eta-nf eterm))
;; (pp neterm)
;; [q,n]NatToPos n--q

;; VCauchyAuxPos
(set-goal "all p,q,n(SZero p+q=n -> (n#2**n*2)<=(1#2**p))")
(assume "p" "q" "n" "2p+q<n")
(simp "RatLe0CompRule")
(simp "IntTimes2RewRule")
(simp "<-" "2p+q<n")
(drop "2p+q<n")
(simp "PosToNatToIntId")
(ng #t)
;; ?^8:SZero(p*2**p)+q*2**p<=SZero(2**(SZero p+q))
(simp (pf "SZero(2**(SZero p+q))=2**(SZero p+q)+2**(SZero p+q)"))
(get 10)
(use "SZeroPosPlus")
;; ?^9:SZero(p*2**p)+q*2**p<=2**(SZero p+q)+2**(SZero p+q)
(use "PosLeMonPlus")
;; 11,12
;; ?^11:SZero(p*2**p)<=2**(SZero p+q)
(inst-with-to "SZeroPosTimes" (pt "p*2**p") "Inst")
(simp "Inst")
(drop "Inst")
(simp "PosTimesAssoc")
(use "PosLeTrans" (pt "2**p*2**p"))
(use "PosLeMonTimes")
(use "PosLeTimesTwoExp")
(use "Truth")
(simp "PosExpTwoPosPlus")
(simp "<-" "SZeroPosPlus")
(use "PosLeMonPosExpPos")
(use "Truth")
;; ?^12:q*2**p<=2**(SZero p+q)
(simp "PosTimesComm")
(use "PosLeTrans" (pt "2**p*2**q"))
(use "PosLeMonTimes")
(use "Truth")
(use "PosLeTrans" (pt "2*q"))
(use "Truth")
(use "PosLeTimesTwoExp")
(simp "PosExpTwoPosPlus")
(use "PosLeMonPosExpPos")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "VCauchyAuxPos")

;; VCauchy
(set-goal "all xSTimes,xNorm,xPlus,xUMinus,M,xs,K,xs1,N,g(
 xB^(Inhab alpha) ->
 all x(xB^ x -> xNorm(xPlus x(xUMinus x))===0) ->
 all n xB^(xs n) ->
 all n xB^(xs1 n) ->
 all x(xB^ x -> xB^(xUMinus x)) ->
 all rea,x(Real rea -> xB^ x -> xB^(xSTimes rea x)) ->
 all x(xB^ x -> xNorm(xPlus(Inhab alpha)x)===xNorm x) ->
 all x(xB^ x -> xNorm(xUMinus x)===xNorm x) ->
 all rea,x(0<<=rea -> xB^ x -> xNorm(xSTimes rea x)===rea*xNorm x) ->
 all p,n(M p<=n -> xNorm(xs n)<<=(1#2**p)) ->
 M 1=Zero -> all p,q(p<=q -> M p<=M q) ->
 all n K n=M(NatToPos(Succ n)) ->
 all n xs1 n eqd(V alpha)xSTimes g K xs n ->
 all p N p=PosToNat(SZero p) ->
 all n,m Real(xNorm(xPlus(xs1 n)(xUMinus(xs1 m)))) ->
 all p,n,m(N p<=n -> n<m -> xNorm(xPlus(xs1 n)(xUMinus(xs1 m)))<<=(1#2**p)))")
(assume "xSTimes" "xNorm" "xPlus" "xUMinus" "M" "xs" "K" "xs1" "N" "g"
	"InhB" "BanachNormZero" "xsBanach" "xs1Banach"
	"BanachxUMinus" "BanachxSTimes"
	"BanachNormPlusInhab" "BanachNormUMinus" "BanachNormTimes"
	"MMod" "M1=0" "MMon" "KDef" "xs1Def" "NDef" "RHyp")
;; We will often need monotonicity of K.
(assert "all n,m(n<=m -> K n<=K m)")
(assume "n" "m" "n<=m")
(simp "KDef")
(simp "KDef")
(use "MMon")
(simp "NatToPosLe")
(use "n<=m")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "KMon")
(use "StabCases" (make-cterm (pf "all n H g K n=Zero")))
;; 13-15
(use "StabCauchy")
(use "RHyp")
;; 14
(assume "hZero")
(assert "all n xs1 n eqd(Inhab alpha)")
(assume "n1")
(simp "xs1Def")
(use "VIfH0")
(use "hZero")
;; Assertion proved.
(assume "xs1Zero" "p" "n" "m" "Np<=m" "n<m")
(simp "xs1Zero")
(simp "xs1Zero")
;; ?^25:xNorm(xPlus(Inhab alpha)(xUMinus(Inhab alpha)))<<=(1#2**p)
(simpreal "BanachNormZero")
(use "RatLeToRealLe")
(use "Truth")
(use "InhB")
;; 15
(assume "hNotZero")
(assert "exca n Zero<H g K n")
(assume "AllHyp")
(use "hNotZero")
(assume "n")
(use "StabAtom")
(assume "hnNotZero")
(use "NatLeCases" (pt "Zero") (pt "H g K n"))
(use "Truth")
(use "AllHyp")
(assume "0=hn")
(use "hnNotZero")
(use "NatEqSym")
(use "0=hn")
;; Assertion proved.
(assume "ExcaHyp")
(inst-with-to
 "ExcaElim" (py "nat")
 (make-cterm (pf "all p,n,m(N p<=n -> n<m ->
                  xNorm(xPlus(xs1 n)(xUMinus(xs1 m)))<<=(1#2**p))"))
 (make-cterm (pv "n") (pf "Zero<H g K n"))
 "ExcaElimInst")
(use "ExcaElimInst")
(drop "ExcaElimInst")
(use "StabCauchy")
(drop "ExcaElimInst")
(use "RHyp")
(drop "ExcaElimInst")
(use "ExcaHyp")
(drop "ExcaElimInst" "ExcaHyp" "hNotZero")
(assume "n0" "0<hn0")
(assert "exnc n1,m(n1<=n0 andnc H g K n1=m+2)")
(use "HFind")
(simp "KDef")
(use "M1=0")
(assume "hn0=0")
(simphyp-with-to "0<hn0" "hn0=0" "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "ExHyp")
(by-assume "ExHyp" "n" "nProp")
(by-assume "nProp" "m" "nmProp")
(assume "p" "n1" "n2" "Np<=n1" "n1<n2")
(use "NatLeLtCases" (pt "n") (pt "n1"))
;; 71,72
(assume "n<=n1")
(assert "xs1 n1 eqd xSTimes n(xs m)")
(simp "xs1Def")
(assert "n1=n+(n1--n)")
(simp "NatPlusMinus")
(ng #t)
(use "Truth")
(use "n<=n1")
;; Assertion proved.
(assume "n1=n+(n1--n)")
(simp "n1=n+(n1--n)")
(use "VIfH2Up")
(use "nmProp")
(use "KMon")
;; Assertion proved
(assume "xs1 n1 eqd xSTimes n(xs m)")
;; Similar with n2 for n1
(assert "xs1 n2 eqd xSTimes n(xs m)")
(simp "xs1Def")
(assert "n2=n+(n2--n)")
(simp "NatPlusMinus")
(ng #t)
(use "Truth")
(use "NatLeTrans" (pt "n1"))
(use "n<=n1")
(use "NatLtToLe")
(use "n1<n2")
;; Assertion proved.
(assume "n2=n+(n2--n)")
(simp "n2=n+(n2--n)")
(use "VIfH2Up")
(use "nmProp")
(use "KMon")
;; Assertion proved
(assume "xs1 n2 eqd xSTimes n(xs m)")
(simp "xs1 n1 eqd xSTimes n(xs m)")
(simp "xs1 n2 eqd xSTimes n(xs m)")
(simpreal "BanachNormZero")
(use "RatLeToRealLe")
(use "Truth")
(use "BanachxSTimes")
(use "RealRat")
(use "xsBanach")
;; ?^72:n1<n -> xNorm(xPlus(xs1 n1)(xUMinus(xs1 n2)))<<=(1#2**p)
(assume "n1<n")
(use "NatLeLtCases" (pt "n") (pt "n2"))
;; 111,112
(assume "n<=n2")
(cases (pt "n"))
;; 114,115
(assume "n=0")
(simphyp-with-to "n1<n" "n=0" "Absurd")
(use "EfRealLe")
(use "Absurd")
;; 115
(assume "n3" "n=Sn3")
(assert "H g K n3=Zero")
(use "H2Down" (pt "m"))
(simp "<-" "n=Sn3")
(use "nmProp")
(use "KMon")
(assume "hn3=0")
(assert "n1<=n3")
(use "NatLtSuccToLe")
(simp "<-" "n=Sn3")
(use "n1<n")
;; Assertion proved.
(assume "n1<=n3")
(assert "H g K n1=Zero")
(use "H0DownMon" (pt "n3"))
(use "KMon")
(use "hn3=0")
(use "n1<=n3")
;; Assertion proved.
(assume "hn1=0")
(assert "xs1 n1 eqd(Inhab alpha)")
(simp "xs1Def")
(use "VIfH0")
(use "hn1=0")
;; Assertion proved.
(assume "xs1 n1 eqd(Inhab alpha)")
(simp "xs1 n1 eqd(Inhab alpha)")
(simpreal "BanachNormPlusInhab")
(simpreal "BanachNormUMinus")
(simp "xs1Def")
(assert "n2=n+(n2--n)")
(simp "NatPlusMinus")
(ng #t)
(use "Truth")
(use "n<=n2")
;; Assertion proved
(assume "n2=n+(n2--n)")
(simp "n2=n+(n2--n)")
(simp "VIfH2Up" (pt "m"))
;; ?^156:xNorm(xSTimes n(xs m))<<=(1#2**p)
(assert "xNorm(xs m)<<=(1#2**(NatToPos(Succ n)))")
(use "MMod")
;; Need positive exponent to make MMod usable
;; ?^161:M(NatToPos(Succ n))<=m
(simp "<-" "KDef")
;; ?^162:K n<=m
(assert "NatLeastUp(K n)(K(Succ n))g=m")
(use "HProp2Val")
(use "nmProp")
;; Assertion proved
(assume "NatLeastUp(K n)(K(Succ n))g=m")
(simp "<-" "NatLeastUp(K n)(K(Succ n))g=m")
(use "NatLeastUpLBound")
(use "KMon")
(use "Truth")
;; Assertion proved.
;; ?^159:xNorm(xs m)<<=(1#2**NatToPos(Succ n)) -> xNorm(xSTimes n(xs m))<<=(1#2**p)
(simp (pf "2**NatToPos(Succ n)=2**n*2"))
;; 170,171
;; ?^171:2**NatToPos(Succ n)=2**n*2
(get 171)
(simp "PosToNatToPosId")
(use "Truth")
(use "Truth")
;; ?^170:xNorm(xs m)<<=(1#2**n*2) -> xNorm(xSTimes n(xs m))<<=(1#2**p)
(assume "xNorm(xs m)<<=(1#2**n*2)")
(cut "(n#2**n*2)<<=(1#2**p)") ;suffices, as we pove right now:
;; 175,176
(assume "(n#2**n*2)<<=(1#2**p)")
(simpreal "BanachNormTimes")
;; ?^178:n*xNorm(xs m)<<=(1#2**p)
(use "RealLeTrans" (pt "RealTimes n(1#2**n*2)"))
(use "RealLeMonTimesR")
;; ?^183:0<<=n
(use "RatLeToRealLe")
(use "Truth")
;; ?^184:xNorm(xs m)<<=(1#2**n*2)
(use "xNorm(xs m)<<=(1#2**n*2)")
;; ?^182:RealTimes n(1#2**n*2)<<=(1#2**p)
(use "(n#2**n*2)<<=(1#2**p)")
(use "xsBanach")
(use "RatLeToRealLe")
(use "Truth")
;; ?^176:(n#2**n*2)<<=(1#2**p)
;; The formula cut in above.  We need a relation between n and p
(assert "SZero p<n")
(use "NatLeLtTrans" (pt "N p"))
(simp "NDef")
(use "Truth")
(use "NatLeLtTrans" (pt "n1"))
(use "Np<=n1")
(use "n1<n")
;; Assertion proved.
;; ?^187:SZero p<n -> (n#2**n*2)<<=(1#2**p)

;; (pp "VCauchyAuxPos")
;; all p,q,n(PosToNat(SZero p+q)=n -> (n#2**n*2)<=(1#2**p))

;; (pp "NatLtPosNatToExDiff")
;; all q,n(q<n -> exl r PosToNat(q+r)=n)

(assume "2p<n")
(inst-with-to "NatLtPosNatToExDiff" (pt "SZero p") (pt "n") "2p<n" "ExDiff")
(by-assume "ExDiff" "q" "qProp")
(use "RatLeToRealLe")
(use-with "VCauchyAuxPos" (pt "p") (pt "q") (pt "n") "qProp")
;; 158 all n,m(n<=m -> K n<=K m)
(use "KMon")
(use "nmProp")
(use "xs1Banach")
;; ?^145:xB^(xUMinus(xs1 n2))
(use "BanachxUMinus")
(use "xs1Banach")
;; ?^112:n2<n -> xNorm(xPlus(xs1 n1)(xUMinus(xs1 n2)))<<=(1#2**p)
(assume "n2<n")
(assert "all n3(n3<n -> H g K n3=Zero)")
 (assume "n3" "n3<n")
 (cases (pt "n"))
 (assume "n=0")
 (simphyp-with-to "n3<n" "n=0" "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "n4" "n=n4+1")
 (assert "H g K n4=Zero")
  (use "H2Down" (pt "m"))
  (simp "<-" "n=n4+1")
  (use "nmProp")
  (use "KMon")
 (assume "hn4=0")
 (use "H0DownMon" (pt "n4"))
 (use "KMon")
 (use "hn4=0")
 (use "NatLtSuccToLe")
 (simp "<-" "n=n4+1")
 (use "n3<n")
(assume "all n3(n3<n -> H g K n3=Zero)")
;; ?^224:xNorm(xPlus(xs1 n1)(xUMinus(xs1 n2)))<<=(1#2**p)
(simp "xs1Def")
(assert "(V alpha)xSTimes g K xs n1 eqd(Inhab alpha)")
 (use "VIfH0")
 (use "all n3(n3<n -> H g K n3=Zero)")
(use "n1<n")
(assume "(V alpha)xSTimes g K xs n1 eqd(Inhab alpha)")
(simp "(V alpha)xSTimes g K xs n1 eqd(Inhab alpha)")
(simp "xs1Def")
(assert "(V alpha)xSTimes g K xs n2 eqd(Inhab alpha)")
 (use "VIfH0")
 (use "all n3(n3<n -> H g K n3=Zero)")
 (use "n2<n")
(assume "(V alpha)xSTimes g K xs n2 eqd(Inhab alpha)")
(simp "(V alpha)xSTimes g K xs n2 eqd(Inhab alpha)")
(simpreal "BanachNormZero")
(use "RatLeToRealLe")
(use "Truth")
(use "InhB")
;; Proof finished.
;; (cdp)
(save "VCauchy")

;; H2Compl
(set-goal "all xSTimes,xNorm,xPlus,xUMinus,xLim,x,n1,m,M,xs,K,xs1,N,g(
 xB^ x ->
 all n xB^(xs1 n) ->
 all x(xB^ x -> Real(xNorm x)) ->
 all x1,x2(xB^ x1 -> xB^ x2 -> 0<<=xNorm(xPlus x1(xUMinus x2))) ->
 all x1,x2(xB^ x1 -> xB^ x2-> xB^(xPlus x1 x2)) ->
 all x(xB^ x -> xB^(xUMinus x)) ->
 all x1,x2(xB^ x1 -> xB^ x2 ->
  xNorm(xPlus x1(xUMinus x2))===0 -> xEq^ x1 x2) ->
 all xs1,N,p,n(
  all p,n,m(N p<=n -> n<m -> xNorm(xPlus(xs1 n)(xUMinus(xs1 m)))<<=(1#2**p)) ->
  N p<=n -> xNorm(xPlus(xs1 n)(xUMinus(xLim xs1 N)))<<=(1#2**p)) ->
 all p,n(M p<=n -> xNorm(xs n)<<=(1#2**p)) -> 
 M 1=Zero -> 
 all p,q(p<=q -> M p<=M q) -> 
 all n K n=M(NatToPos(Succ n)) -> 
 all n xs1 n eqd(V alpha)xSTimes g K xs n -> 
 x eqd xLim xs1 N ->
 all p N p=PosToNat(SZero p) -> 
 all p,n,m(N p<=n -> n<m -> xNorm(xPlus(xs1 n)(xUMinus(xs1 m)))<<=(1#2**p)) ->
 H g K n1=Succ(Succ m) -> xEq^(xSTimes n1(xs m))x)")
(assume "xSTimes" "xNorm" "xPlus" "xUMinus" "xLim"
	"x" "n1" "m" "M" "xs" "K" "xs1" "N" "g"
	"xBanach" "xs1Banach" "BanachNormReal" "BanachNormNNeg"
	"BanachxPlus" "BanachxUMinus"
        "BanachInitEqv" "BanachCauchyConvMod"
	"MMod" "M1=0" "MMon" "KDef" "xs1Def" "xDef" "NDef" "NMod" "hn1=m+2")
;; We will often need monotonicity of K.
(assert "all n,m(n<=m -> K n<=K m)")
(assume "n" "m1" "n<=m1")
(simp "KDef")
(simp "KDef")
(use "MMon")
(simp "NatToPosLe")
(use "n<=m1")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "KMon")
;; We now use the fact that the Cauchy sequence xs1 with modulus N
;; converges with the same modulus to its limit x:
(assert "all p,n(N p<=n -> xNorm(xPlus(xs1 n)(xUMinus x))<<=(1#2**p))")
(simp "xDef")
(assume "p" "n")
(use "BanachCauchyConvMod")
(use "NMod")
(assume "xs1Conv")
;; We show that beyond n1 (where hn1=m+2) xs1 is constant
(assert "all n(n1<n -> H g K n=Succ Zero)")
(ind)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "IH" "n1<n+1")
(use "NatLtSuccCases" (pt "n1") (pt "n"))
(use "n1<n+1")
(assume "n1<n")
(use "H1Succ")
(use "IH")
(use "n1<n")
(use "KMon")
(assume "n1=n")
(simp "<-" "n1=n")
(use "H2Succ" (pt "m"))
(use "hn1=m+2")
(use "KMon")
;; Assertion proved.
(assume "hn=1")
(assert "all n(n1<n -> xs1 n1 eqd xs1 n)")
(ind)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n" "IH" "n1<n+1")
(use "NatLtSuccCases" (pt "n1") (pt "n"))
(use "n1<n+1")
(assume "n1<n")
(assert "xs1(Succ n)eqd xs1(Pred(Succ n))")
(simp "xs1Def")
(simp "xs1Def")
(use "VIfH1")
(use "H1Succ")
(use "hn=1")
(use "n1<n")
(use "KMon")
(ng #t)
(assume "EqHyp")
(simp "EqHyp")
(use "IH")
(use "n1<n")
(assume "n1=n")
(simp "<-" "n1=n")
(assert "xs1(Succ n1)eqd xs1(Pred(Succ n1))")
(simp "xs1Def")
(simp "xs1Def")
(use "VIfH1")
(use "hn=1")
(use "Truth")
(ng #t)
(assume "EqHyp")
(simp "EqHyp")
(use "InitEqD")
;; Assertion "all n(n1<n -> xs1 n1 eqd xs1 n)" proved.
(assume "xs1ConstAux")
(assert "all n(n1<=n -> xs1 n1 eqd xs1 n)")
(assume "n" "n1<=n")
(use "NatLeCases" (pt "n1") (pt "n"))
(use "n1<=n")
(use "xs1ConstAux")
(assume "n1=n")
(simp "n1=n")
(use "InitEqD")
;; Assertion "all n(n1<=n -> xs1 n1 eqd xs1 n)") proved.
(assume "xs1Const")
(drop "xs1ConstAux")
(assert "xs1 n1 eqd xSTimes n1(xs m)")
(simp "xs1Def")
(use "VIfH2")
(use "hn1=m+2")
;; Assertion "xs1 n1 eqd xSTimes n1(xs m)" proved
(assume "xs1 n1 eqd xSTimes n1(xs m)")
(simp "<-" "xs1 n1 eqd xSTimes n1(xs m)")
(use "BanachInitEqv")
(use "xs1Banach")
(use "xBanach")
;; ?^91:xNorm(xPlus(xs1 n1)(xUMinus x))===0
(use "RealLeAntiSym")
;; 92,93
(use "RealLeAllPlusToLe")
(use "BanachNormReal")
(use "BanachxPlus")
(use "xs1Banach")
(use "BanachxUMinus")
(use "xBanach")
(use "RealRat")
;; ?^96:all p xNorm(xPlus(xs1 n1)(xUMinus x))<<=RealPlus 0(1#2**p)
(ng #t)
;; ?^101:all p xNorm(xPlus(xs1 n1)(xUMinus x))<<=(1#2**p)
(assume "p")
(assert "all n(n1<=n -> N p<=n ->
 xs1 n1 eqd xs1 n andnc xNorm(xPlus(xs1 n)(xUMinus x))<<=(1#2**p))")
(assume "n" "n1<=n" "Np<=n")
(split)
(use "xs1Const")
(use "n1<=n")
(use "xs1Conv")
(use "Np<=n")
;; Assertion proved.
(assume "Assertion")
(assert "xs1 n1 eqd xs1(n1 max(N p))")
(use "Assertion")
(use "NatMaxUB1")
(use "NatMaxUB2")
(assume "EqHyp")
(simp "EqHyp")
(use "xs1Conv")
(use "NatMaxUB2")
(use "BanachNormNNeg")
(use "xs1Banach")
(use "xBanach")
;; Proof finished.
;; (cdp)
(save "H2Compl")

;; We now aim at IshiharaTrick.  First we list in the order of usage
;; what is needed.

;; AC
(add-global-assumption
 "AC" "all m exl boole (Pvar nat boole)^ m boole ->
       exl g all m (Pvar nat boole)^ m (g m)")

;; RatLtMonTimesNat
(set-goal "all a,n,m(0<a -> n<m -> n*a<m*a)")
(assume "a" "n" "m" "0<a" "n<m")
(use "RatNotLeToLt")
(assume "m*a<=n*a")
(inst-with-to "RatLeTimesCancelR" (pt "a") (pt "(m#1)") (pt "(n#1)")
	      "0<a" "m*a<=n*a" "Inst")
(ng "Inst")
(assert "m<=n -> F")
(assume "m<=n")
(use-with "NatLtLeTrans"  (pt "n") (pt "m") (pt "n") "n<m" "m<=n")
(assume "m<=n -> F")
(use "m<=n -> F")
(simp "<-" "NatToIntLe")
(use "Inst")
;; Proof finished.
;; (cdp)
(save "RatLtMonTimesNat")

;; IshiharaTrickAux
(set-goal "all xSTimes,xNorm,xPlus,xUMinus,xLim,ySTimes,yNorm,xs,xs1,g,K,M,N(
 xB^(Inhab alpha) ->
 all x(xB^ x -> xNorm(xPlus x(xUMinus x))===0) ->
 all n xB^(xs n) ->
 all n xs1 n eqd(V alpha)xSTimes g K xs n ->
 all rea,x(Real rea -> xB^ x -> xB^(xSTimes rea x)) ->
 all x(xB^ x -> xB^(xUMinus x)) ->
 all x(xB^ x -> xNorm(xPlus(Inhab alpha)x)===xNorm x) ->
 all x(xB^ x -> xNorm(xUMinus x)===xNorm x) ->
 all rea,x(0<<=rea -> xB^ x -> xNorm(xSTimes rea x)===rea*xNorm x) ->
 all p,m(M p<=m -> xNorm(xs m)<<=(1#2**p)) ->
 M 1=Zero ->
 all p,q(p<=q -> M p<=M q) ->
 all n K n=M(NatToPos(Succ n)) ->
 all p N p=PosToNat(SZero p) ->
 all x(xB^ x -> Real(xNorm x)) ->
 all x,x0(xB^ x -> xB^ x0 -> xB^(xPlus x x0)) ->
 all xs,M(
        all p,n,m(
         M p<=n -> n<m -> xNorm(xPlus(xs n)(xUMinus(xs m)))<<=(1#2**p)) -> 
        xB^(xLim xs M)) ->
 xB^(xLim xs1 N))")
(assume "xSTimes" "xNorm" "xPlus" "xUMinus" "xLim" "ySTimes" "yNorm"
	"xs" "xs1" "g" "K" "M" "N"
	"InhB" "BanachNormZero" "xsB" "xs1Def" "BanachxSTimes"
        "BanachxUMinus" "BanachNormPlusInhab" "BanachNormUMinus"
        "BanachNormTimes" "Conv" "M0" "MMon" "KDef" "NDef"
	"RealxNorm" "BanachxPlus" "BLim")
(use "BLim")
(use "VCauchy" (pt "xSTimes") (pt "M") (pt "xs") (pt "K") (pt "g"))
(use "InhB")
(use "BanachNormZero")
(use "xsB")
(assume "n")
(simp "xs1Def")
;; ?^21:xB^((V alpha)xSTimes g K xs n)
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
(use "BanachxUMinus")
(use "BanachxSTimes")
(use "BanachNormPlusInhab")
(use "BanachNormUMinus")
(use "BanachNormTimes")
(use "Conv")
(use "M0")
;; ?^15:all p,q(p<=q -> M p<=M q)
(use "MMon")
(use "KDef")
(use "xs1Def")
(use "NDef")
;; ?^19:all n,m Real(xNorm(xPlus(xs1 n)(xUMinus(xs1 m))))
(assert "all n xB^(xs1 n)")
(assume "n")
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
;; Assertion proved.
(assume "xs1B")
;; ?^32:all n,m Real(xNorm(xPlus(xs1 n)(xUMinus(xs1 m))))
(assume "n" "m1")
(use "RealxNorm")
(use "BanachxPlus")
(use "xs1B")
(use "BanachxUMinus")
(use "xs1B")
;; Proof finished.
;; (cdp)
(save "IshiharaTrickAux")

;; IshiharaTrick
(set-goal "allnc xNorm,xPlus,xUMinus,ySTimes
 all xSTimes,xLim,yNorm,f,xs,M,a,b,p(
 xB^(Inhab alpha) ->
 all x(xB^ x -> Real(xNorm x)) ->
 all x0,x1(xB^ x0 -> xB^ x1 -> 0<<=xNorm(xPlus x0(xUMinus x1))) -> 
 all x1,x2(xB^ x1 -> xB^ x2 ->
  xNorm(xPlus x1(xUMinus x2))===0 -> xEq^ x1 x2) ->
 all x(xB^ x -> xNorm(xPlus x(xUMinus x))===0) ->
 all n xB^(xs n) ->
 all x(xB^ x -> xB^(xUMinus x)) ->
 all x1,x2(xB^ x1 -> xB^ x2 -> xB^(xPlus x1 x2)) ->
 all rea,x(Real rea -> xB^ x -> xB^(xSTimes rea x)) ->
 all x(xB^ x -> xNorm(xPlus(Inhab alpha)x)===xNorm x) ->
 all x(xB^ x -> xNorm(xUMinus x)===xNorm x) ->
 all rea,x(0<<=rea -> xB^ x -> xNorm(xSTimes rea x)===rea*xNorm x) ->
 all xs,M((all p,n,m(M p<=n -> n<m ->
                     xNorm(xPlus(xs n)(xUMinus(xs m)))<<=(1#2**p)) ->
   xB^(xLim xs M))) ->
 all xs,M((all p,n,m(M p<=n -> n<m ->
                   xNorm(xPlus(xs n)(xUMinus(xs m)))<<=(1#2**p)) ->
   all p,n(M p<=n -> xNorm(xPlus(xs n)(xUMinus(xLim xs M)))<<=(1#2**p)))) ->
 all x(xB^ x -> yN^(f x)) ->
 all x1,x2(xB^ x1 -> xB^ x2 -> xEq^ x1 x2 -> yEq^(f x1)(f x2)) ->
 all y(yN^ y -> Real(yNorm y)) ->
 all y1,y2(yN^ y1 -> yN^ y2 -> yEq^ y1 y2 -> yNorm y1===yNorm y2) ->
 all y(yN^ y -> 0<<=yNorm y) ->
 all rea,y(0<<=rea -> yN^ y -> yNorm(ySTimes rea y)===rea*yNorm y) ->
 all rea,x f(xSTimes rea x)eqd ySTimes rea(f x) ->
 all p,m(M p<=m -> xNorm(xs m)<<=(1#2**p)) ->
 M 1=Zero ->
 all p,q(p<q -> M p<M q) ->
 0<a -> a<b -> (1#2**p)<=b-a ->
 exnc m a<<=yNorm(f(xs m)) oru all m yNorm(f(xs m))<<=b)")
(assume "xNorm" "xPlus" "xUMinus" "ySTimes"
	"xSTimes" "xLim" "yNorm" "f" "xs" "M" "a" "b" "p"
	"InhB" "RealxNorm" "BanachNormNNeg" "BanachInitEqv"
	"BanachNormZero" "xsB" "BanachxUMinus" "BanachxPlus" "BanachxSTimes"
	"BanachNormPlusInhab" "BanachNormUMinus" "BanachNormTimes"
	"BLim" "BCompl" "fBanachNorm" "fCompat"
	"RealyNorm" "yNormCompat"
	"0<<=yNorm" "yNormTimes"
	"fLin*" "Conv" "M0" "MStrMon" "0<a" "a<b" "(1#2**p)<=b-a")
(assert "exl g all m((g m -> yNorm(f(xs m))<<=b) andnc
                     ((g m -> F) -> a<<=yNorm(f(xs m))))")
(use "AC")
(assume "m")
(use "ApproxSplitBooleRat" (pt "p"))
(use "RealyNorm")
(use "fBanachNorm")
(use "xsB")
(use "(1#2**p)<=b-a")
;; Assertion proved.
(assume "g1Ex")
(by-assume "g1Ex" "g1" "g1Prop")
(cut "exl g all m((g m -> a<<=yNorm(f(xs m))) andnc
                 ((g m -> F) -> yNorm(f(xs m))<<=b))")
(use "Id")
(assume "gEx")
(by-assume "gEx" "g" "gProp")
;; (drop "g1Prop")
(assert "exl K all n K n=M(NatToPos(Succ n))")
(intro 0 (pt "[n]M(NatToPos(Succ n))"))
(assume "n")
(use "Truth")
;; Assertion proved.
(assume "KEx")
(by-assume "KEx" "K" "KDef")
(assert "exl xs1 all n xs1 n eqd(V alpha)xSTimes g K xs n")
(intro 0 (pt "[n](V alpha)xSTimes g K xs n"))
(assume "n")
(use "InitEqD")
;; Assertion proved.
(assume "xs1Ex")
(by-assume "xs1Ex" "xs1" "xs1Def")
(assert "exl N all p N p=PosToNat(SZero p)")
(intro 0 (pt "[p]PosToNat(SZero p)"))
(assume "p1")
(use "Truth")
;; Assertion proved.
(assume "NEx")
(by-assume "NEx" "N" "NDef")
(assert "exl x x eqd xLim xs1 N")
(intro 0 (pt "xLim xs1 N"))
(use "InitEqD")
;; Assertion proved.
(assume "xEx")
(by-assume "xEx" "x" "xDef")
;; We prove ordinary monotonicity of M from strict monotonicity.
(assert "all p,q(p<=q -> M p<=M q)")
(assume "p0" "q" "p0<=q")
(use "PosLeCases" (pt "p0") (pt "q"))
(use "p0<=q")
(assume "p0<q")
(use "NatLtToLe")
(use "MStrMon")
(use "p0<q")
(assume "p0=q")
(simp "p0=q")
(use "Truth")
;; Assertion proved.
(assume "MMon")
(assert "exl n yNorm(f x)<<=n*a")
(use "RealLePosRatBound")
(use "RealyNorm")
(use "fBanachNorm")
(simp "xDef")
(use "IshiharaTrickAux" (pt "xSTimes") (pt "xNorm") (pt "xPlus") (pt "xUMinus")
     (pt "ySTimes") (pt "yNorm") (pt "xs") (pt "g") (pt "K") (pt "M"))
(use "InhB")
(use "BanachNormZero")
(use "xsB")
(use "xs1Def")
(use "BanachxSTimes")
(use "BanachxUMinus")
(use "BanachNormPlusInhab")
(use "BanachNormUMinus")
(use "BanachNormTimes")
(use "Conv")
(use "M0")
(use "MMon")
(use "KDef")
(use "NDef")
(use "RealxNorm")
(use "BanachxPlus")
(use "BLim")
;; IshiharaTrickAux successfully used
(use "0<a")
;; ?_65:exl n yNorm(f x)<<=n*a -> 
;;      exnc m a<<=yNorm(f(xs m)) oru all m yNorm(f(xs m))<<=b
(assume "n0Ex")
(by-assume "n0Ex" "n0" "n0Prop")
;; We will often need monotonicity of K.
(assert "all n,m(n<=m -> K n<=K m)")
(assume "n" "m" "n<=m")
(simp "KDef")
(simp "KDef")
(use "MMon")
(simp "NatToPosLe")
(use "n<=m")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "KMon")
;; Now the main case distinction, on hn0=0
(cases (pt "H g K n0"))
;; 103,104
(assume "hn0=0")
(intro 1)
(assert "all n(n<=n0 -> H g K n=Zero)")
(assume "n" "n<=n0")
(use "H0DownMon" (pt "n0"))
(use "KMon")
(use "hn0=0")
(use "n<=n0")
;; Assertion proved.
(assume "all n(n<=n0 -> H g K n=Zero)")
(assert "all n(n0<n -> (H g K n=Zero -> F) -> F)")
(assume "n1" "n0<n1" "H g K n1=Zero -> F")
(assert "exd n exl m(n<=n1 andnc H g K n=Succ(Succ m))")
(use "HFind")
(simp "KDef")
(use "M0")
(use "H g K n1=Zero -> F")
(assume "ExHyp")
(by-assume "ExHyp" "n" "nProp")
(by-assume "nProp" "m" "mProp")
(use "NatLeLtCases" (pt "n") (pt "n0"))
;; 129,130
(assume "n<=n0")
(assert "H g K n=Zero")
(use "H0DownMon" (pt "n0"))
(use "KMon")
(use "hn0=0")
(use "n<=n0")
(simp "mProp")
(assume "Absurd")
(use "Absurd")
;; 130:n0<n -> F
;; Now derive a contradiction as Ishihara did, using H2Compl and HProp2gVal
(assert "xEq^(xSTimes n(xs m))x")
(use-with "H2Compl"
	  (pt "xSTimes") (pt "xNorm") (pt "xPlus") (pt "xUMinus") (pt "xLim")
	  (pt "x") (pt "n") (pt "m") (pt "M") (pt "xs") (pt "K")
	  (pt "xs1") (pt "N") (pt "g")
	  "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?")
;; 141-157
;; ?^141:xB^ x
(simp "xDef")
(use "IshiharaTrickAux" (pt "xSTimes") (pt "xNorm") (pt "xPlus") (pt "xUMinus")
     (pt "ySTimes") (pt "yNorm") (pt "xs") (pt "g") (pt "K") (pt "M"))
(use "InhB")
(use "BanachNormZero")
(use "xsB")
(use "xs1Def")
(use "BanachxSTimes")
(use "BanachxUMinus")
(use "BanachNormPlusInhab")
(use "BanachNormUMinus")
(use "BanachNormTimes")
(use "Conv")
(use "M0")
(use "MMon")
(use "KDef")
(use "NDef")
(use "RealxNorm")
(use "BanachxPlus")
(use "BLim")
;; IshiharaTrickAux successfully used
;; ?^142:all n xB^(xs1 n)
(assume "n2")
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
;; ?^143:all x(xB^ x -> Real(xNorm x))
(auto)
;;156:all p,n,m(N p<=n -> n<m -> xNorm(xPlus(xs1 n)(xUMinus(xs1 m)))<<=(1#2**p))
(use "VCauchy" (pt "xSTimes") (pt "M") (pt "xs") (pt "K") (pt "g"))
(auto)
;; ?^184:all n xB^(xs1 n)
(assume "n2")
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
;; ?^185:all x(xB^ x -> xB^(xUMinus x))
(auto)
;; ?^196:all n,m Real(xNorm(xPlus(xs1 n)(xUMinus(xs1 m))))
(assume "n2" "m2")
(use "RealxNorm")
(use "BanachxPlus")
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
(use "BanachxUMinus")
;; ?^210:xB^(xs1 m2)
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
;; ?^157:H g K n=Succ(Succ m)
(use "mProp")
;; ?^139:xEq^(xSTimes n(xs m))x -> n0<n -> F
;; Assertion proved.
(assume "xEq^(xSTimes n(xs m))x""n0<n")
(assert "g m")
(use "HProp2gVal" (pt "K") (pt "n"))
(use "mProp")
(use "KMon")
(use "Truth")
;; Assertion proved.
;; ?^216:g m -> F
(assume "gm")
(assert "a<<=yNorm(f(xs m))")
(use "gProp")
(use "gm")
;; Assertion proved.
;; ?^222:a<<=yNorm(f(xs m)) -> F
(assume "a<<=yNorm(f(xs m))")
(assert "RealTimes n a<<=n*yNorm(f(xs m))")
(use "RealLeMonTimesTwo")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "RatLtToLe")
(use "0<a")
(use "RatLeToRealLe")
(use "Truth")
(use "a<<=yNorm(f(xs m))")
;; Assertion proved.
;; ?^226:RealTimes n a<<=n*yNorm(f(xs m)) -> F
(assume "RealTimes n a<<=n*yNorm(f(xs m))")
(assert "RealTimes n a<<=yNorm(ySTimes n(f(xs m)))")
(use "RealLeCompat"
     (pt "RealConstr([n1]RatConstr(NatToInt n)One*a)([p]Zero)")
     (pt "n*yNorm(f(xs m))"))
(use "RealEqRefl")
(use "RealRat")
(simpreal "yNormTimes")
(use "RealEqRefl")
(use "RealTimesReal")
(use "RealRat")
(use "RealyNorm")
(use "fBanachNorm")
(use "xsB")
(use "fBanachNorm")
(use "xsB")
(use "RatLeToRealLe")
(use "Truth")
(use "RealTimes n a<<=n*yNorm(f(xs m))")
;; Assertion proved.
(assume "RealTimes n a<<=yNorm(ySTimes n(f(xs m)))")
;; Was
;; (assert "n*a<<=yNorm(f x)")
;; (use "BanachEqvCompat")
;; Instead we start from xEq^(xSTimes n(xs m))x and derive first
;; yEq^(f(xSTimes n(xs m)))(f x)) and then
;; yNorm(f(xSTimes n(xs m)))===yNorm(f x)
;; Then by compatibility of <<= with === we have n*a<<=yNorm(f x)

(assert "yEq^(f(xSTimes n(xs m)))(f x)")
(use "fCompat")
(use "BanachxSTimes")
(use "RealRat")
(use "xsB")
;; ?^257:xB^ x
(simp "xDef")
(use "IshiharaTrickAux" (pt "xSTimes") (pt "xNorm") (pt "xPlus") (pt "xUMinus")
     (pt "ySTimes") (pt "yNorm") (pt "xs") (pt "g") (pt "K") (pt "M"))
(use "InhB")
(use "BanachNormZero")
(use "xsB")
(use "xs1Def")
(use "BanachxSTimes")
(use "BanachxUMinus")
(use "BanachNormPlusInhab")
(use "BanachNormUMinus")
(use "BanachNormTimes")
(use "Conv")
(use "M0")
(use "MMon")
(use "KDef")
(use "NDef")
(use "RealxNorm")
(use "BanachxPlus")
(use "BLim")
;; IshiharaTrickAux successfully used
;; ?^258:xEq^(xSTimes n(xs m))x
(use "xEq^(xSTimes n(xs m))x")
;; ?^254:yEq^(f(xSTimes n(xs m)))(f x) -> F
(assume "yEq^(f(xSTimes n(xs m)))(f x)")
(assert "yNorm(f(xSTimes n(xs m)))===yNorm(f x)")
(use "yNormCompat")
(use "fBanachNorm")
(use "BanachxSTimes")
(use "RealRat")
(use "xsB")
(use "fBanachNorm")
(simp "xDef")
(use "BLim")
(use "VCauchy" (pt "xSTimes") (pt "M") (pt "xs") (pt "K") (pt "g"))
(auto)
;; ?^294:all n xB^(xs1 n)
(assume "n2")
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
;; ?^295:all x(xB^ x -> xB^(xUMinus x))
(auto)
;; ?^306:all n,m Real(xNorm(xPlus(xs1 n)(xUMinus(xs1 m))))
(assume "n2" "m2")
(use "RealxNorm")
(use "BanachxPlus")
;; ?^314:xB^(xs1 n2)
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
(use "BanachxUMinus")
;; ?^320:xB^(xs1 m2)
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
;; ?^284:yEq^(f(xSTimes n(xs m)))(f x)
(use "yEq^(f(xSTimes n(xs m)))(f x)")
;; Assertion proved.
(assume "yNorm(f(xSTimes n(xs m)))===yNorm(f x)")
(assert "n*a<<=yNorm(f x)")
(use "RealLeCompat"
     (pt "RealConstr([nat]n*a)([p]Zero)") (pt "yNorm(f(xSTimes n(xs m)))"))
(use "RealEqRefl")
(use "RealRat")
(use "yNorm(f(xSTimes n(xs m)))===yNorm(f x)")
(simp "fLin*")
(use "RealTimes n a<<=yNorm(ySTimes n(f(xs m)))")
;; "Assertion proved.
(assume "n*a<<=yNorm(f x)")
;; With n0Prop: yNorm(f x)<<=n0*a we get n*a<=n0*a contradicting n0<n
(assert "n*a<=n0*a")
(use "RealLeTransRat" (pt "yNorm(f x)"))
(use "n*a<<=yNorm(f x)")
(use "n0Prop")
;; Assertion proved.
(assume "n*a<=n0*a")
(assert "n0*a<n*a")
(use "RatLtMonTimesNat")
(use "0<a")
(use "n0<n")
;; Assertion proved.
(assume "n0*a<n*a")
;; Assertion proved.
(assert "n*a<n*a")
(use "RatLeLtTrans" (pt "n0*a"))
(use "n*a<=n0*a")
(use "n0*a<n*a")
(assume "Absurd")
(use "Absurd")
;; ?^114:all n(n0<n -> (H g K n=Zero -> F) -> F) -> all m yNorm(f(xs m))<<=b
;; Here we need that M is strictly monotonic, to use HProp0Cor
(assume "all n(n0<n -> (H g K n=Zero -> F) -> F)")
(assert "all n H g K n=Zero")
(assume "n")
(use "NatLeLtCases" (pt "n") (pt "n0"))
(use "all n(n<=n0 -> H g K n=Zero)")
(assume "n0<n")
(use "StabAtom")
(use "all n(n0<n -> (H g K n=Zero -> F) -> F)")
(use "n0<n")
(assume "all n H g K n=Zero" "m")
(use "gProp")
(use "HProp01Cor" (pt "K") (pt "Succ m"))
(use "all n H g K n=Zero")
(assert "all n n<K(Succ n)")
(ind)
(use "NatLeLtTrans" (pt "K Zero"))
(simp "KDef")
(use "Truth")
(simp "KDef")
(simp "KDef")
(use "MStrMon")
(use "Truth")
(assume "n" "IH")
(use "NatLtLeTrans" (pt "Succ(K(Succ n))"))
(use "IH")
(use "NatLtToSuccLe")
(simp "KDef")
(simp "KDef")
(use "MStrMon")
(simp "NatToPosLt")
(use "Truth")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "all n n<K(Succ n)")
(use "all n n<K(Succ n)")
;; ?_104:all n(
;;        H g K n0=Succ n -> 
;;        exnc m a<<=yNorm(f(xs m)) oru all m yNorm(f(xs m))<<=b)
(assume "n" "hn0=n+1")
(intro 0)
(assert "exd n1 exl m(n1<=n0 andnc H g K n1=m+2)")
(use "HFind")
(simp "KDef")
(use "M0")
(simp "hn0=n+1")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "exd n1 exl m(n1<=n0 andnc H g K n1=m+2)")
(by-assume "exd n1 exl m(n1<=n0 andnc H g K n1=m+2)" "n1" "n1Prop")
(by-assume "n1Prop" "m" "mProp")
(intro 0 (pt "m"))
(use "gProp")
(use "HProp2gVal" (pt "K") (pt "n1"))
(use "mProp")
(use "KMon")
(use "Truth")
;; ?_16:exl g 
;;       all m(
;;        (g m -> a<<=yNorm(f(xs m))) andnc ((g m -> F) -> yNorm(f(xs m))<<=b))
(intro 0 (pt "[m]negb(g1 m)"))
(ng #t)
(assume "m")
(split)
(assume "negb(g1 m)")
(use "g1Prop")
(cases (pt "g1 m"))
(assume "g1 m" "Useless")
(simphyp-with-to "negb(g1 m)" "g1 m" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "negb(g1 m) -> F")
(use "g1Prop")
(cases (pt "g1 m"))
(strip)
(use "Truth")
(assume "g1 m -> F")
(use "negb(g1 m) -> F")
(simp "g1 m -> F")
(use "Truth")
;; Proof finished.
;; (cp)
(save "IshiharaTrick")

(define eterm (proof-to-extracted-term))

(remove-computation-rules-for (pt "H g K n"))
;; (display-pconst "V")
(remove-computation-rules-for (pt "(V alpha)xSTimes g K xs n"))
(remove-computation-rules-for (pt "NatToPos n"))

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [xSTimes,xLim,yNorm,f,xs,M,a,a0,p]
;;  [let g
;;    ([n]negb(cAC([n0]cApproxSplitBooleRat a a0(yNorm(f(xs n0)))p)n))
;;    [case (H g([n]M(NatToPos(Succ n)))
;;           (cRealLePosRatBound
;;            (yNorm
;;             (f
;;              (xLim(V xSTimes g([n]M(NatToPos(Succ n)))xs)
;;               ([p0]NatDouble(PosToNat p0)))))
;;            a))
;;     (Zero -> False)
;;     (Succ n -> True)]]

(pp "RealLePosRatBound")
;; all rea,a(Real rea -> 0<a -> exl n rea<<=n*a)

(pp "ApproxSplitBooleRat")
;; all a,b,rea,p(
;;  Real rea -> 
;;  (1#2**p)<=b-a -> 
;;  exl boole((boole -> rea<<=b) andnc ((boole -> F) -> a<<=rea)))

(pp "AC")
;; all m exl boole (Pvar nat boole)^ m boole -> 
;; exl g all m (Pvar nat boole)^ m(g m)

;; Ishihara's trick one with existence: orl instead of oru.  Literally
;; the same proof works.  However, in the extracted term a subterm
;; starting with cRealLePosRatBound occurs twice.  We might take it
;; out with a second let.

;; We first have to revive the computation rules for NatToPos

(add-computation-rules
 "NatToPosStep n(nat=>pos)"
 "[if (NatEven n)
      (SZero((nat=>pos)(NatHalf n)))
      [if (n=Succ Zero) One (SOne((nat=>pos)(NatHalf n)))]]")

(add-computation-rules
 "NatToPos n" "(GRec nat pos)([n]n)n NatToPosStep")

(add-computation-rules "H g K n" "HitPast g K(K n)n")

(add-computation-rules
 "(V alpha)xSTimes g K xs n" "(Seq alpha)xSTimes(H g K)(H g K n)xs n")

(set-goal "allnc xNorm,xPlus,xUMinus,ySTimes
 all xSTimes,xLim,yNorm,f,xs,M,a,b,p(
 xB^(Inhab alpha) ->
 all x(xB^ x -> Real(xNorm x)) ->
 all x0,x1(xB^ x0 -> xB^ x1 -> 0<<=xNorm(xPlus x0(xUMinus x1))) -> 
 all x1,x2(xB^ x1 -> xB^ x2 ->
  xNorm(xPlus x1(xUMinus x2))===0 -> xEq^ x1 x2) ->
 all x(xB^ x -> xNorm(xPlus x(xUMinus x))===0) ->
 all n xB^(xs n) ->
 all x(xB^ x -> xB^(xUMinus x)) ->
 all x1,x2(xB^ x1 -> xB^ x2 -> xB^(xPlus x1 x2)) ->
 all rea,x(Real rea -> xB^ x -> xB^(xSTimes rea x)) ->
 all x(xB^ x -> xNorm(xPlus(Inhab alpha)x)===xNorm x) ->
 all x(xB^ x -> xNorm(xUMinus x)===xNorm x) ->
 all rea,x(0<<=rea -> xB^ x -> xNorm(xSTimes rea x)===rea*xNorm x) ->
 all xs,M((all p,n,m(M p<=n -> n<m ->
                     xNorm(xPlus(xs n)(xUMinus(xs m)))<<=(1#2**p)) ->
   xB^(xLim xs M))) ->
 all xs,M((all p,n,m(M p<=n -> n<m ->
                   xNorm(xPlus(xs n)(xUMinus(xs m)))<<=(1#2**p)) ->
   all p,n(M p<=n -> xNorm(xPlus(xs n)(xUMinus(xLim xs M)))<<=(1#2**p)))) ->
 all x(xB^ x -> yN^(f x)) ->
 all x1,x2(xB^ x1 -> xB^ x2 -> xEq^ x1 x2 -> yEq^(f x1)(f x2)) ->
 all y(yN^ y -> Real(yNorm y)) ->
 all y1,y2(yN^ y1 -> yN^ y2 -> yEq^ y1 y2 -> yNorm y1===yNorm y2) ->
 all y(yN^ y -> 0<<=yNorm y) ->
 all rea,y(0<<=rea -> yN^ y -> yNorm(ySTimes rea y)===rea*yNorm y) ->
 all rea,x f(xSTimes rea x)eqd ySTimes rea(f x) ->
 all p,m(M p<=m -> xNorm(xs m)<<=(1#2**p)) ->
 M 1=Zero ->
 all p,q(p<q -> M p<M q) ->
 0<a -> a<b -> (1#2**p)<=b-a ->
 exl m a<<=yNorm(f(xs m)) orl all m yNorm(f(xs m))<<=b)")
(assume "xNorm" "xPlus" "xUMinus" "ySTimes"
	"xSTimes" "xLim" "yNorm" "f" "xs" "M" "a" "b" "p"
	"InhB" "RealxNorm" "BanachNormNNeg" "BanachInitEqv"
	"BanachNormZero" "xsB" "BanachxUMinus" "BanachxPlus" "BanachxSTimes"
	"BanachNormPlusInhab" "BanachNormUMinus" "BanachNormTimes"
	"BLim" "BCompl" "fBanachNorm" "fCompat"
	"RealyNorm" "yNormCompat"
	"0<<=yNorm" "yNormTimes"
	"fLin*" "Conv" "M0" "MStrMon" "0<a" "a<b" "(1#2**p)<=b-a")
(assert "exl g all m((g m -> yNorm(f(xs m))<<=b) andnc
                     ((g m -> F) -> a<<=yNorm(f(xs m))))")
(use "AC")
(assume "m")
(use "ApproxSplitBooleRat" (pt "p"))
(use "RealyNorm")
(use "fBanachNorm")
(use "xsB")
(use "(1#2**p)<=b-a")
;; Assertion proved.
(assume "g1Ex")
(by-assume "g1Ex" "g1" "g1Prop")
(cut "exl g all m((g m -> a<<=yNorm(f(xs m))) andnc
                 ((g m -> F) -> yNorm(f(xs m))<<=b))")
(use "Id")
(assume "gEx")
(by-assume "gEx" "g" "gProp")
(assert "exl K all n K n=M(NatToPos(Succ n))")
(intro 0 (pt "[n]M(NatToPos(Succ n))"))
(assume "n")
(use "Truth")
;; Assertion proved.
(assume "KEx")
(by-assume "KEx" "K" "KDef")
(assert "exl xs1 all n xs1 n eqd(V alpha)xSTimes g K xs n")
(intro 0 (pt "[n](V alpha)xSTimes g K xs n"))
(assume "n")
(use "InitEqD")
;; Assertion proved.
(assume "xs1Ex")
(by-assume "xs1Ex" "xs1" "xs1Def")
(assert "exl N all p N p=PosToNat(SZero p)")
(intro 0 (pt "[p]PosToNat(SZero p)"))
(assume "p1")
(use "Truth")
;; Assertion proved.
(assume "NEx")
(by-assume "NEx" "N" "NDef")
(assert "exl x x eqd xLim xs1 N")
(intro 0 (pt "xLim xs1 N"))
(use "InitEqD")
;; Assertion proved.
(assume "xEx")
(by-assume "xEx" "x" "xDef")
;; We prove ordinary monotonicity of M from strict monotonicity.
(assert "all p,q(p<=q -> M p<=M q)")
(assume "p0" "q" "p0<=q")
(use "PosLeCases" (pt "p0") (pt "q"))
(use "p0<=q")
(assume "p0<q")
(use "NatLtToLe")
(use "MStrMon")
(use "p0<q")
(assume "p0=q")
(simp "p0=q")
(use "Truth")
;; Assertion proved.
(assume "MMon")
(assert "exl n yNorm(f x)<<=n*a")
(use "RealLePosRatBound")
(use "RealyNorm")
(use "fBanachNorm")
(simp "xDef")
(use "IshiharaTrickAux" (pt "xSTimes") (pt "xNorm") (pt "xPlus") (pt "xUMinus")
     (pt "ySTimes") (pt "yNorm") (pt "xs") (pt "g") (pt "K") (pt "M"))
(use "InhB")
(use "BanachNormZero")
(use "xsB")
(use "xs1Def")
(use "BanachxSTimes")
(use "BanachxUMinus")
(use "BanachNormPlusInhab")
(use "BanachNormUMinus")
(use "BanachNormTimes")
(use "Conv")
(use "M0")
(use "MMon")
(use "KDef")
(use "NDef")
(use "RealxNorm")
(use "BanachxPlus")
(use "BLim")
;; IshiharaTrickAux successfully used
(use "0<a")
;; ?_65:exl n yNorm(f x)<<=n*a -> 
;;      exl m a<<=yNorm(f(xs m)) orl all m yNorm(f(xs m))<<=b
(assume "n0Ex")
(by-assume "n0Ex" "n0" "n0Prop")
;; We will often need monotonicity of K.
(assert "all n,m(n<=m -> K n<=K m)")
(assume "n" "m" "n<=m")
(simp "KDef")
(simp "KDef")
(use "MMon")
(simp "NatToPosLe")
(use "n<=m")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "KMon")
;; Now the main case distinction, on hn0=0
(cases (pt "H g K n0"))
;; 103,104
(assume "hn0=0")
(intro 1)
(assert "all n(n<=n0 -> H g K n=Zero)")
(assume "n" "n<=n0")
(use "H0DownMon" (pt "n0"))
(use "KMon")
(use "hn0=0")
(use "n<=n0")
;; Assertion proved.
(assume "all n(n<=n0 -> H g K n=Zero)")
(assert "all n(n0<n -> (H g K n=Zero -> F) -> F)")
(assume "n1" "n0<n1" "H g K n1=Zero -> F")
(assert "exd n exl m(n<=n1 andnc H g K n=Succ(Succ m))")
(use "HFind")
(simp "KDef")
(use "M0")
(use "H g K n1=Zero -> F")
(assume "ExHyp")
(by-assume "ExHyp" "n" "nProp")
(by-assume "nProp" "m" "mProp")
(use "NatLeLtCases" (pt "n") (pt "n0"))
;; 129,130
(assume "n<=n0")
(assert "H g K n=Zero")
(use "H0DownMon" (pt "n0"))
(use "KMon")
(use "hn0=0")
(use "n<=n0")
(simp "mProp")
(assume "Absurd")
(use "Absurd")
;; 130:n0<n -> F
;; Now derive a contradiction as Ishihara did, using H2Compl and HProp2gVal
(assert "xEq^(xSTimes n(xs m))x")
(use-with "H2Compl"
	  (pt "xSTimes") (pt "xNorm") (pt "xPlus") (pt "xUMinus") (pt "xLim")
	  (pt "x") (pt "n") (pt "m") (pt "M") (pt "xs") (pt "K")
	  (pt "xs1") (pt "N") (pt "g")
	  "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" "?")
;; 141-157
;; ?^141:xB^ x
(simp "xDef")
(use "IshiharaTrickAux" (pt "xSTimes") (pt "xNorm") (pt "xPlus") (pt "xUMinus")
     (pt "ySTimes") (pt "yNorm") (pt "xs") (pt "g") (pt "K") (pt "M"))
(use "InhB")
(use "BanachNormZero")
(use "xsB")
(use "xs1Def")
(use "BanachxSTimes")
(use "BanachxUMinus")
(use "BanachNormPlusInhab")
(use "BanachNormUMinus")
(use "BanachNormTimes")
(use "Conv")
(use "M0")
(use "MMon")
(use "KDef")
(use "NDef")
(use "RealxNorm")
(use "BanachxPlus")
(use "BLim")
;; IshiharaTrickAux successfully used
;; ?^142:all n xB^(xs1 n)
(assume "n2")
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
;; ?^143:all x(xB^ x -> Real(xNorm x))
(auto)
;;156:all p,n,m(N p<=n -> n<m -> xNorm(xPlus(xs1 n)(xUMinus(xs1 m)))<<=(1#2**p))
(use "VCauchy" (pt "xSTimes") (pt "M") (pt "xs") (pt "K") (pt "g"))
(auto)
;; ?^184:all n xB^(xs1 n)
(assume "n2")
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
;; ?^185:all x(xB^ x -> xB^(xUMinus x))
(auto)
;; ?^196:all n,m Real(xNorm(xPlus(xs1 n)(xUMinus(xs1 m))))
(assume "n2" "m2")
(use "RealxNorm")
(use "BanachxPlus")
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
(use "BanachxUMinus")
;; ?^210:xB^(xs1 m2)
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
;; ?^157:H g K n=Succ(Succ m)
(use "mProp")
;; ?^139:xEq^(xSTimes n(xs m))x -> n0<n -> F
;; Assertion proved.
(assume "xEq^(xSTimes n(xs m))x""n0<n")
(assert "g m")
(use "HProp2gVal" (pt "K") (pt "n"))
(use "mProp")
(use "KMon")
(use "Truth")
;; Assertion proved.
;; ?^216:g m -> F
(assume "gm")
(assert "a<<=yNorm(f(xs m))")
(use "gProp")
(use "gm")
;; Assertion proved.
;; ?^222:a<<=yNorm(f(xs m)) -> F
(assume "a<<=yNorm(f(xs m))")
(assert "RealTimes n a<<=n*yNorm(f(xs m))")
(use "RealLeMonTimesTwo")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "RatLtToLe")
(use "0<a")
(use "RatLeToRealLe")
(use "Truth")
(use "a<<=yNorm(f(xs m))")
;; Assertion proved.
;; ?^226:RealTimes n a<<=n*yNorm(f(xs m)) -> F
(assume "RealTimes n a<<=n*yNorm(f(xs m))")
(assert "RealTimes n a<<=yNorm(ySTimes n(f(xs m)))")
(use "RealLeCompat"
     (pt "RealConstr([n1]RatConstr(NatToInt n)One*a)([p]Zero)")
     (pt "n*yNorm(f(xs m))"))
(use "RealEqRefl")
(use "RealRat")
(simpreal "yNormTimes")
(use "RealEqRefl")
(use "RealTimesReal")
(use "RealRat")
(use "RealyNorm")
(use "fBanachNorm")
(use "xsB")
(use "fBanachNorm")
(use "xsB")
(use "RatLeToRealLe")
(use "Truth")
(use "RealTimes n a<<=n*yNorm(f(xs m))")
;; Assertion proved.
(assume "RealTimes n a<<=yNorm(ySTimes n(f(xs m)))")
;; Was
;; (assert "n*a<<=yNorm(f x)")
;; (use "BanachEqvCompat")
;; Instead we start from xEq^(xSTimes n(xs m))x and derive first
;; yEq^(f(xSTimes n(xs m)))(f x)) and then
;; yNorm(f(xSTimes n(xs m)))===yNorm(f x)
;; Then by compatibility of <<= with === we have n*a<<=yNorm(f x)


(assert "yEq^(f(xSTimes n(xs m)))(f x)")
(use "fCompat")
(use "BanachxSTimes")
(use "RealRat")
(use "xsB")
;; ?^257:xB^ x
(simp "xDef")
(use "IshiharaTrickAux" (pt "xSTimes") (pt "xNorm") (pt "xPlus") (pt "xUMinus")
     (pt "ySTimes") (pt "yNorm") (pt "xs") (pt "g") (pt "K") (pt "M"))
(use "InhB")
(use "BanachNormZero")
(use "xsB")
(use "xs1Def")
(use "BanachxSTimes")
(use "BanachxUMinus")
(use "BanachNormPlusInhab")
(use "BanachNormUMinus")
(use "BanachNormTimes")
(use "Conv")
(use "M0")
(use "MMon")
(use "KDef")
(use "NDef")
(use "RealxNorm")
(use "BanachxPlus")
(use "BLim")
;; IshiharaTrickAux successfully used
;; ?^258:xEq^(xSTimes n(xs m))x
(use "xEq^(xSTimes n(xs m))x")
;; ?^254:yEq^(f(xSTimes n(xs m)))(f x) -> F
(assume "yEq^(f(xSTimes n(xs m)))(f x)")
(assert "yNorm(f(xSTimes n(xs m)))===yNorm(f x)")
(use "yNormCompat")
(use "fBanachNorm")
(use "BanachxSTimes")
(use "RealRat")
(use "xsB")
(use "fBanachNorm")
(simp "xDef")
(use "BLim")
(use "VCauchy" (pt "xSTimes") (pt "M") (pt "xs") (pt "K") (pt "g"))
(auto)
;; ?^294:all n xB^(xs1 n)
(assume "n2")
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
;; ?^295:all x(xB^ x -> xB^(xUMinus x))
(auto)
;; ?^306:all n,m Real(xNorm(xPlus(xs1 n)(xUMinus(xs1 m))))
(assume "n2" "m2")
(use "RealxNorm")
(use "BanachxPlus")
;; ?^314:xB^(xs1 n2)
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
(use "BanachxUMinus")
;; ?^320:xB^(xs1 m2)
(simp "xs1Def")
(use "VB")
(use "InhB")
(use "xsB")
(use "BanachxSTimes")
;; ?^284:yEq^(f(xSTimes n(xs m)))(f x)
(use "yEq^(f(xSTimes n(xs m)))(f x)")
;; Assertion proved.
(assume "yNorm(f(xSTimes n(xs m)))===yNorm(f x)")
(assert "n*a<<=yNorm(f x)")
(use "RealLeCompat"
     (pt "RealConstr([nat]n*a)([p]Zero)") (pt "yNorm(f(xSTimes n(xs m)))"))
(use "RealEqRefl")
(use "RealRat")
(use "yNorm(f(xSTimes n(xs m)))===yNorm(f x)")
(simp "fLin*")
(use "RealTimes n a<<=yNorm(ySTimes n(f(xs m)))")
;; "Assertion proved.
(assume "n*a<<=yNorm(f x)")
;; With n0Prop: yNorm(f x)<<=n0*a we get n*a<=n0*a contradicting n0<n
(assert "n*a<=n0*a")
(use "RealLeTransRat" (pt "yNorm(f x)"))
(use "n*a<<=yNorm(f x)")
(use "n0Prop")
;; Assertion proved.
(assume "n*a<=n0*a")
(assert "n0*a<n*a")
(use "RatLtMonTimesNat")
(use "0<a")
(use "n0<n")
;; Assertion proved.
(assume "n0*a<n*a")
;; Assertion proved.
(assert "n*a<n*a")
(use "RatLeLtTrans" (pt "n0*a"))
(use "n*a<=n0*a")
(use "n0*a<n*a")
(assume "Absurd")
(use "Absurd")
;; ?^114:all n(n0<n -> (H g K n=Zero -> F) -> F) -> all m yNorm(f(xs m))<<=b
;; Here we need that M is strictly monotonic, to use HProp0Cor
(assume "all n(n0<n -> (H g K n=Zero -> F) -> F)")
(assert "all n H g K n=Zero")
(assume "n")
(use "NatLeLtCases" (pt "n") (pt "n0"))
(use "all n(n<=n0 -> H g K n=Zero)")
(assume "n0<n")
(use "StabAtom")
(use "all n(n0<n -> (H g K n=Zero -> F) -> F)")
(use "n0<n")
(assume "all n H g K n=Zero" "m")
(use "gProp")
(use "HProp01Cor" (pt "K") (pt "Succ m"))
(use "all n H g K n=Zero")
(assert "all n n<K(Succ n)")
(ind)
(use "NatLeLtTrans" (pt "K Zero"))
(simp "KDef")
(use "Truth")
(simp "KDef")
(simp "KDef")
(use "MStrMon")
(use "Truth")
(assume "n" "IH")
(use "NatLtLeTrans" (pt "Succ(K(Succ n))"))
(use "IH")
(use "NatLtToSuccLe")
(simp "KDef")
(simp "KDef")
(use "MStrMon")
(simp "NatToPosLt")
(use "Truth")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "all n n<K(Succ n)")
(use "all n n<K(Succ n)")
;; ?_104:all n(
;;        H g K n0=Succ n -> 
;;        exl m a<<=yNorm(f(xs m)) orl all m yNorm(f(xs m))<<=b)
(assume "n" "hn0=n+1")
(intro 0)
(assert "exd n1 exl m(n1<=n0 andnc H g K n1=m+2)")
(use "HFind")
(simp "KDef")
(use "M0")
(simp "hn0=n+1")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "exd n1 exl m(n1<=n0 andnc H g K n1=m+2)")
(by-assume "exd n1 exl m(n1<=n0 andnc H g K n1=m+2)" "n1" "n1Prop")
(by-assume "n1Prop" "m" "mProp")
(intro 0 (pt "m"))
(use "gProp")
(use "HProp2gVal" (pt "K") (pt "n1"))
(use "mProp")
(use "KMon")
(use "Truth")
;; ?_16:exl g 
;;       all m(
;;        (g m -> a<<=yNorm(f(xs m))) andnc ((g m -> F) -> yNorm(f(xs m))<<=b))
(intro 0 (pt "[m]negb(g1 m)"))
(ng #t)
(assume "m")
(split)
(assume "negb(g1 m)")
(use "g1Prop")
(cases (pt "g1 m"))
(assume "g1 m" "Useless")
(simphyp-with-to "negb(g1 m)" "g1 m" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "negb(g1 m) -> F")
(use "g1Prop")
(cases (pt "g1 m"))
(strip)
(use "Truth")
(assume "g1 m -> F")
(use "negb(g1 m) -> F")
(simp "g1 m -> F")
(use "Truth")
;; Proof finished.
;; (cp)

(define eterm (proof-to-extracted-term))

(remove-computation-rules-for (pt "H g K n"))
;; (display-pconst "V")
(remove-computation-rules-for (pt "(V alpha)xSTimes g K xs n"))
(remove-computation-rules-for (pt "NatToPos n"))

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [xSTimes,xLim,yNorm,f,xs,M,a,a0,p]
;;  [let g
;;    ([n]negb(cAC([n0]cApproxSplitBooleRat a a0(yNorm(f(xs n0)))p)n))
;;    [case (H g([n]M(NatToPos(Succ n)))
;;           (cRealLePosRatBound
;;            (yNorm
;;             (f
;;              (xLim(V xSTimes g([n]M(NatToPos(Succ n)))xs)
;;               ([p0]NatDouble(PosToNat p0)))))
;;            a))
;;     (Zero -> DummyR)
;;     (Succ n -> 
;;     Inl[case (cHFind g([n0]M(NatToPos(Succ n0)))
;;                (cRealLePosRatBound
;;                 (yNorm
;;                  (f
;;                   (xLim(V xSTimes g([n0]M(NatToPos(Succ n0)))xs)
;;                    ([p0]NatDouble(PosToNat p0)))))
;;                 a))
;;          (n0 pair n1 -> n1)])]]

;; Again we revive the computation rules for NatToPos

(add-computation-rules
 "NatToPosStep n(nat=>pos)"
 "[if (NatEven n)
      (SZero((nat=>pos)(NatHalf n)))
      [if (n=Succ Zero) One (SOne((nat=>pos)(NatHalf n)))]]")

(add-computation-rules
 "NatToPos n" "(GRec nat pos)([n]n)n NatToPosStep")

(add-computation-rules "H g K n" "HitPast g K(K n)n")

(add-computation-rules
 "(V alpha)xSTimes g K xs n" "(Seq alpha)xSTimes(H g K)(H g K n)xs n")

 
