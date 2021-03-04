;; 2021-03-04.  rseq.scm.  Based on Jan Belle's exp.scm.

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "list.scm")
;; (libload "pos.scm")
;; (libload "int.scm")
;; (libload "rat.scm")
;; (libload "rea.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")")
    (if (not (assoc "pos" ALGEBRAS))
	(myerror "First execute (libload \"pos.scm\")")
	(if (not (assoc "int" ALGEBRAS))
	    (myerror "First execute (libload \"int.scm\")")
	    (if (not (assoc "rat" ALGEBRAS))
		(myerror "First execute (libload \"rat.scm\")")
		(if (not (assoc "rea" ALGEBRAS))
		    (myerror "First execute (libload \"rea.scm\")"))))))

(display "loading rseq.scm ...") (newline)

;; 1.  Completeness
;; ================

;; The real numbers were built by completion of the rationals viewed as
;; metric space.  We show that a further completion (this time of the
;; reals) does not yield anything new, i.e., that every Cauchy sequence
;; xs of reals with modulus M converges (even with the same modulus) to
;; an already existing real, defined as RealLim xs M.  This is the
;; content of the theorem RealComplete below.

;; The first part uses work of Max Zeuner (semws18/completeness.scm) and
;; Wolfgang Boehnisch (semws19/completeness.scm).  The second part is
;; based on Jan Belle's Master Thesis (2021).

;; To define RealLim we need to diagonalize.

(add-var-name "ass" (py "nat=>nat=>rat"))
(add-var-name "Ns" (py "nat=>pos=>nat"))

;; In RealSeqApprox we use cNatPos for the following reason.  Unfolding
;; NatToPos n is complex: because of the binary structure of pos GRec
;; is used.  Hence we use cNatPos instead (with NatPos deanimated) and
;; NatPosExFree : all n cNatPos n=NatToPos n

;; RealSeqApprox
(set-goal "all ass,Ns,xs,bs(
 all n xs n eqd RealConstr(ass n)(Ns n) ->
 all n Real(xs n) ->
 all n bs n=ass n(Ns n(cNatPos n)) ->
 all n abs(bs n+ ~(xs n))<<=(1#2**n))")
(assume "ass" "Ns" "xs" "bs" "xsDef" "Rxs" "bsDef" "n")
(use "RealLeTrans" (pt "RealConstr([n0](1#2**cNatPos n))([p]Zero)"))
;; 3,4
(simp "xsDef")
(simp "bsDef")
(use "RatCauchyConvMod")
(simp "<-" "xsDef")
(use "Rxs")
(use "Truth")
;; ?^4:(1#2**cNatPos n)<<=(1#2**n)
(use "RatLeToRealLe")
(simp "RatLe0CompRule")
(simp "IntTimes2RewRule")
(simp "IntTimes2RewRule")
(simp "IntLe4CompRule")
(use "PosLeMonPosExp")
(simp "NatPosExFree")
(cases (pt "n"))
(assume "Useless")
(use "Truth")
(assume "n0" "Useless")
(simp "PosToNatToPosId")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealSeqApprox")

;; RealCauchyApprox
(set-goal "all ass,Ns,xs,M,bs,L(
 all n Real(xs n) ->
 all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) ->
 all n xs n eqd RealConstr(ass n)(Ns n) ->
 all n bs n=ass n(Ns n(cNatPos n)) ->
 all p L p=M(PosS p)max PosS(PosS p) ->
 all p,n,m(L p<=n -> L p<=m -> abs(bs n+ ~(bs m))<<=(1#2**p)))")
(assume "ass" "Ns" "xs" "M" "bs" "L" "Rxs" "xsCs" "xsDef" "bsDef" "LDef"
	"p" "n" "m" "nBd" "mBd")
;; Split (1#2**p)
(use "RealLeTrans" (pt "RealPlus(1#2**n)(1#2**PosS p)+(1#2**m)"))
;; 3,4
;; ?^3:abs(bs n+ ~(bs m))<<=RealPlus(1#2**n)(1#2**PosS p)+(1#2**m)
;; First replace ~,+,abs on rat by their counterparts on rea
(use "RealLeTrans" (pt "abs(bs n+RealUMinus(bs m))"))
;; 5,6
(simpreal "<-" "RatUMinusRealUMinus")
(simpreal "<-" "RatPlusRealPlus")
(simpreal "<-" "RatAbsRealAbs")
(use "RealLeRefl")
(autoreal)
;; 6
(simpreal
 (pf "bs n+RealUMinus(bs m)===bs n+ ~(xs n)+(xs n+ RealUMinus(bs m))"))
;; This will be proved by RealPlusInsert
(use "RealLeTrans" (pt "abs(bs n+ ~(xs n))+abs(xs n+ RealUMinus(bs m))"))
(use "RealLeAbsPlus")
(autoreal)
(simpreal "<-" "RealPlusAssoc")
(use "RealLeMonPlusTwo")
;; 21,22
;; ?^22:abs(xs n+ ~(bs m))<<=RealPlus(1#2**PosS p)(1#2**m)
;; ?^21:abs(bs n+ ~(xs n))<<=(1#2**n)
(use "RealSeqApprox" (pt "ass") (pt "Ns"))
(use "xsDef")
(use "Rxs")
(use "bsDef")
;; 22
;; Here with RealUMinus
(simpreal
 (pf "xs n+RealUMinus(bs m)===xs n+ ~(xs m)+(xs m+ RealUMinus(bs m))"))
;; 26,27
;; 26 will be proved by RealPlusInsert
(use "RealLeTrans" (pt "abs(xs n+ ~(xs m))+abs(xs m+ RealUMinus(bs m))"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
(use "xsCs")
(use "NatLeTrans" (pt "L p"))
(simp "LDef")
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "L p"))
(simp "LDef")
(use "NatMaxUB1")
(use "mBd")
;; ?^39:abs(xs m+ ~(bs m))<<=(1#2**m)
(simpreal "RealPlusComm")
(simpreal "<-" "RealAbsUMinus")
(simpreal "RealUMinusPlus")
(simpreal "RealUMinusUMinus")
;; ?^50:abs(bs m+ ~(xs m))<<=(1#2**m)
(use "RealSeqApprox" (pt "ass") (pt "Ns"))
(use "xsDef")
(use "Rxs")
(use "bsDef")
(autoreal)
;; ?^27:xs n+ ~(bs m)===xs n+ ~(xs m)+(xs m+ ~(bs m))
(use "RealPlusInsert")
(autoreal)
;; ?^12:bs n+ ~(bs m)===bs n+ ~(xs n)+(xs n+ ~(bs m))
(use "RealPlusInsert")
(autoreal)
;; ?^4:RealPlus(1#2**n)(1#2**PosS p)+(1#2**m)<<=(1#2**p)
(simpreal "<-" "RatPlusRealPlus")
(simpreal "<-" "RatPlusRealPlus")
(use "RatLeToRealLe")
(use "RatLeTrans" (pt "(1#2**PosS(PosS p))+(1#2**PosS p)+(1#2**PosS(PosS p))"))
(use "RatLeMonPlus")
(use "RatLeMonPlus")
(ng #t)
(use "PosLeMonPosExp")
(use "NatLeTrans" (pt "L p"))
(simp "LDef")
(use "NatMaxUB2")
(use "nBd")
(use "Truth")
(ng #t)
(use "PosLeMonPosExp")
(use "NatLeTrans" (pt "L p"))
(simp "LDef")
(use "NatMaxUB2")
(use "mBd")
;; ?^65:(1#2**PosS(PosS p))+(1#2**PosS p)+(1#2**PosS(PosS p))<=(1#2**p)
(simp
 (pf "(1#2**PosS(PosS p))+(1#2**PosS p)=(1#2**PosS p)+(1#2**PosS(PosS p))"))
(simp "<-" "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(simprat "RatPlusHalfExpPosS")
(use "RatLeRefl")
(use "Truth")
(use "RatPlusComm")
;; Proof finished.
;; (cdp)
(save "RealCauchyApprox")

(add-program-constant "RealLim" (py "(nat=>rea)=>(pos=>nat)=>rea"))

(add-computation-rules
 "RealLim xs M"
 "RealConstr([n](xs n)seq((xs n)mod(cNatPos n)))
            ([p]M(PosS p)max PosS(PosS p))")

;; RealLimTotal
(set-totality-goal "RealLim")
(assume "xs^" "Txs" "M^" "TM")
(ng)
(intro 0)
(fold-alltotal)
(assume "n")
(use "RealSeqTotal")
(use "Txs")
(use "NatTotalVar")
(use "RealModTotal")
(use "Txs")
(use "NatTotalVar")
(use "PosTotalVar")
;; 5
(fold-alltotal)
(assume "p")
(use "NatMaxTotal")
(use "TM")
(use "PosTotalVar")
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; RealLimReal
(set-goal "all xs,M(
     all n Real(xs n) -> 
     all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
     all p,q(p<=q -> M p<=M q) ->
     Real(RealLim xs M))")
(assume "xs" "M" "Rxs" "xsCs" "MMon")
(intro 0)
;; 3,4
(intro 0)
(assume "p" "n" "m" "nBd" "mBd")
(use "RealLeToRatLe")
(ng #t)
;; To apply RealCauchyApprox we need assDef NsDef xsChar bsDef LDef
;; Introduce assDef
(assert "exl ass all n ass n eqd(xs n)seq")
(intro 0 (pt "[n](xs n)seq"))
(assume "n1")
(use "InitEqD")
(assume "assEx")
(by-assume "assEx" "ass" "assDef")
;; Introduce NsDef
(assert "exl Ns all n Ns n eqd(xs n)mod")
(intro 0 (pt "[n](xs n)mod"))
(assume "n1")
(use "InitEqD")
(assume "NsEx")
(by-assume "NsEx" "Ns" "NsDef")
;; Introduce xsChar
(assert "all n xs n eqd RealConstr(ass n)(Ns n)")
(assume "n1")
(simp "assDef")
(simp "NsDef")
(cases (pt "xs n1"))
(ng #t)
(assume "as" "M1" "Useless")
(use "InitEqD")
(assume "xsChar")
;; Introduce bsDef
(assert "exl bs all n bs n =ass n(Ns n(cNatPos n))")
(intro 0 (pt "[n]ass n(Ns n(cNatPos n))"))
(assume "n1")
(use "Truth")
(assume "bsEx")
(by-assume "bsEx" "bs" "bsDef")
;; Introduce LDef
(assert "exl L all p L p=M(PosS p)max PosS(PosS p)")
(intro 0 (pt "[p]M(PosS p)max PosS(PosS p)"))
(assume "p1")
(use "Truth")
(assume "LEx")
(by-assume "LEx" "L" "LDef")
(simp "<-" "assDef")
(simp "<-" "NsDef")
(simp "<-" "bsDef")
(simp "<-" "assDef")
(simp "<-" "NsDef")
(simp "<-" "bsDef")
(use "RealCauchyApprox" (pt "ass") (pt "Ns") (pt "xs") (pt "M") (pt "L"))
(use "Rxs")
(use "xsCs")
(use "xsChar")
(use "bsDef")
(use "LDef")
;; ?^61:L p<=n
(simp "LDef")
(use "NatLeTrans" (pt "(RealLim xs M)mod p"))
(ng #t)
(use "Truth")
(use "nBd")
(use "NatLeTrans" (pt "(RealLim xs M)mod p"))
(simp "LDef")
(use "Truth")
(use "mBd")
;; ?^4:Mon((RealLim xs M)mod)
(intro 0)
(assume "p" "q" "p<=q")
(ng #t)
(use "NatLeMonMax")
(use "MMon")
(use "p<=q")
(simp "PosToNatLe")
(use "p<=q")
;; Proof finished.
;; (cdp)
(save "RealLimReal")

;; RealCauchyConvMod
(set-goal "all ass,Ns,xs,M,bs,L,x(
 all n xs n eqd RealConstr(ass n)(Ns n) ->
 all n Real(xs n) ->
 all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) ->
 all p,q(p<=q -> M p<=M q) ->
 all n bs n=ass n(Ns n(cNatPos n)) ->
 all q L q=M(PosS q)max PosS(PosS q) ->
 x===RealConstr bs L ->
 all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)))")
(assume "ass" "Ns" "xs" "M" "bs" "L" "x" "xsDef" "Rxs" "xsCs" "MMon" "bsDef"
	"LDef" "xEq" "p" "n" "nBd")
(use "RealLeAllPlusToLe")
(autoreal)
(assume "q")
;; ?^6:abs(xs n+ ~x)<<=RealPlus(1#2**p)(1#2**q)
(defnc "m" "(M p)max(PosS q max L(PosS q))")
(simpreal (pf "xs n+ ~x===xs n+ ~(xs m)+((xs m)+ ~x)"))
(use "RealLeTrans" (pt "abs(xs n+ ~(xs m))+abs(xs m+ ~x)"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
;; 20,21
;; ?^20:abs(xs n+ ~(xs m))<<=(1#2**p)
(use "xsCs")
(use "nBd")
(simp "mDef")
(use "NatMaxUB1")
;; ?^21:abs(xs m+ ~x)<<=(1#2**q)
(simpreal (pf "(1#2**q)===RealPlus(1#2**PosS q)(1#2**PosS q)"))
;; 25,26
;; ?^26:(1#2**q)===RealPlus(1#2**PosS q)(1#2**PosS q) will be provable by
;; RatPlusHalfExpPosS
(simpreal (pf "xs m+ ~x===xs m+RealUMinus(bs m)+(bs m+ ~x)"))
(use "RealLeTrans" (pt "abs(xs m+RealUMinus(bs m))+abs(bs m+ ~x)"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
;; ?^33:abs(xs m+ ~(bs m))<<=(1#2**PosS q)
(simpreal "RealPlusComm")
(simpreal "<-" "RealAbsUMinus")
(simpreal "RealUMinusPlus")
(simpreal "RealUMinusUMinus")
;; ?^43:abs(bs m+ ~(xs m))<<=(1#2**PosS q)
(use "RealLeTrans" (pt "RealConstr([n](1#2**m))([p]Zero)"))
(use "RealSeqApprox" (pt "ass") (pt "Ns"))
(use "xsDef")
(use "Rxs")
(use "bsDef")
;; ?^46:(1#2**m)<<=(1#2**PosS q)
(use "RatLeToRealLe")
(simp "RatLe0CompRule")
(simp "IntTimes2RewRule")
(simp "IntTimes2RewRule")
(simp "IntLe4CompRule")
(use "PosLeMonPosExp")
(simp "mDef")
(use "NatLeTrans" (pt "PosS q max L(PosS q)"))
(use "NatMaxUB1")
(use "NatMaxUB2")
(autoreal)
;; ?^34:abs(bs m+ ~x)<<=(1#2**PosS q)
(simpreal "xEq")
(use "RatCauchyConvMod")
(autoreal)
(simp "mDef")
(use "NatLeTrans" (pt "PosS q max L(PosS q)"))
(use "NatMaxUB2")
(use "NatMaxUB2")
;; ?^28:xs m+ ~x===xs m+ ~(bs m)+(bs m+ ~x)
(use "RealPlusInsert")
(autoreal)
;; ?^26:(1#2**q)===RealPlus(1#2**PosS q)(1#2**PosS q)
(simpreal "<-" "RatPlusRealPlus")
(use "RatEqvToRealEq")
(simprat "RatPlusHalfExpPosS")
(use "Truth")
;; ?^15:xs n+ ~x===xs n+ ~(xs m)+(xs m+ ~x)
(use "RealPlusInsert")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealCauchyConvMod")

;; Every Cauchy sequence xs of reals with monotone modulus M converges
;; with the same modulus M to its limit RealLim xs M

;; RealComplete
(set-goal "all xs,M(
 all n Real(xs n) -> 
 all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
 all p,q(p<=q -> M p<=M q) ->
 all p,n(M p<=n -> abs(xs n+ ~(RealLim xs M))<<=(1#2**p)))")
(assume "xs" "M" "Rxs" "xsCs" "MMon")

;; Introduce assDef
(assert "exl ass all n ass n eqd(xs n)seq")
(intro 0 (pt "[n](xs n)seq"))
(assume "n1")
(use "InitEqD")
(assume "assEx")
(by-assume "assEx" "ass" "assDef")

;; Introduce NsDef
(assert "exl Ns all n Ns n eqd(xs n)mod")
(intro 0 (pt "[n](xs n)mod"))
(assume "n1")
(use "InitEqD")
(assume "NsEx")
(by-assume "NsEx" "Ns" "NsDef")

;; Introduce xsChar
(assert "all n xs n eqd RealConstr(ass n)(Ns n)")
(assume "n1")
(simp "assDef")
(simp "NsDef")
(cases (pt "xs n1"))
(ng #t)
(assume "as" "M1" "Useless")
(use "InitEqD")
(assume "xsChar")

;; Introduce bsDef
(assert "exl bs all n bs n =ass n(Ns n(cNatPos n))")
(intro 0 (pt "[n]ass n(Ns n(cNatPos n))"))
(assume "n1")
(use "Truth")
(assume "bsEx")
(by-assume "bsEx" "bs" "bsDef")

;; Introduce LDef
(assert "exl L all p L p=M(PosS p)max PosS(PosS p)")
(intro 0 (pt "[p]M(PosS p)max PosS(PosS p)"))
(assume "p1")
(use "Truth")
(assume "LEx")
(by-assume "LEx" "L" "LDef")

;; ?^43:all p,n(M p<=n -> abs(xs n+ ~(RealLim xs M))<<=(1#2**p))
(assume "p" "n")
(use "RealCauchyConvMod" (pt "ass") (pt"Ns") (pt "bs") (pt "L"))
(use "xsChar")
(use "Rxs")
(use "xsCs")
(use "MMon")
(use "bsDef")
(use "LDef")
;; ?^51:RealLim xs M===RealConstr bs L
(use "RealSeqEqToEq" (pt "Zero"))
(use "RealLimReal")
(use "Rxs")
(use "xsCs")
(use "MMon")
;; ?^53:Real(RealConstr bs L)
(intro 0)
(ng #t)
(intro 0)
(assume "p1" "n1" "m1" "n1Bd" "m1Bd")
(use "RealLeToRatLe")
(use "RealCauchyApprox" (pt "ass") (pt "Ns") (pt "xs") (pt "M") (pt "L"))
(use "Rxs")
(use "xsCs")
(use "xsChar")
(use "bsDef")
(use "LDef")
(use "n1Bd")
(use "m1Bd")
(intro 0)
(assume "p1" "q1" "p1<=q1")
(ng #t)
(simp "LDef")
(simp "LDef")
(use "NatLeMonMax")
(use "MMon")
(use "p1<=q1")
(simp "PosToNatLe")
(use "p1<=q1")
;; ?^54:all n(Zero<=n -> (RealLim xs M)seq n==(RealConstr bs L)seq n)
(assume "n1" "Useless")
(ng #t)
(simp "xsChar")
(ng #t)
(simp "bsDef")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealComplete")

;; 2.  Convergence
;; ===============

;; We prove further properties of RealConv.  Using the predicate
;; RealConv we can write RealComplete as follows.

;; RealConvLim
(set-goal "all xs,M(
 all n Real(xs n) -> 
 all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
 all p,q(p<=q -> M p<=M q) -> RealConv xs(RealLim xs M)M)")
(assume "xs" "M" "Rxs" "xsCs" "MMon")
(intro 0)
;; 3-6
(use "Rxs")
;; 4
(use "RealLimReal")
;; 7-9
(use "Rxs")
(use "xsCs")
(use "MMon")
;; 5
(intro 0)
(use "MMon")
;; 6
(use "RealComplete")
(use "Rxs")
(use "xsCs")
(use "MMon")
;; Proof finished.
;; (cdp)
(save "RealConvLim")

;; RealConvUniq
(set-goal "all xs,y,M,z,N(RealConv xs y M -> RealConv xs z N -> y===z)")
(assume "xs" "y" "M" "z" "N" "xsyConv" "xszConv")
(use "RealConvEq" (pt "xs") (pt "xs") (pt "M") (pt "N"))
(inst-with-to "RealConvElim1" (pt "xs") (pt "y") (pt "M") "xsyConv" "Rxs")
(assume "n")
(use "RealEqRefl")
(use "Rxs")
(use "xsyConv")
(use "xszConv")
;; Proof finished.
;; (cdp)
(save "RealConvUniq")

;; RealConvCompat
(set-goal "all xs,x,M,ys,y,N(all n(xs n===ys n) -> x===y -> all p(M p=N p) ->
 RealConv xs x M -> RealConv ys y N)")
(assume "xs" "x" "M" "ys" "y" "N" "xs=ys" "x=y" "M=N" "CxsxM")
(intro 0)
;; 3-6
(assume "n")
(autoreal)
;; ?^5:Mon N
(intro 0)
(assume "p" "q" "p<=q")
(simp "<-" "M=N")
(simp "<-" "M=N")
(use "MonElim")
(use "RealConvElim3" (pt "xs") (pt "x"))
(use "CxsxM")
(use "p<=q")
;; ?^6:all p,n(N p<=n -> abs(ys n+ ~y)<<=(1#2**p))
(assume "p" "n" "nBd")
(simpreal "<-" "xs=ys")
(simpreal "<-" "x=y")
(use "RealConvElim4" (pt "M"))
(use "CxsxM")
(simp "M=N")
(use "nBd")
;; Proof finished.
;; (cdp)
(save "RealConvCompat")

;; RealConvMonLe
(set-goal "all xs,x,M,N(RealConv xs x M -> Mon N -> all p M p<=N p -> 
 RealConv xs x N)")
(assume "xs" "x" "M" "N" "CxsxM" "NMon" "M<=N")
(intro 0)
;; 3-6
(use "RealConvElim1" (pt "x") (pt "M"))
(use "CxsxM")
(autoreal)
;; 5
(use "NMon")
;; ?^6:all p,n(N p<=n -> abs(xs n+ ~x)<<=(1#2**p))
(assume "p" "n" "nBd")
(use "RealConvElim4" (pt "M"))
(use "CxsxM")
(use "NatLeTrans" (pt "N p"))
(use "M<=N")
(use "nBd")
;; Proof finished.
;; (cdp)
(save "RealConvMonLe")

;; RealConvPlusConstR
(set-goal "all xs,x,M,y(RealConv xs x M -> Real y ->
 RealConv([n]xs n+y)(x+y)M)")
(assume "xs" "x" "M" "y" "CxsxM" "Ry")
(intro 0)
;; 3-6
(assume "n")
(ng #t)
(autoreal)
;; ?^5:Mon M
(use "RealConvElim3" (pt "xs") (pt "x"))
(use "CxsxM")
;; 6
(ng #t)
;; ?^10:all p,n(M p<=n -> abs(xs n+y+ ~(x+y))<<=(1#2**p))
(assume "p" "n" "nBd")
(simpreal (pf "x+y===y+x"))
(simpreal "RealUMinusPlus")
(simpreal (pf "xs n+y+(~y+ ~x)===xs n+(y+ ~y+ ~x)"))
(simpreal "RealPlusMinusZero")
(simpreal "RealZeroPlus")
;; ?^21:abs(xs n+ ~x)<<=(1#2**p)
(use "RealConvElim4" (pt "M"))
(use "CxsxM")
(use "nBd")
(autoreal)
;; ?^18:xs n+y+(~y+ ~x)===xs n+(y+ ~y+ ~x)
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealConvPlusConstR")

;; RealConvPlusConstL
(set-goal "all xs,x,M,y(RealConv xs x M -> Real y ->
 RealConv([n]y+xs n)(y+x)M)")
(assume "xs" "x" "M" "y" "CxsxM" "Ry")
(intro 0)
;; 3-6
(assume "n")
(ng #t)
(autoreal)
;; ?^5:Mon M
(use "RealConvElim3" (pt "xs") (pt "x"))
(use "CxsxM")
;; ?^6:all p,n(M p<=n -> abs(([n0]y+xs n0)n+ ~(y+x))<<=(1#2**p))
(ng #t)
;; ?^10:all p,n(M p<=n -> abs(y+xs n+ ~(y+x))<<=(1#2**p))
(assume "p" "n" "nBd")
(simpreal "RealUMinusPlus")
(simpreal (pf "y+xs n===xs n+y"))
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "y+(~y+ ~x)===y+ ~y+ ~x"))
(simpreal "RealPlusMinusZero")
(simpreal "RealZeroPlus")
;; ?^25:abs(xs n+ ~x)<<=(1#2**p)
(use "RealConvElim4" (pt "M"))
(use "CxsxM")
(use "nBd")
(autoreal)
;; ?^22:y+(~y+ ~x)===y+ ~y+ ~x
(simpreal "RealPlusAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealConvPlusConstL")

;; RealConvPlus
(set-goal "all xs,x,M,ys,y,N(
 RealConv xs x M -> 
 RealConv ys y N -> RealConv([n]xs n+ys n)(x+y)([p]M(PosS p)max N(PosS p)))")
(assume "xs" "x" "M" "ys" "y" "N" "xsxConv" "ysyConv")
(intro 0)
;; 3-6
;; ?^3:allnc n Real(([n0]xs n0+ys n0)n)
(assume "n")
(ng #t)
;; ?^8:Real(xs n+ys n)
(autoreal)
;; ?^5:Mon([p]M(PosS p)max N(PosS p))
(intro 0)
(ng #t)
(assume "p" "q" "p<=q")
(use "NatLeMonMax")
(use "MonElim")
(use "RealConvElim3" (pt "xs") (pt "x"))
(use "xsxConv")
(use "p<=q")
(use "MonElim")
(use "RealConvElim3" (pt "ys") (pt "y"))
(use "ysyConv")
(use "p<=q")
;; 6
(assume "p" "n")
(ng #t)
;; ?^21:M(PosS p)max N(PosS p)<=n -> abs(xs n+ys n+ ~(x+y))<<=(1#2**p)
(assume "nBd")
(simpreal (pf "xs n+ys n+ ~(x+y)===xs n+ ~x+(ys n+ ~y)"))
;; 23,24
(use "RealLeTrans" (pt "abs(xs n+ ~x)+abs(ys n+ ~y)"))
(use "RealLeAbsPlus")
(autoreal)
;; ?^26:abs(xs n+ ~x)+abs(ys n+ ~y)<<=(1#2**p)
(use "RealLeTrans" (pt "RealPlus(1#2**PosS p)(1#2**PosS p)"))
(use "RealLeMonPlusTwo")
(use "RealConvElim4" (pt "M"))
(use "xsxConv")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS p)"))
(use "NatMaxUB1")
(use "nBd")
;; ?^32:abs(ys n+ ~y)<<=(1#2**PosS p)
(use "RealConvElim4" (pt "N"))
(use "ysyConv")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS p)"))
(use "NatMaxUB2")
(use "nBd")
;; ?^30:RealPlus(1#2**PosS p)(1#2**PosS p)<<=(1#2**p)
(use "RatLeToRealLe")
(simprat
 (pf "(2**PosS p+2**PosS p#2**PosS p*2**PosS p)==(1#2**PosS p)+(1#2**PosS p)"))
(simprat "RatPlusHalfExpPosS")
(use "Truth")
(use "Truth")
;; ?^24:xs n+ys n+ ~(x+y)===xs n+ ~x+(ys n+ ~y)
(simpreal "RealUMinusPlus")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealPlusComm")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealConvPlus")

;; RealConvUMinus
(set-goal "all xs,x,M(RealConv xs x M -> RealConv([n]~(xs n))(~x)M)")
(assume "xs" "x" "M" "xsxConv")
(intro 0)
;; 3-6
(assume "n")
(ng #t)
(autoreal)
;; ?^5:Mon M
(use "RealConvElim3" (pt "xs") (pt "x"))
(use "xsxConv")
;; ?^6:allnc p,n(M p<=n -> abs(([n0]~(xs n0))n+ ~ ~x)<<=(1#2**p))
(assume "p" "n" "nBd")
(ng #t)
;; ?^11:abs(~(xs n)+ ~ ~x)<<=(1#2**p)
(simpreal "<-" "RealUMinusPlus")
(simpreal "RealAbsUMinus")
(use "RealConvElim4" (pt "M"))
(use "xsxConv")
(use "nBd")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealConvUMinus")

;; RealConvTimesConstR
(set-goal "all xs,x,M,y,q(RealConv xs x M -> Real y -> abs y<<=2**q ->
 RealConv([n]xs n*y)(x*y)([p]M(p+q)))")
(assume "xs" "x" "M" "y" "q" "CxsxM" "Ry" "yBd")
(intro 0)
;; 3-6
(assume "n")
(ng #t)
(autoreal)
;; ?^5:Mon([p]M(p+q))
(intro 0)
(assume "p" "r" "p<=r")
(ng #t)
(use "MonElim")
(use "RealConvElim3" (pt "xs") (pt "x"))
(use "CxsxM")
(use "p<=r")
;; 6
(ng #t)
(assume "p" "n" "nBd")
(simpreal "<-" "RealTimesUMinusId")
(simpreal "<-" "RealTimesPlusDistrLeft")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes(1#2**(p+q))(2**q)"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
;; ?^31:abs(xs n+ ~x)<<=(1#2**(p+q))
(use "RealConvElim4" (pt "M"))
(use "CxsxM")
(use "nBd")
(use "yBd")
;; ?^28:RealTimes(1#2**(p+q))(2**q)<<=(1#2**p)
(use "RatLeToRealLe")
(ng #t)
(simp "PosExpTwoPosPlus")
(simp "PosPlusComm")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealConvTimesConstR")

;; RealConvTimesConstL
(set-goal "all xs,x,M,y,q(RealConv xs x M -> Real y -> abs y<<=2**q ->
 RealConv([n]y*xs n)(y*x)([p]M(p+q)))")
(assume "xs" "x" "M" "y" "q" "CxsxM" "Ry" "yBd")
(intro 0)
;; 3-6
(assume "n")
(ng #t)
(autoreal)
;; ?^5:Mon([p]M(p+q))
(intro 0)
(assume "p" "r" "p<=r")
(ng #t)
(use "MonElim")
(use "RealConvElim3" (pt "xs") (pt "x"))
(use "CxsxM")
(use "p<=r")
;; 6
(ng #t)
(assume "p" "n" "nBd")
;; ?^16:abs(y*xs n+ ~(y*x))<<=(1#2**p)
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes(2**q)(1#2**(p+q))"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "yBd")
;; ?^32:abs(xs n+ ~x)<<=(1#2**(p+q))
(use "RealConvElim4" (pt "M"))
(use "CxsxM")
(use "nBd")
;; ?^28:RealTimes(1#2**(p+q))(2**q)<<=(1#2**p)
(use "RatLeToRealLe")
(ng #t)
(simp "PosExpTwoPosPlus")
(simp "PosPlusComm")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealConvTimesConstL")

;; For RealConvTimes we need bounds, as for RealTimesReal.  This could
;; be done directly, by transferring the previous bound constructions.
;; Here we proceed differently, via RCpl.  The reasons are (1) that we
;; can then use previous work of Jan Belle who proved RCplTimesRCpl,
;; and (2) that a study of RCpl in interesting in itself (it is
;; parallel to the completion MCpl of metric spaces in metr.scm).

;; We generally study Cauchy sequences xs of reals with modulus M.  We
;; view pairs (xs,M) as points v in the completion RCpl of the reals.
;; For such pairs we define the standard arithmetical operations,
;; which involves an explicit construction of the modulus.

(add-ids
 (list (list "RCauchy" (make-arity (py "nat=>rea") (py "pos=>nat"))))
 '("allnc xs,M(
    allnc p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) ->
    RCauchy xs M)" "RCauchyIntro"))

;; RCauchyElim
(set-goal "allnc xs,M(RCauchy xs M ->
    allnc p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)))")
(assume "xs" "M")
(elim)
(search)
;; Proof finished.
;; (cdp)
(save "RCauchyElim")

;; RCauchyIntro2  ;strengthened since a premise is weakened: assumes m<=n
(set-goal "all xs,M(
     all n Real(xs n) -> 
     all p,n,m(M p<=n -> M p<=m -> m<=n -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
     RCauchy xs M)")
(assume "xs" "M" "Rxs" "Cauchyxs")
(use "RCauchyIntro")
(assume "p" "n" "m" "Mp<=n" "Mp<=m")
(cases (pt "m<=n"))
(assume "m<=n")
(use "Cauchyxs")
(use "Mp<=n")
(use "Mp<=m")
(use "m<=n")
(assume "m</=n")
(use "RealLeCompat"
     (pt "abs (xs m+ ~(xs n))") (pt "RealConstr([n]1#2**p)([p]Zero)"))
(use "RealAbsPlusUMinus")
(autoreal)
(use "RealEqRefl")
(autoreal)
(use "Cauchyxs")
(use "Mp<=m")
(use "Mp<=n")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "m</=n")
;; Proof finished.
;; (cdp)
(save "RCauchyIntro2")

;; 2020-11-23.  We study the completion of real numbers.

(add-var-name "v" (py "(nat=>rea)yprod(pos=>nat)"))

(add-ids
 (list (list "RCpl" (make-arity (py "(nat=>rea)yprod(pos=>nat)"))))
 '("allnc v(
   allnc n Real(lft v n) ->  RCauchy(lft v)(rht v) -> Mon(rht v) -> RCpl v)"
   "RCplIntro"))

;; RCplToR
(set-goal "allnc v(RCpl v -> allnc n Real(lft v n))")
(assume "v" "Pv")
(elim "Pv")
(search)
;; Proof finished.
;; (cdp)
(save "RCplToR")

;; RCplToRCauchy
(set-goal "allnc v(RCpl v -> RCauchy(lft v)(rht v))")
(assume "v" "Pv")
(elim "Pv")
(search)
;; Proof finished.
;; (cdp)
(save "RCplToRCauchy")

;; RCplToMon
(set-goal "allnc v(RCpl v -> Mon(rht v))")
(assume "v" "Pv")
(elim "Pv")
(search)
;; Proof finished.
;; (cdp)
(save "RCplToMon")

;; The following variants will be useful, because their heads will be
;; more often of the form of a given goal.

;; RCplPairToR
(set-goal "allnc xs,M(RCpl(xs pair M) -> allnc n Real(xs n))")
(assume "xs" "M" "Pv")
(use-with "RCplToR" (pt "xs pair M") "Pv")
;; Proof finished.
;; (cdp)
(save "RCplPairToR")

;; RCplPairToRCauchy
(set-goal "allnc xs,M(RCpl(xs pair M) -> RCauchy xs M)")
(assume "xs" "M" "Pv")
(use-with "RCplToRCauchy" (pt "xs pair M") "Pv")
;; Proof finished.
;; (cdp)
(save "RCplPairToRCauchy")

;; RCplPairToMon
(set-goal "allnc xs,M(RCpl(xs pair M) -> Mon M)")
(assume "xs" "M" "Pv")
(use-with "RCplToMon" (pt "xs pair M") "Pv")
;; Proof finished.
;; (cdp)
(save "RCplPairToMon")

;; RealBound - shorthand for cRBd(x seq)(x mod)
(add-program-constant "RealBound" (py "rea=>nat"))

(add-computation-rule "RealBound x" "cRBd(x seq)(x mod)")

;; RealBoundTotal
(set-totality-goal "RealBound")
(fold-alltotal)
(cases)
(assume "as" "M")
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; RCplBound
(add-program-constant "RCplBound" (py "(nat=>rea)yprod(pos=>nat)=>nat"))

(add-computation-rule "RCplBound(xs pair M)" "RealBound(abs(xs(M 1))+(1#2))")

;; RCplBoundTotal
(set-totality-goal "RCplBound")
(fold-alltotal)
(cases)
(assume "xs" "M")
(ng #t)
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; RCplLeBound
(set-goal "allnc v,n(RCpl v -> rht v 1<=n -> abs(lft v n)<<=2**RCplBound v)")
(cases)
(assume "xs" "M" "n" "RCplv" "M1<=n")
(inst-with-to "RCplPairToR" (pt "xs") (pt "M") "RCplv" "Rxs")
(use "RealLeTrans" (pt "abs(xs(M 1))+(1#2)"))
(use "RealLeCompat" (pt "abs(xs n+ ~(xs(M 1))+xs(M 1))")
     (pt "(1#2**1)+abs(xs(M 1))"))
(use "RealAbsCompat")
(use "RealEqTrans" (pt "xs n+(~(xs (M 1))+xs(M 1))"))
(use "RealEqSym")
(use "RealPlusAssoc")
(autoreal)
;; ?^13:xs n+(~(xs(M 1))+xs(M 1))===lft(xs pair M)n
(use "RealEqTrans" (pt "xs n+0"))
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealEqTrans" (pt "xs(M 1)+ ~(xs(M 1))"))
(use "RealPlusComm")
(autoreal)
(use "RealPlusMinusZero")
(autoreal)
(use "RealPlusZero")
(autoreal)
(use "RealPlusComm")
(autoreal)
(use "RealLeTrans" (pt "abs(xs n+ ~(xs (M 1)))+abs(xs (M 1))"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
(use "RCauchyElim" (pt "M"))
(use "RCplPairToRCauchy")
(use "RCplv")
(use "M1<=n")
(use "Truth")
(use "RealLeRefl")
(autoreal)
(use "RealLeBound")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RCplLeBound")

;; RCplTimes
(add-program-constant
 "RCplTimes"
 (py "(nat=>rea)yprod(pos=>nat)=>(nat=>rea)yprod(pos=>nat)=>
      (nat=>rea)yprod(pos=>nat)"))

(add-computation-rule
 "RCplTimes(xs pair M)(ys pair N)"
 "([n]xs n*ys n)pair([p]M(p+cNatPos(Succ(RCplBound(ys pair N))))max 
                        N(p+cNatPos(Succ(RCplBound(xs pair M)))))")

;; RCplTimesTotal
(set-totality-goal "RCplTimes")
(fold-alltotal)
(cases)
(assume "xs" "M")
(fold-alltotal)
(cases)
(assume "ys" "N")
(simp "RCplTimes0CompRule")
(use "YprodTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; RCplTimesRCpl
(set-goal "allnc v0,v1(RCpl v0 -> RCpl v1 -> RCpl(RCplTimes v0 v1))")
(cases)
(assume "xs0" "M0")
(cases)
(assume "xs1" "M1" "RCplxs0" "RCplxs1")
(inst-with-to "RCplPairToR" (pt "xs0") (pt "M0") "RCplxs0" "Rxs0")
(inst-with-to "RCplPairToR" (pt "xs1") (pt "M1") "RCplxs1" "Rxs1")
(use "RCplIntro")
(assume "n")
(ng #t)
(autoreal)
;; ?^11:RCauchy(lft(RCplTimes(xs0 pair M0)(xs1 pair M1)))
;;      (rht(RCplTimes(xs0 pair M0)(xs1 pair M1)))
(use "RCauchyIntro")
(assume "p" "n" "m")
;; ?^16:rht(RCplTimes(xs0 pair M0)(xs1 pair M1))p<=n -> 
;;      rht(RCplTimes(xs0 pair M0)(xs1 pair M1))p<=m -> 
;;      abs(lft(RCplTimes(xs0 pair M0)(xs1 pair M1))n+ 
;;          ~(lft(RCplTimes(xs0 pair M0)(xs1 pair M1))m))<<=
;;      (1#2**p)

(assert "all n0,n1(
      (M0 1<=n -> abs(xs0 n)<<=2**n0) -> 
      (M1 1<=m -> abs(xs1 m)<<=2**n1) -> 
      M0(p+cNatPos(Succ n1))max M1(p+cNatPos(Succ n0))<=n -> 
      M0(p+cNatPos(Succ n1))max M1(p+cNatPos(Succ n0))<=m -> 
      abs(xs0 n*xs1 n+ ~(xs0 m*xs1 m))<<=(1#2**p))"))

(assume "n0" "n1" "xs0Bound" "xs1Bound" "xs0xs1modp<=n" "xs0xs1modp<=m")
(use "RealLeTrans" (pt "abs(xs0 n*xs1 n+ ~(xs0 n*xs1 m))+
                        abs(xs0 n*xs1 m+ ~(xs0 m*xs1 m))"))
(use "RealLeAbsMinus")
(autoreal)
(use "RealLeCompat"
     (pt "abs(xs0 n)*abs(xs1 n+ ~(xs1 m))+abs(xs1 m)*abs(xs0 n+ ~(xs0 m))")
     (pt "RealTimes(2**n0)(1#2**(p+cNatPos (Succ n0)))+
          RealTimes(2**n1)(1#2**(p+cNatPos (Succ n1)))"))
(use "RealPlusCompat")
(use "RealEqTrans" (pt "abs(xs0 n*(xs1 n+ ~(xs1 m)))"))
(use "RealEqSym")
(use "RealAbsTimes")
(autoreal)
(use "RealAbsCompat")
(use "RealEqTrans" (pt "xs0 n*xs1 n+xs0 n* ~(xs1 m)"))
(use "RealTimesPlusDistr")
(autoreal)
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealTimesIdUMinus")
(autoreal)
(use "RealEqTrans" (pt "abs(xs1 m*(xs0 n+ ~(xs0 m)))"))
(use "RealEqSym")
(use "RealAbsTimes")
(autoreal)
(use "RealAbsCompat")
(use "RealEqTrans" (pt "(xs0 n+ ~(xs0 m))*xs1 m"))
(use "RealTimesComm")
(autoreal)
(use "RealEqTrans" (pt "xs0 n*xs1 m+ ~(xs0 m)*xs1 m"))
(use "RealTimesPlusDistrLeft")
(autoreal)
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealTimesUMinusId")
(autoreal)
;; ?^26:RealTimes(2**n0)(1#2**(p+cNatPos(Succ n0)))+
;;      RealTimes(2**n1)(1#2**(p+cNatPos(Succ n1)))===
;;      (1#2**p)

(assert "all n2 RealTimes(2**n2)(1#2**(p+cNatPos(Succ n2)))===
                (1#2**(PosS p))")
(assume "n2")
(use "RatEqvToRealEq")
(ng #t)
(simp "PosExpTwoNatPlus")
(simp "PosToNatPlus")
(simp "NatPosExFree")
(simp "PosToNatToPosId")
(simp "PosSSucc")
(simp "NatPlusComm")
(use "Truth")
(use "Truth")
;; Auxiliary assertion proved.
(assume "AuxAssertion")

;; ?^78:RealTimes(2**n0)(1#2**(p+cNatPos(Succ n0)))+
;;      RealTimes(2**n1)(1#2**(p+cNatPos(Succ n1)))===
;;      (1#2**p)

(use "RealEqTrans" (pt "RealPlus(1#2**PosS p)(1#2**PosS p)"))
(use "RealPlusCompat")
(use "AuxAssertion")
 (use "AuxAssertion")
(use "RealPlusHalfExpPosS")

;; ?^27:abs(xs0 n)*abs(xs1 n+ ~(xs1 m))+abs(xs1 m)*abs(xs0 n+ ~(xs0 m))<<=
;;      RealTimes(2**n0)(1#2**(p+cNatPos(Succ n0)))+
;;      RealTimes(2**n1)(1#2**(p+cNatPos(Succ n1)))
(use "RealLeMonPlusTwo")
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "xs0Bound")
(use "NatLeTrans" (pt "M0(p+cNatPos(Succ n1))"))
(use "MonElim")
(use "RCplPairToMon" (pt "xs0"))
(use "RCplxs0")
(use "Truth")
(use "NatLeTrans" (pt "M0 (p+cNatPos(Succ n1))max M1(p+cNatPos(Succ n0))"))
(use "NatMaxUB1")
(use "xs0xs1modp<=n")
(use "RCauchyElim" (pt "M1"))
(use "RCplPairToRCauchy")
(use "RCplxs1")
(use "NatLeTrans" (pt "M0(p+cNatPos(Succ n1))max M1(p+cNatPos(Succ n0))"))
(use "NatMaxUB2")
(use "xs0xs1modp<=n")
(use "NatLeTrans" (pt "M0(p+cNatPos(Succ n1))max M1(p+cNatPos(Succ n0))"))
(use "NatMaxUB2")
(use "xs0xs1modp<=m")
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "xs1Bound")
(use "NatLeTrans" (pt "M1(p+cNatPos(Succ n0))"))
(use "MonElim")
(use "RCplPairToMon" (pt "xs1"))
(use "RCplxs1")
(use "Truth")
(use "NatLeTrans" (pt "M0(p+cNatPos(Succ n1))max M1 (p+cNatPos(Succ n0))"))
(use "NatMaxUB2")
(use "xs0xs1modp<=m")
(use "RCauchyElim" (pt "M0"))
(use "RCplPairToRCauchy")
(use "RCplxs0")
(use "NatLeTrans" (pt "M0(p+cNatPos(Succ n1))max M1(p+cNatPos(Succ n0))"))
(use "NatMaxUB1")
(use "xs0xs1modp<=n")
(use "NatLeTrans" (pt "M0(p+cNatPos(Succ n1))max M1(p+cNatPos(Succ n0))"))
(use "NatMaxUB1")
(use "xs0xs1modp<=m")
;; Assertion proved.

(assume "Assertion" "xs0xs1modp<=n" "xs0xs1modp<=m")
(ng #t)
(use "Assertion" (pt "RCplBound(xs0 pair M0)") (pt "RCplBound(xs1 pair M1)"))
(use-with "RCplLeBound" (pt "xs0 pair M0") (pt "n") "RCplxs0")
(use-with "RCplLeBound" (pt "xs1 pair M1") (pt "m") "RCplxs1")
(use "xs0xs1modp<=n")
(use "xs0xs1modp<=m")
;; ?^12:Mon(rht(RCplTimes(xs0 pair M0)(xs1 pair M1)))
(use "MonIntro")
(assume "p" "q" "p<=q")

(assert "all r0, r1 M0(p+r0)max M1 (p+r1)<=M0(q+r0)max M1(q+r1)")
(assume "r0" "r1")
(use "NatMaxLUB")
(use "NatLeTrans" (pt "M0(q+r0)"))
(use "MonElim")
(use "RCplPairToMon" (pt "xs0"))
(use "RCplxs0")
(use "p<=q")
(use "NatMaxUB1")
(use "NatLeTrans" (pt "M1(q+r1)"))
(use "MonElim")
(use "RCplPairToMon" (pt "xs1"))
(use "RCplxs1")
(use "p<=q")
(use "NatMaxUB2")
;; Assertion proved.
(assume "Assertion")
(use "Assertion")
;; Proof finished.
;; (cdp)
(save "RCplTimesRCpl")

;; RealConvToRCpl
(set-goal "all xs,x,M(RealConv xs x M -> RCpl(xs pair([p]M(PosS p))))")
(assume "xs" "x" "M" "CxsxM")
(intro 0)
;; 3-5
(ng #t)
(use "RealConvElim1" (pt "x") (pt "M"))
(use "CxsxM")
;; 4
(ng #t)
;; ?^8:RCauchy xs([p]M(PosS p))
(intro 0)
(ng #t)
(assume "p" "n" "m" "nBd" "mBd")
(use "RealLeTrans" (pt "abs(xs n+ ~x)+abs(x+ ~(xs m))"))
(use "RealLeAbsMinus")
(autoreal)
(use "RealLeTrans" (pt "RealPlus(1#2**PosS p)(1#2**PosS p)"))
;; 17,18
(use "RealLeMonPlusTwo")
(use-with "RealConvElim4" (pt "xs") (pt "x") (pt "M") "CxsxM" (pt "PosS p")
	  (pt "n") "nBd")
(simpreal "RealAbsPlusUMinus")
(use-with "RealConvElim4" (pt "xs") (pt "x") (pt "M") "CxsxM" (pt "PosS p")
	  (pt "m") "mBd")
(autoreal)
;; ?^18:RealPlus(1#2**PosS p)(1#2**PosS p)<<=(1#2**p)
(simpreal "RealPlusHalfExpPosS")
(use "RatLeToRealLe")
(use "Truth")
;; 5
(ng #t)
(intro 0)
(ng #t)
(assume "p" "q" "p<=q")
(use "MonElim")
(use "RealConvElim3" (pt "xs") (pt "x"))
(use "CxsxM")
(use "p<=q")
;; Proof finished.
;; (cdp)
(save "RealConvToRCpl")

(add-program-constant
 "RealTimesMod" (py "(nat=>rea)=>(pos=>nat)=>(nat=>rea)=>(pos=>nat)=>pos=>nat"))

(add-computation-rule
"RealTimesMod xs M ys N p"
"M(PosS(p+cNatPos(Succ(cRBd(abs(ys(N 2))+(1#2))seq(abs(ys(N 2))+(1#2))mod))))max
 N(PosS(p+cNatPos(Succ(cRBd(abs(xs(M 2))+(1#2))seq(abs(xs(M 2))+(1#2))mod))))")

(set-totality-goal "RealTimesMod")
(fold-alltotal)
(assume "xs")
(fold-alltotal)
(assume "M")
(fold-alltotal)
(assume "ys")
(fold-alltotal)
(assume "N")
(fold-alltotal)
(assume "p")
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Idea: use cRTimesMod instead, and make RTimesMod into an
;; existence theorem

;; RTimesMod
(set-goal "all xs,M,ys,N,p(RCpl(xs pair M) -> RCpl(ys pair N) -> exl n n eqd
 M(PosS(p+cNatPos(Succ(cRBd(abs(ys(N 2))+(1#2))seq(abs(ys(N 2))+(1#2))mod))))max
 N(PosS(p+cNatPos(Succ(cRBd(abs(xs(M 2))+(1#2))seq(abs(xs(M 2))+(1#2))mod)))))")
(assume "xs" "M" "ys" "N" "p" "CxsxM" "CysyN")
(intro 0 (pt "RealTimesMod xs M ys N p"))
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "RTimesMod")

;; (pp (nt (pt "cRTimesMod xs M ys N p")))
(animate "RTimesMod")
;; (pp (nt (pt "cRTimesMod xs M ys N p")))
;; (deanimate "RTimesMod")

;; RealConvTimes
(set-goal "all xs,x,M,ys,y,N,L(RealConv xs x M -> RealConv ys y N ->
 L eqd [p]cRTimesMod xs M ys N p ->
 RealConv([n]xs n*(ys n))(RealLim([n]xs n*(ys n))L)L)")
(assume "xs" "x" "M" "ys" "y" "N" "L" "CxsxM" "CysyN" "LDef")
(use "RealConvLim")
;; 3-5
(ng #t)
(assume "n")
(autoreal)
;; 4
(ng #t)
(assume "p" "n" "m" "nBd" "mBd")
;; ?^9:abs(xs n*ys n+ ~(xs m*ys m))<<=(1#2**p)
(inst-with-to "RealConvToRCpl" (pt "xs") (pt "x") (pt "M") "CxsxM" "xsRCpl")
(inst-with-to "RealConvToRCpl" (pt "ys") (pt "y") (pt "N") "CysyN" "ysRCpl")

(assert "RCpl(([n]xs n*ys n)pair L)")
(simp "LDef")
(ng)
(inst-with-to "RCplTimesRCpl"
(pt "(xs pair([p]M(PosS p)))")
(pt "(ys pair([p]N(PosS p)))")
"xsRCpl" "ysRCpl" "Inst")
(ng "Inst")
(use "Inst")
;; Assertion proved.
(assume "Assertion")

;;   Assertion:RCpl(([n]xs n*ys n)pair L)
;; -----------------------------------------------------------------------------
;; ?^21:abs(xs n*ys n+ ~(xs m*ys m))<<=(1#2**p)

(assert "RCauchy([n]xs n*ys n)L")
(use "RCplPairToRCauchy")
(use "Assertion")
;; Assertion proved.
(assume "RCHyp1")

(inst-with-to "RCauchyElim" (pt "[n]xs n*(ys n)") (pt "L") "RCHyp1"
(pt "p") (pt "n") (pt "m") "nBd" "mBd" "RCInst")
(use "RCInst")
;; ?^5:all p,q(p<=q -> L p<=L q)

(assume "p" "q" "p<=q")
(simp "LDef")
(ng #t)
(use "NatLeMonMax")
(use "MonElim")
(use "RealConvElim3" (pt "xs") (pt "x"))
(use "CxsxM")
(ng #t)
(use "p<=q")
;; 35
(use "MonElim")
(use "RealConvElim3" (pt "ys") (pt "y"))
(use "CysyN")
(ng #t)
(use "p<=q")
;; Proof finished.
;; (cdp)
(save "RealConvTimes")

;; (pp "RealConvTimes")

;; all xs,x,M,ys,y,N,L(
;;  RealConv xs x M -> 
;;  RealConv ys y N -> 
;;  L eqd([p]cRTimesMod xs M ys N p) -> 
;;  RealConv([n]xs n*ys n)(RealLim([n]xs n*ys n)L)L)

;; (pp (nt (pt "cRTimesMod xs M ys N p")))

;; M(PosS(p+cNatPos(Succ(cRBd(abs(ys(N 2))+(1#2))seq(abs(ys(N 2))+(1#2))mod))))
;; max 
;; N(PosS(p+cNatPos(Succ(cRBd(abs(xs(M 2))+(1#2))seq(abs(xs(M 2))+(1#2))mod))))

;; 3.  Sum
;; =======

;; RealSum
(add-program-constant "RealSum" (py "nat=>nat=>(nat=>rea)=>rea"))

(add-computation-rules
"RealSum Zero Zero xs" "xs Zero"
"RealSum(Succ n)Zero xs" "0"
"RealSum n(Succ m)xs" "[if (n<=Succ m) (RealSum n m xs+xs(Succ m)) 0]")

(set-totality-goal "RealSum")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "m")
(fold-alltotal)
(assume "xs")
(ind (pt "m"))
(cases (pt "n"))
(assume "Useless")
(use "ReaTotalVar")
;; 11
(assume "m1" "Useless")
(use "ReaTotalVar")
;; 9
(assume "m1" "IH")
(ng #t)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "RealPlusTotal")
(use "IH")
(use "ReaTotalVar")
(use "ReaTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; RealSumReal
(set-goal "all n,m,xs(all n0 Real(xs n0) -> Real(RealSum n m xs))")
(assume "n" "m" "xs" "Rxs")
(ind (pt "m"))
(cases (pt "n"))
(assume "n=0")
(ng #t)
(autoreal)
;; 6
(assume "n0" "n=n0+1")
(ng #t)
(autoreal)
;; 4
(assume "m0" "IH")
(ng #t)
(cases (pt "n<=Succ m0"))
(assume "n<=m0+1")
(ng #t)
(use "RealPlusReal")
(use "IH")
(use "Rxs")
(assume "n</=m0+1")
(ng #t)
(realproof)
;; Proof finished.
;; (cdp)
(save "RealSumReal")

;; RealLeMonSum
(set-goal "all xs,ys,m,n(all l(m<=l -> l<=n -> xs l<<=ys l) ->
 RealSum m n xs<<=RealSum m n ys)")
(assume "xs" "ys" "n" "m")
(ind (pt "m"))
;; 3,4
(cases (pt "n"))
;; 5,6
(assume "n=0")
(ng #t)
(assume "xs0<=ys0")
(use "xs0<=ys0")
(use "Truth")
(use "Truth")
;; 6
(assume "n0" "n=n0+1" "Useless")
(ng #t)
(use "RealLeRefl")
(use "RealRat")
;; 4
(assume "m0" "IH" "xs<=ys")
(ng #t)
(cases (pt "n<=Succ m0"))
(assume "n<=m0+1")
(ng #t)
(use "RealLeMonPlusTwo")
(use "IH")
(assume "l" "n<=l" "l<=m0")
(use "xs<=ys")
(use "n<=l")
(use "NatLeTrans" (pt "m0"))
(use "l<=m0")
(use "Truth")
(use "xs<=ys")
(use "n<=m0+1")
(use "Truth")
(assume "Useless")
(ng #t)
(use "RealLeRefl")
(use "RealRat")
;; Proof finished.
;; (cdp)
(save "RealLeMonSum")

;; RealSumCompat
(set-goal "all xs,ys,m,n(all l(m<=l -> l<=n -> xs l===ys l) ->
 RealSum m n xs===RealSum m n ys)")
(assume "xs" "ys" "n" "m" "xs=ys")
(use "RealLeAntiSym")
(use "RealLeMonSum")
(assume "l" "n<=l" "l<=m")
(use "RealEqElim0")
(search)
;; 4
(use "RealLeMonSum")
(assume "l" "n<=l" "l<=m")
(use "RealEqElim1")
(search)
;; Proof finished.
;; (cdp)
(save "RealSumCompat")

;; RealSumZero
(set-goal "all xs,n,m(m<n -> RealSum n m xs===0)")
(assume "xs" "n" "m" "m<n")
(cases (pt "m"))
;; 3,4
(assume "m=0")
(cases (pt "n"))
;; 6,7
(assume "n=0")
(ng #t)
(assert "Zero<n")
(simp "<-" "m=0")
(use "m<n")
;; Assertion proved.
(simp "n=0")
(assume "Absurd")
(use "EfRealEq")
(use "Absurd")
;; 7
(assume "n0" "n=n0+1")
(ng #t)
(use "RealEqRefl")
(use "RealRat")
;; 4
(assume "m0" "m=m0+1")
(ng #t)
(simp "<-" "m=m0+1")
(assert "n<=m -> F")
(assume "n<=m")
(assert "m<m")
(use "NatLtLeTrans" (pt "n"))
(use "m<n")
(use "n<=m")
(assume "Absurd")
(use "Absurd")
(assume "n</=m")
(simp "n</=m")
(ng #t)
(use "RealEqRefl")
(use "RealRat")
;; Proof finished.
;; (cdp)
(save "RealSumZero")

;; RealSumOne
(set-goal "all xs,n(Real(xs n) -> RealSum n n xs===xs n)")
(assume "xs" "n" "Rxn")
(cases (pt "n"))
;; 3,4
(assume "n=0")
(ng #t)
(use "RealEqRefl")
(simp "<-" "n=0")
(use "Rxn")
;; 4
(assume "m" "n=m+1")
(ng #t)
(use "RealEqTrans" (pt "0+xs(Succ m)"))
(use "RealPlusCompat")
(use "RealSumZero")
(use "Truth")
(simp "<-" "n=m+1")
(use "RealEqRefl")
(use "Rxn")
(simp "<-" "n=m+1")
(simpreal "RealZeroPlus")
(use "RealEqRefl")
(use "Rxn")
(use "Rxn")
;; Proof finished.
;; (cdp)
(save "RealSumOne")

;; RealSumShiftPlus
(set-goal "all xs,m,n0,n(all l Real(xs l) ->
 RealSum n0(n0+n)([l]xs(m+l))===RealSum(m+n0)(m+n0+n)xs)")
(assume "xs" "m" "n0" "n" "Rxs")
(ind (pt "n"))
;; 3,4
(ng #t)
(simpreal "RealSumOne")
(simpreal "RealSumOne")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; 4
(assume "n1" "IH")
(ng #t)
(simp "<-" "NatPlus1CompRule")
(simp "<-" "NatPlus1CompRule")
(simp "NatLe2RewRule")
(simp "NatLe2RewRule")
(ng #t)
(use "RealPlusCompat")
(use "IH")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealSumShiftPlus")

;; RealSumShift
(set-goal "all xs,m,n,n0(all l Real(xs l) ->
 RealSum n0 n([l]xs(m+l))===RealSum(m+n0)(m+n)xs)")
(assume "xs" "m" "n" "n0" "Rxs")
(use "NatLeLtCases" (pt "n0") (pt "n"))
;; 3,4
(assume "n0<=n")
(assert "n=n0+(n--n0)")
(simp "NatPlusComm")
(use "NatEqSym")
(use "NatMinusPlusEq")
(use "n0<=n")
;; Assertion proved
(assume "SumHyp")
(simp "SumHyp")
(use "RealSumShiftPlus")
(use "Rxs")
;; 4
(assume "n<n0")
(simpreal (pf "RealSum n0 n([n^]xs(m+n^))===0"))
(simpreal (pf "RealSum(m+n0)(m+n)xs===0"))
(use "RealEqRefl")
(autoreal)
(use "RealSumZero")
(use "n<n0")
(use "RealSumZero")
(use "n<n0")
;; Proof finished.
;; (cdp)
(save "RealSumShift")

;; RealSumShiftPred
(set-goal "all xs,n(all l Real(xs l) ->
 RealSum(Succ Zero)(Succ n)([l]xs(Pred l))===RealSum Zero n xs)")
(assume "xs" "n" "Rxs")
(ind (pt "n"))
;; 3,4
(ng #t)
(simpreal "RealZeroPlus")
(use "RealEqRefl")
(autoreal)
;; 4
(assume "n1" "IH")
(ng #t)
(use "RealPlusCompat")
(simpreal "<-" "IH")
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealSumShiftPred")

;;  RealTimesSumDistrPlus
(set-goal "all n0,n,x,ys(Real x -> all l Real(ys l) ->
 x*RealSum n0(n0+n)ys===RealSum n0(n0+n)([l]x*ys l))")
(assume "n0" "n" "x" "ys" "Rx" "Rys")
(ind (pt "n"))
;; 3,4
(ng #t)
(simpreal "RealSumOne")
(simpreal "RealSumOne")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; 4
(assume "n1" "IH")
(ng #t)
(simp "<-" "NatPlus1CompRule")
(simp "NatLe2RewRule")
(ng #t)
(simpreal "RealTimesPlusDistr")
(use "RealPlusCompat")
(use "IH")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealTimesSumDistrPlus")

;; RealTimesSumDistr
(set-goal "all n0,n,x,ys(Real x -> all l Real(ys l) ->
 x*RealSum n0 n ys===RealSum n0 n([l]x*ys l))")
(assume "n0" "n" "x" "ys" "Rx" "Rys")
(use "NatLeLtCases" (pt "n0") (pt "n"))
;; 3,4
(assume "n0<=n")
(assert "n=n0+(n--n0)")
(simp "NatPlusComm")
(use "NatEqSym")
(use "NatMinusPlusEq")
(use "n0<=n")
;; Assertion proved
(assume "SumHyp")
(simp "SumHyp")
(use "RealTimesSumDistrPlus")
(use "Rx")
(use "Rys")
;; 4
(assume "n<n0")
(simpreal (pf "RealSum n0 n ys===0"))
(simpreal (pf "RealSum n0 n([n^]x*ys n^)===0"))
(simpreal "RealTimesZero")
(use "RealEqRefl")
(autoreal)
(use "RealSumZero")
(use "n<n0")
(use "RealSumZero")
(use "n<n0")
;; Proof finished.
;; (cdp)
(save "RealTimesSumDistr")

;; RealTimesSumDistrLeftPlus
(set-goal "all n0,n,xs,y(all l Real(xs l) -> Real y ->
 RealSum n0(n0+n)xs*y===RealSum n0(n0+n)([l]xs l*y))")
(assume "n0" "n" "xs" "y" "Rxs" "Ry")
(ind (pt "n"))
;; 3,4
(ng #t)
(simpreal "RealSumOne")
(simpreal "RealSumOne")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; 4
(assume "n1" "IH")
(ng #t)
(simp "<-" "NatPlus1CompRule")
(simp "NatLe2RewRule")
(ng #t)
(simpreal "RealTimesPlusDistrLeft")
(use "RealPlusCompat")
(use "IH")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealTimesSumDistrLeftPlus")

;; RealTimesSumDistrLeft
(set-goal "all n0,n,xs,y(all l Real(xs l) -> Real y ->
 RealSum n0 n xs*y===RealSum n0 n([l]xs l*y))")
(assume "n0" "n" "xs" "y" "Rxs" "Ry")
(use "NatLeLtCases" (pt "n0") (pt "n"))
;; 3,4
(assume "n0<=n")
(assert "n=n0+(n--n0)")
(simp "NatPlusComm")
(use "NatEqSym")
(use "NatMinusPlusEq")
(use "n0<=n")
;; Assertion proved
(assume "SumHyp")
(simp "SumHyp")
(use "RealTimesSumDistrLeftPlus")
(use "Rxs")
(use "Ry")
;; 4
(assume "n<n0")
(simpreal (pf "RealSum n0 n xs===0"))
(simpreal (pf "RealSum n0 n([n^]xs n^ *y)===0"))
(simpreal "RealZeroTimes")
(use "RealEqRefl")
(autoreal)
(use "RealSumZero")
(use "n<n0")
(use "RealSumZero")
(use "n<n0")
;; Proof finished.
;; (cdp)
(save "RealTimesSumDistrLeft")

;; RealSumPlus
(set-goal "all xs,n0,n1,n2(
     all l Real(xs l) -> 
     n0<=n1 -> 
     n1<=n2 -> RealSum n0 n1 xs+RealSum(Succ n1)n2 xs===RealSum n0 n2 xs)")
(assume "xs" "n0" "n1" "n" "Rxs" "n0<=n1")
(ind (pt "n"))
;; 3,4
(simp "NatLeToEq")
(assume "n1=0")
(ng #t)
(simp "n1=0")
(use "RealPlusZero")
(use "RealSumReal")
(use "Rxs")
;; 4
(assume "n2" "IH" "n1<=n2+1")
(ng #t)
(cases (pt "n1<=n2"))
(assume "n1<=n2")
(ng #t)
(assert "n0<=Succ n2")
(use "NatLeTrans" (pt "n1"))
(use "n0<=n1")
(use "n1<=n2+1")
;; Assertion proved.
(assume "n0<=n2+1")
(simp "n0<=n2+1")
(ng #t)
;; ?^23:RealSum n0 n1 xs+(RealSum(Succ n1)n2 xs+xs(Succ n2))===
;;      RealSum n0 n2 xs+xs(Succ n2)
(use "RealEqTrans" (pt "RealSum n0 n1 xs+RealSum (Succ n1) n2 xs+xs (Succ n2)"))
;; 24,25
(use "RealPlusAssoc")
(use "RealSumReal")
(use "Rxs")
(use "RealSumReal")
(use "Rxs")
(use "Rxs")
;; 25
(use "RealPlusCompat")
(use "IH")
(use "n1<=n2")
(use "RealEqRefl")
(use "Rxs")
;; 14
(assume "n1</=n2")
(ng #t)
;; ?^36:RealSum n0 n1 xs+0===[if (n0<=Succ n2) (RealSum n0 n2 xs+xs(Succ n2)) 0]
(assert "n1=Succ n2")
(use "NatLeAntiSym")
(use "n1<=n2+1")
(use "NatLtToSuccLe")
(use "NatNotLeToLt")
(use "n1</=n2")
;; Assertion proved.
(assume "n1=n2+1")
(simp "n1=n2+1")
(ng #t)
;; ?^45:[if (n0<=Succ n2) (RealSum n0 n2 xs+xs(Succ n2)) 0]+0===
;;      [if (n0<=Succ n2) (RealSum n0 n2 xs+xs(Succ n2)) 0]
(assert "n0<=Succ n2")
(use "NatLeTrans" (pt "n1"))
(use "n0<=n1")
(use "n1<=n2+1")
;; Assertion proved.
(assume "n0<=n2+1")
(simp "n0<=n2+1")
(ng #t)
(use "RealPlusZero")
(use "RealPlusReal")
(use "RealSumReal")
(use "Rxs")
(use "Rxs")
;; Proof finished.
;; (cdp)
(save "RealSumPlus")

;; We will need special cases where the left or right sum has one
;; element only.

;; RealSumPlusL
(set-goal "all xs,n,m(
     all l Real(xs l) -> 
     n<=m -> xs n+RealSum(Succ n)m xs===RealSum n m xs)")
(assume "xs" "n" "m" "Rxs" "n<=m")
(simpreal "<-" "RealSumOne")
(use "RealSumPlus")
(use "Rxs")
(use "Truth")
(use "n<=m")
(use "Rxs")
;; Proof finished.
;; (cdp)
(save "RealSumPlusL")

;; RealSumPlusR
(set-goal "all xs,n,m(
     all l Real(xs l) -> 
     n<=m -> RealSum n(Succ m)xs===RealSum n m xs+xs(Succ m))")
(assume "xs" "n" "m" "Rxs" "n<=m")
(ng #t)
(assert "n<=Succ m")
(use "NatLeTrans" (pt "m"))
(use "n<=m")
(use "Truth")
;; Assertion proved.
(assume "Assertion")
(simp "Assertion")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealSumPlusR")

;; RealSumPlusSeq
(set-goal "all xs,ys(all n Real(xs n) -> all n Real(ys n) -> all m,n(
RealSum n m xs+RealSum n m ys===RealSum n m([l]xs l+ys l)))")
(assume "xs" "ys" "Rxs" "Rys")
(ind)
(cases)
(ng #t)
(use "RealEqRefl")
(autoreal)
;; 6
(ng #t)
(assume "n")
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH" "n")
(ng #t)
(cases (pt "n<=Succ m"))
;; 14,15
(ng #t)
(assume "n<=Sm")
(simpreal "<-" "IH")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealPlusComm")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 15
(assume "Sm<n")
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealSumPlusSeq")

;; Further properties of RealSum for possible later use.

;; RealLeAbsSum
(set-goal "all xs,n,m(
  all n Real(xs n) -> abs(RealSum n m xs)<<=RealSum n m([n]abs(xs n)))")
(assume "xs" "n" "m" "Rxs")
(ind (pt "m"))
;; 3,4
(cases (pt "n"))
;; 5,6
(assume "n=0")
(ng #t)
(use "RealLeRefl")
(autoreal)
;; 6
(assume "n0" "n=n0+1")
(ng #t)
(use "RealLeRefl")
(use "RealRat")
;; 4
(assume "m0" "IH")
(ng #t)
(cases (pt "n<=Succ m0"))
(assume "n<=m0+1")
(ng #t)
(use "RealLeTrans" (pt "abs(RealSum n m0 xs)+abs(xs(Succ m0))"))
(use "RealLeAbsPlus")
(use "RealSumReal")
(use "Rxs")
(use "Rxs")
(use "RealLeMonPlus")
(autoreal)
(use "IH")
;; 16
(assume "n</=m0+1")
(ng #t)
(use "RealLeRefl")
(realproof)
;; Proof finished.
;; (cdp)
(save "RealLeAbsSum")

;; RealSumUMinus
(set-goal "all xs,n0,n1,n2(
     all n Real(xs n) -> 
     n0<=n1 -> 
     n1<=n2 -> RealSum n0 n2 xs+ ~(RealSum n0 n1 xs)===RealSum(Succ n1)n2 xs)")
(assume "xs" "n0" "n1" "n2" "Rxs" "n0<=n1" "n1<=n2")
(inst-with-to "RealSumReal" (pt "n0") (pt "n1") (pt "xs") "Rxs" "RealSumn0n1")
(inst-with-to "RealSumReal" (pt "n0") (pt "n2") (pt "xs") "Rxs" "RealSumn0n2")
(inst-with-to "RealSumReal"
              (pt "Succ n1") (pt "n2") (pt "xs") "Rxs" "RealSumn1+1n2")
(use "RealEqTrans"
(pt "(RealSum n0 n1 xs)+(RealSum(Succ n1)n2 xs)+ ~(RealSum n0 n1 xs)"))
;; 9,10
(use "RealPlusCompat")
(use "RealEqSym")
(use "RealSumPlus")
(use "Rxs")
(use "n0<=n1")
(use "n1<=n2")
(use "RealEqRefl")
(autoreal)
;; 10
(use "RealEqTrans"
(pt "(RealSum (Succ n1) n2 xs)+(RealSum n0 n1 xs)+ ~(RealSum n0 n1 xs)"))
;; 18,19
(use "RealPlusCompat")
(use "RealPlusComm")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 19
(use "RealEqTrans"
(pt "(RealSum(Succ n1)n2 xs)+((RealSum n0 n1 xs)+ ~(RealSum n0 n1 xs))"))
;; 25,26
(use "RealEqSym")
(use "RealPlusAssoc")
(autoreal)
;; 26
(use "RealEqTrans" (pt "(RealSum(Succ n1) n2 xs)+0"))
;; 31,32
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealPlusMinusZero")
(autoreal)
;; 32
(use "RealPlusZero")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealSumUMinus")

;; 4.  Geometric sequence, sum and series
;; ======================================

;; GeomSeqConv
(set-goal "all p,x,q,n(
     Real x -> 
     RealPos(1+ ~(abs x))p -> PosPred(2**PosS p)*q<=n -> abs(x**n)<<=(1#2**q))")
(assume "p" "x" "q" "n" "Realx" "absx<1" "Mq<=n")
;; (pp "RealLeCompat")
(use "RealLeCompat" (pt "(abs x)**n") (pt "RealConstr([n]1#2**q)([p]Zero)"))
;; 3-5
;; ?^3:abs x**n===abs(x**n)
(use "RealEqSym")
(use "RealAbsExp")
(autoreal)
;; ?^4:(1#2**q)===(1#2**q)
(use "RealEqRefl")
(use "RealRat")
;; ?^5:abs x**n<<=(1#2**q)
(use "RealLeTrans" (pt "RealExp(1+ ~(1#2**PosS p))n"))
;; 9,10
(use "RealLeMonExpBase")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLePlusCancelR" (pt "RealConstr([n]1#2**(PosS p))([p]Zero)"))
(autoreal)
;; ?^17:abs x+(1#2**PosS p)<<=RealPlus(1+ ~(1#2**PosS p))(1#2**PosS p)
(use "RealLeCompat"
     (pt "abs x+(1#2**(PosS p))") (pt "RealConstr([n]1)([p]Zero)"))
;; 18-20
(use "RealEqRefl")
(autoreal)
;; ?^19:1===RealPlus(1+ ~(1#2**PosS p))(1#2**PosS p)
(use "RealEqTrans"
     (pt "RealConstr([n]1+ ~(1#2**(PosS p))+(1#2**(PosS p)))([p]Zero)"))
;; ?^22:1===1+ ~(1#2**PosS p)+(1#2**PosS p)
(use "RatEqvToRealEq")
(use "RatEqvSym")
(use "RatEqvPlusMinus")
;; 23:1+ ~(1#2**PosS p)+(1#2**PosS p)===RealPlus(1+ ~(1#2**PosS p))(1#2**PosS p)
(use "RatPlusRealPlus")
;; ?^20:abs x+(1#2**PosS p)<<=1
(use "RealLePlusL")
(autoreal)
(simpreal "RealPlusComm")
(use "RealPosToLe")
(realproof)
(use "absx<1")
(autoreal)
;; ?^10:RealExp(1+ ~(1#2**PosS p))n<<=(1#2**q)
(use "RealLeCompat"
     (pt "RealConstr([m](1+ ~(1#2**(PosS p)))**n)([p]Zero)")
     (pt "RealConstr([n]1#2**q)([p]Zero)"))
;; 34-36
(use "RatExpRealExp")
;; ?^35:(1#2**q)===(1#2**q)
(use "RealEqRefl")
(use "RealRat")
;; ?^36:(1+ ~(1#2**PosS p))**n<<=(1#2**q)
(use "RatLeToRealLe")
;; (pp (nt (pt "1+ ~p")))
;; [if (1=p) 0 [if (1<p) (IntN(p--1)) 1]]
;; Here --1 arises
(ng #t)
;; ?^39:([if (2**PosS p=1) 0 (2**PosS p--1)]#2**PosS p)**n<=(1#2**q)
(simp "PosMinusOnePred")
;; ?^40:([if (2**PosS p=1) 0 (PosPred(2**PosS p))]#2**PosS p)**n<=(1#2**q)
(assert "2**(PosS p) = 1 -> F")
(assume "2**(p+1)=1")
(assert "2 <= 1")
(use "PosLeTrans" (pt "2**(PosS p)"))
(use "Truth")
(simp "2**(p+1)=1")
(use "Truth")
(assume "Absurd")
(use "Absurd")
(assume "2**(p+1)/=1")
(simp "2**(p+1)/=1")
(ng #t)
(use "RatLeUDivUDivInv")
(use "Truth")
;; ?^55:RatUDiv(1#2**q)<=RatUDiv((PosPred(2**PosS p)#2**PosS p)**n)
(simprat "RatUDivExp")
;; ?^56:RatUDiv(1#2**q)<=RatUDiv(PosPred(2**PosS p)#2**PosS p)**n
(ng #t)
;; ?^57:2**q<=(2**PosS p#PosPred(2**PosS p))**n
(assert "all p0 p0 * (1#p0) == 1")
    (assume "p0")
    (use "Truth")
  (assume "RatTimesInv")
(simp
 "RatLeCompat"
 (pt "(1+PosToNat(PosPred(2**PosS p))*(1#(PosPred(2**PosS p))))**(PosToNat q)")
 (pt "(1+(1#(PosPred(2**PosS p))))**n"))
;; 62-64
;; ?^62:(1+PosPred(2**PosS p)*(1#PosPred(2**PosS p)))**q<=
;;      (1+(1#PosPred(2**PosS p)))**n
(use
 "RatLeTrans"
 (pt "((1+(1#(PosPred(2**PosS p))))**(PosToNat(PosPred(2**PosS p))))**(PosToNat q)"))
;; 66,66
;; ?^65:(1+PosPred(2**PosS p)*(1#PosPred(2**PosS p)))**q<=
;;      (1+(1#PosPred(2**PosS p)))**PosPred(2**PosS p)**q
(use "RatLeMonExpBase")
;; 67,68
(simp "PosToNatToIntId")
(simprat "RatTimesInv")
(use "Truth")
;; ?^68:1+PosPred(2**PosS p)*(1#PosPred(2**PosS p))<=
;;      (1+(1#PosPred(2**PosS p)))**PosPred(2**PosS p)
(use "RatLeExpBernoulli")
;; ?^71:~1<=(1#PosPred(2**PosS p))
(use "Truth")
;; ?^66:(1+(1#PosPred(2**PosS p)))**PosPred(2**PosS p)**q<=
;;      (1+(1#PosPred(2**PosS p)))**n
(simprat "<-" "RatExpNatTimes")
(simp "<-" "PosToNatTimes")
(use "RatLeMonExp")
(use "Truth")
(use "Mq<=n")
;; ?^64:(2**PosS p#PosPred(2**PosS p))**n==(1+(1#PosPred(2**PosS p)))**n
(use "RatExpCompat")
;; ?^76:(2**PosS p#PosPred(2**PosS p))==1+(1#PosPred(2**PosS p))
(use "RatEqvTimesCancelR" (pt "(PosPred(2**PosS p)#1)"))
;; 77,78
;; ?^77:0<abs(PosPred(2**PosS p))
(use "RatNotZeroToZeroLtAbs")
;; ?^79:PosPred(2**PosS p)==0 -> F
(ng #t)
(assume "Absurd")
(use "Absurd")
;; ?^78:(2**PosS p#PosPred(2**PosS p))*PosPred(2**PosS p)==
;;      (1+(1#PosPred(2**PosS p)))*PosPred(2**PosS p)
(simprat "RatTimesPlusDistrLeft")
(simprat (pf "allnc p (1#p)*p==1"))
(simprat "<-" (pf "allnc p,q p*(RatUDiv q)==(p#q)")) ;RatTimesUDiv
;; 85,86
;; ?^85:2**PosS p*RatUDiv(PosPred(2**PosS p))*PosPred(2**PosS p)==
;;      RatTimes 1(PosPred(2**PosS p))+1
(simp "<-" "RatTimesAssoc")
(simprat (pf "RatUDiv(PosPred(2**PosS p))*(PosPred(2**PosS p))==
              (PosPred(2**PosS p))*RatUDiv(PosPred(2**PosS p))"))
(simprat "RatTimesUDivR")
(ng #t)
;; ?^92:2**PosS p=PosS(PosPred(2**PosS p))
(simp "PosSPosPredId")
(use "Truth")
(use "Truth")
;; ?^91:0<abs(PosPred(2**PosS p))
(use "RatNotZeroToZeroLtAbs")
;; ?^95:PosPred(2**PosS p)==0 -> F
(ng #t)
(assume "Absurd")
(use "Absurd")
;; ?^89:RatUDiv(PosPred(2**PosS p))*PosPred(2**PosS p)==
;;      PosPred(2**PosS p)*RatUDiv(PosPred(2**PosS p))
(use "Truth")
;; ?^86:allnc p,q p*RatUDiv q==(p#q)
(strip)
(use "Truth")
;; ?^84:allnc p (1#p)*p==1
(strip)
(use "Truth")
;; ?^63:2**q==(1+PosPred(2**PosS p)*(1#PosPred(2**PosS p)))**q
(simp "PosToNatToIntId")
;; ?^100:2**q==(1+PosPred(2**PosS p)*(1#PosPred(2**PosS p)))**q
(simp "PosToNatToIntId")
;; ?^101:2**q==(1+PosPred(2**PosS p)*(1#PosPred(2**PosS p)))**q
(simp "RatTimes0CompRule")
(simp (pf "2**q=RatExp 2 q"))
(use "RatExpCompat")
(simp "PosTimes0RewRule")
(simp "IntTimes1RewRule")
(simp (pf "2=RatPlus 1 1"))
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished
;;(cdp)
(save "GeomSeqConv")

;; (pp "GeomSeqConv")

;; We show that convergence also holds in the sense that we can prove
;; RealConv([n]x**n)0([q]PosPred(2**PosS p)*q)

;; GeomSeqRealConv
(set-goal "all x,p(
 Real x -> 
 RealPos(1+ ~abs x)p ->
 RealConv([n]x**n)0([q]PosPred(2**PosS p)*q))")
(assume "x" "p" "Rx" "absx<1")
(intro 0)
;; 3-6
(ng #t)
(assume "n")
(autoreal)
;; ?^5:Mon([p0]PosToNat(PosPred(2**PosS p)*p0))
(intro 0)
(ng #t)
(assume "p1" "q" "p1<=q")
(simp "PosToNatLe")
(use "p1<=q")
;; 6
(ng #t)
(assume "q" "n" "nBd")
(simpreal "RealPlusZero")
(use "GeomSeqConv" (pt "p"))
(autoreal)
(use "absx<1")
(use "nBd")
(autoreal)
;; Proof finished.
;; (cdp)
(save "GeomSeqRealConv")

;; GeomSumEq
(set-goal "all x,p(
     Real x -> 
     RealPos abs(1+ ~x)p -> 
     all n RealSum Zero n([m]x**m)===(1+ ~(x**Succ n))*RealUDiv(1+ ~x)p)")
(assume "x" "p" "Rx" "x/=1" "n0")
(ind (pt "n0"))
;; 3,4
(ng #t)
(use "RealEqSym")
;; ?^6:(1+ ~(1*x))*RealUDiv(1+ ~x)p===1
(assert (pf "1+ ~(1*x)===1+ ~x"))
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
;; Assertion proved.
(assume "EqHyp")
(simpreal "EqHyp")
(use "RealTimesUDivR2")
(realproof)
(use "x/=1")
;; 4
(assume "n" "IH")
(assert "Real(RealUDiv(1+ ~x)p)")
(use "RealUDivReal")
(realproof)
(use "x/=1")
;; Assertion proved.
(assume "Real1/(1-x)")
(ng #t)
(use "RealEqTrans" (pt "(1+ ~(x**(Succ n)))*(RealUDiv(1+ ~x) p)+x**(Succ n)"))
;; 23,24
(use "RealPlusCompat")
(use "IH")
(use "RealEqRefl")
(realproof)
;; 24
(use "RealEqTrans"
     (pt "(1+ ~(x**(Succ n)))*(RealUDiv(1+ ~x) p)+
          (x**(Succ n)+ ~(x**(Succ(Succ n))))*(RealUDiv(1+ ~x) p)"))
;; 28,29
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealEqTrans" (pt "x**(Succ n)*1"))
(use "RealEqSym")
(use "RealTimesOne")
(realproof)
(use "RealEqTrans" (pt "x**Succ n*((1+ ~x)*(RealUDiv(1+ ~x) p))"))
;; 37,38
(simpreal "RealTimesUDivR2")
(simpreal "RealTimesOne")
(use "RealEqRefl")
(autoreal)
(use "x/=1")
(autoreal)
;; ?^38:x**Succ n*((1+ ~x)*RealUDiv(1+ ~x)p)===
;;      (x**Succ n+ ~(x**Succ(Succ n)))*RealUDiv(1+ ~x)p
(simpreal "RealTimesAssoc")
(use "RealTimesCompat")
;; 49,50
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesOne")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(ng #t)
(use "RealTimesIdUMinus")
(autoreal)
;; 50
(use "RealEqRefl")
(autoreal)
;; 29
(simpreal "<-" "RealTimesPlusDistrLeft")
(use "RealTimesCompat")
;; 68,69
(ng #t)
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "(~(x**n*x)+x**n*x)===(x**n*x+ ~(x**n*x))"))
(simpreal "RealPlusMinusZero")
(use "RealPlusZero")
(autoreal)
(use "RealPlusComm")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 69
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "GeomSumEq")

;; We prove that the geometric series converges to RealUDiv(1+ ~x)r.
;; Recall

;; (pp "GeomSeqRealConv")

;; all x,p(
;;  Real x -> 
;;  RealPos(1+ ~abs x)p -> 
;;  RealConv([n]x**n)0([p0]PosToNat(PosPred(2**PosS p)*p0)))

;; RealLeUDivTwoExp
(set-goal "all x,p(Real x -> RealPos x p -> (1#2**p)<<=x ->
 RealUDiv x p<<=2**p)")
(assume "x" "p" "Rx" "0<x" "LeHyp")
(use "RealLeUDiv" (pt "p"))
;; 3-7
(autoreal)
;; ?^4:RealPos(2**p)p
(use "Truth")
;; 5
(use "Rx")
;; 6
(use "0<x")
;; ?^7:RealUDiv(2**p)p<<=x
(simpreal (pf "RealUDiv(2**p)p===(1#2**p)"))
(use "LeHyp")
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealLeUDivTwoExp")

;; GeomSerConvAux
(set-goal "all x,q,M,y(Real y ->
     0<<=x -> 
     RealPos(1+ ~x)q -> 
     RealPos(1+ ~x)(PosS q) -> 
     RealConv([n]x**n)0 M -> 
     y eqd RealUDiv(1+ ~x)(PosS q) -> 
     RealConv([n]([m]1+ ~(x**m))n*y)
     (RealUDiv(1+ ~x)(PosS q))
     ([p]M(p+PosS q)))")
(assume "x" "q" "M" "y" "Ry" "0<=x" "x<1q" "x<1Sq" "GSeqConv" "yDef")
(simpreal (pf "(RealUDiv(1+ ~x)(PosS q))===1*(RealUDiv(1+ ~x)(PosS q))"))
(simp "yDef")
(use "RealConvTimesConstR")
;; 6-8
;; ?^6:RealConv([m]1+ ~(x**m))1 M
(use "RealConvCompat"
     (pt "[m]1+ ([l]~(x**l))m")  (pt "1+RealUMinus 0") (pt "M"))
;; 9-11
(ng #t)
(assume "n")
(use "RealEqRefl")
(autoreal)
(simpreal (pf "RealUMinus 0===0"))
(use "RealPlusZero")
(autoreal)
(use "RatEqvToRealEq")
(use "Truth")
;; 11
(assume "p")
(use "Truth")
(use "RealConvPlusConstL")
 ;; 21,22
(use "RealConvUMinus")
(use "GSeqConv")
(use "RealRat")
;; ?^7:Real(RealUDiv(1+ ~x)(PosS q))
(use "RealUDivReal")
(autoreal)
(use "RealPosToPosAbs")
(use "RealPosPosS")
(autoreal)
(use "x<1q")
;; ?^8:abs(RealUDiv(1+ ~x)(PosS q))<<=2**PosS q
(simpreal "RealAbsUDiv")
(use "RealLeUDivTwoExp")
(autoreal)
(use "RealPosToPosAbs")
(use "RealPosPosS")
(autoreal)
(use "x<1q")
;; ?^34:(1#2**PosS q)<<=abs(1+ ~x)
(use "RealPosToLe")
(autoreal)
(use "RealPosToPosAbs")
(use "x<1q")
(use "RealPosPosS")
(autoreal)
(use "x<1q")
(autoreal)
;; ?^4:RealUDiv(1+ ~x)(PosS q)===1*RealUDiv(1+ ~x)(PosS q)
(use "RealEqSym")
(use "RealOneTimes")
(autoreal)
;; Proof finished.
;; (cdp)
(save "GeomSerConvAux")

;; (pp "GeomSerConvAux")

;; GeomSerConv
(set-goal "all x,q,M(
     0<<=x -> 
     RealPos(1+ ~x)q -> 
     RealConv([n]x**n)0 M -> 
     RealConv([n](1+ ~(x**n))*RealUDiv(1+ ~x)(PosS q))
     (RealUDiv(1+ ~x)(PosS q))
     ([p]M(p+PosS q)))")
(assume "x" "q" "M" "0<=x" "x<1" "GSeqConv")
(simp (pf "([n](1+ ~(x**n))*RealUDiv(1+ ~x)(PosS q))eqd
           ([n](([m]1+ ~(x**m))n)*RealUDiv(1+ ~x)(PosS q))"))
(use "GeomSerConvAux")
;; 5-10
(use "RealUDivReal")
(realproof)
(use "RealPosPosS")
(realproof)
(use "RealPosToPosAbs")
(use "x<1")
;; 6
(use "0<=x")
;; 7
(use "x<1")
;; 8
(use "RealPosPosS")
(realproof)
(use "x<1")
;; 9
(use "GSeqConv")
;; 10
(use "InitEqD")
;; 4
(ng #t)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "GeomSerConv")

;; (pp "GeomSeqRealConv")

;; all x,p(
;;  Real x -> 
;;  RealPos(1+ ~abs x)p -> 
;;  RealConv([n]x**n)0([p0]PosToNat(PosPred(2**PosS p)*p0)))

;; (pp "RealConvTimesConstR")

;; all xs,x,M,y,q(
;;  RealConv xs x M -> 
;;  Real y -> abs y<<=2**q -> RealConv([n]xs n*y)(x*y)([p]M(p+q)))

;; (pp "GeomSumEq")
;; (search-about "GeomSeq")
;; (display-pconst "RealPos")

;; 5.  Binomials coefficients and theorem
;; ======================================

;; As an application of RealSumShiftPredShift we prove the Binomial Theorem.
;; This will be needed for the functional equation of the exponential
;; function.

(add-program-constant "Choose" (py "nat=>nat=>nat"))

(add-computation-rules
 "Choose Zero Zero" "Succ Zero"
 "Choose Zero(Succ m)" "Zero"
 "Choose(Succ n)Zero" "Succ Zero"
 "Choose(Succ n)(Succ m)" "Choose n m+Choose n(Succ m)")

(set-totality-goal "Choose")
(fold-alltotal)
(ind)
;; 3,4
(fold-alltotal)
(cases)
(use "NatTotalVar")
(assume "n")
(use "NatTotalVar")
;; 4
(assume "n" "IH")
(fold-alltotal)
(cases)
(use "NatTotalVar")
(assume "m")
(use "NatPlusTotal")
(use "IH")
(use "NatTotalVar")
(use "IH")
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

(set-goal "all n Choose n Zero=Succ Zero")
(cases)
(use "Truth")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Choose n Zero" "Succ Zero")

(set-goal "all n Choose n(Succ Zero)=n")
(cases)
(use "Truth")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Choose n(Succ Zero)" "n")

;; NatLtToChooseZero
(set-goal "all n,m(n<m -> Choose n m=Zero)")
(ind)
;; 2,3
(cases)
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "m" "Useless")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(assume "Absurd")
(use "Absurd")
(ng #t)
(assume "m" "n<m")
(simp "IH")
(ng #t)
(use "IH")
(use "NatLtTrans" (pt "m"))
(use "n<m")
(use "Truth")
(use "n<m")
;; Proof finished.
;; (cdp)
(save "NatLtToChooseZero")

(set-goal "all n Choose n(Succ n)=Zero")
(assume "n")
(use "NatLtToChooseZero")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Choose n(Succ n)" "Zero")

(set-goal "all n Choose n n=Succ Zero")
(ind)
;; 2,3
(use "Truth")
;; 3
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Choose n n" "Succ Zero")

(set-goal "all n Choose(Succ n)n=Succ n")
(ind)
;; 2,3
(use "Truth")
;; 3
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Choose(Succ n)n" "Succ n")

;; (display-pconst "Choose")

;;   comprules
;; 0	Choose Zero Zero	Succ Zero
;; 1	Choose Zero(Succ m)	Zero
;; 2	Choose(Succ n)Zero	Succ Zero
;; 3	Choose(Succ n)(Succ m)	Choose n m+Choose n(Succ m)
;;   rewrules
;; 0	Choose n Zero	Succ Zero
;; 1	Choose n(Succ Zero)	n
;; 2	Choose n(Succ n)	Zero
;; 3	Choose n n	Succ Zero
;; 4	Choose(Succ n)n	Succ n

;; (search-about "Choose")

;; NatLtToChooseZero
;; all n,m(n<m -> Choose n m=Zero)

;; NatPosToChooseSuccPred
(set-goal "all n,m(Zero<m -> m<=n ->
 Choose(Succ n)m=Choose n(Pred m)+Choose n m)")
(ind)
;; 2,3
(cases)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 5
(assume "n" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "n" "IH")
(cases)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "m" "Useless" "m<=n")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatPosToChooseSuccPred")

;; Binom
(set-goal "all x,y(Real x -> Real y ->
 all n (x+y)**n===RealSum Zero n([l]x**(n--l)*y**l*Choose n l))")
(assume "x" "y" "Rx" "Ry")
(ind)
;; 3,4
(ng #t)
(use "RealEqRefl")
(use "RealRat")
;; 4
(assume "n" "IH")
(cases (pt "n"))
(assume "n=0")
(ng #t)
(simpreal "RealOneTimes")
(simpreal "RealOneTimes")
(simpreal "RealOneTimes")
(simpreal "RealOneTimes")
(simpreal "RealTimesOne")
(simpreal "RealTimesOne")
(simpreal "RealTimesOne")
(use "RealEqRefl")
(autoreal)
(assume "m" "n=Sm")
(simp "<-" "n=Sm")
(simp "RealExp1CompRule")
(simpreal "RealTimesComm")
(simpreal "IH")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "RealTimesSumDistr")
(simpreal "RealTimesSumDistr")
(ng #t)
;; ?^44:RealSum Zero n([n0]x*(x**(n--n0)*y**n0*Choose n n0))+
;;      RealSum Zero n([n0]y*(x**(n--n0)*y**n0*Choose n n0))===
;;      RealSum Zero n([n0]x**(Succ n--n0)*y**n0*Choose(Succ n)n0)+1*(y**n*y)*1
(simprsum (pf "all n0 x*(x**(n--n0)*y**n0*Choose n n0)===
                      x**(Succ n--n0)*y**n0*Choose n n0"))
;; 45,46
;; ?^45:RealSum Zero n([n0]x**(Succ n--n0)*y**n0*Choose n n0)+
;;      RealSum Zero n([n0]y*(x**(n--n0)*y**n0*Choose n n0))===
;;      RealSum Zero n([n0]x**(Succ n--n0)*y**n0*Choose(Succ n)n0)+y**n*y
(simprsum (pf "all n0 y*(x**(n--n0)*y**n0*Choose n n0)===
                      x**(n--n0)*y**Succ n0*Choose n n0"))
;; 47,48
;; ?^47:RealSum Zero n([n0]x**(Succ n--n0)*y**n0*Choose n n0)+
;;      RealSum Zero n([n0]x**(n--n0)*y**Succ n0*Choose n n0)===
;;      RealSum Zero n([n0]x**(Succ n--n0)*y**n0*Choose(Succ n)n0)+y**n*y
(simpreal (pf "RealSum Zero n([n0]x**(n--n0)*y**Succ n0*Choose n n0)===
               RealSum(Succ Zero)(Succ n)
               ([n0]x**(n--Pred n0)*y**Succ(Pred n0)*Choose n(Pred n0))"))
;; 49,50
;; ?^49:RealSum Zero n([n0]x**(Succ n--n0)*y**n0*Choose n n0)+
;;      RealSum(Succ Zero)(Succ n)
;;      ([n0]x**(n--Pred n0)*y**Succ(Pred n0)*Choose n(Pred n0))===
;;      RealSum Zero n([n0]x**(Succ n--n0)*y**n0*Choose(Succ n)n0)+y**n*y
(simpreal "RealSumPlusR")
;; 51-53
(ng #t)
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")
;; 59,60
;; ?^59:RealSum Zero n([n0]x**(Succ n--n0)*y**n0*Choose n n0)+
;;      RealSum(Succ Zero)n
;;      ([n0]x**(n--Pred n0)*(y**Pred n0*y)*Choose n(Pred n0))===
;;      RealSum Zero n([n0]x**(Succ n--n0)*y**n0*Choose(Succ n)n0)

(defnc "x1" "RealSum(Succ Zero)n
     ([n0]x**(n--Pred n0)*(y**Pred n0*y)*Choose n(Pred n0))")
(simp "<-" "x1Def")
;; ?^68:RealSum Zero n([n0]x**(Succ n--n0)*y**n0*Choose n n0)+x1===
;;      RealSum Zero n([n0]x**(Succ n--n0)*y**n0*Choose(Succ n)n0)
(assert "Real x1")
(simp "x1Def")
(realproof)
(assume "Rx1")
(simpreal "<-" "RealSumPlusL")
(ng #t)
(defnc "x2" "RealSum(Succ Zero)n([n0]x**(Succ n--n0)*y**n0*Choose n n0)")
(simp "<-" "x2Def")
(assert "Real x2")
(simp "x2Def")
(realproof)
(assume "Rx2")
(simpreal "<-" "RealSumPlusL")
(ng #t)
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simp "x1Def")
(simp "x2Def")
;; ?^101:RealSum(Succ Zero)n([n0]x**(Succ n--n0)*y**n0*Choose n n0)+
;;       RealSum(Succ Zero)n
;;       ([n0]x**(n--Pred n0)*(y**Pred n0*y)*Choose n(Pred n0))===
;;       RealSum(Succ Zero)n([n0]x**(Succ n--n0)*y**n0*Choose(Succ n)n0)
(simprsum (pf "all n0(Succ Zero<=n0 -> n0<=Succ n -> n--Pred n0=Succ n--n0)"))
;; 102,103
(simprsum (pf "all n0(Succ Zero<=n0 -> n0<=Succ n -> y**Pred n0*y===y**n0)"))
;; 104,105
(simprsum (pf "all n0(Succ Zero<=n0 -> n0<=Succ n ->
                      Choose(Succ n)n0=Choose n(Pred n0)+Choose n n0)"))
;; 106,107
;; ?^106:RealSum(Succ Zero)n([n0]x**(Succ n--n0)*y**n0*Choose n n0)+
;;       RealSum(Succ Zero)n([n0]x**(Succ n--n0)*y**n0*Choose n(Pred n0))===
;;       RealSum(Succ Zero)n
;;       ([n0]x**(Succ n--n0)*y**n0*(Choose n(Pred n0)+Choose n n0))

(simpreal "RealSumPlusSeq")
;; 108-110
(ng #t)
;; ?^111:RealSum(Succ Zero)n
;;       ([n0]
;;         x**(Succ n--n0)*y**n0*Choose n n0+
;;         x**(Succ n--n0)*y**n0*Choose n(Pred n0))===
;;       RealSum(Succ Zero)n
;;       ([n0]x**(Succ n--n0)*y**n0*(Choose n(Pred n0)+Choose n n0))

(use "RealSumCompat")
(assume "l" "1<=l" "l<=n")
(ng #t)
(simp "NatPlusComm")
(simpreal "<-" "NatToRealPlus")
(use "RealEqSym")
(use "RealTimesPlusDistr")
(autoreal)
;; 110
(assume "n0")
(autoreal)
;; 109
(assume "n0")
(autoreal)
;; 107
(use "RealSumCompat")
(assume "l" "1<=l" "l<=n")
(ng #t)
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
(simp "NatPosToChooseSuccPred")
(use "RealEqRefl")
(autoreal)
(use "l<=n")
(use "NatLtLeTrans" (pt "Succ Zero"))
(use "Truth")
(use "1<=l")
;; ?^105:RealSum(Succ Zero)n
;;       ([n0]x**(Succ n--n0)*(y**Pred n0*y)*Choose n(Pred n0))===
;;       RealSum(Succ Zero)n([n0]x**(Succ n--n0)*y**n0*Choose n(Pred n0))
(use "RealSumCompat")
(assume "l" "1<=l" "l<=n")
(ng #t)
;; ?^137:x**(Succ n--l)*(y**Pred l*y)*Choose n(Pred l)===
;;       x**(Succ n--l)*y**l*Choose n(Pred l)
(use "RealTimesCompat")
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
;; ?^141:y**Pred l*y===y**l
(cases (pt "l"))
;; 143,144
(assume "l=0")
(simphyp-with-to "1<=l" "l=0" "Absurd")
(use "EfRealEq")
(use "Absurd")
;; 144
(assume "n1" "Useless")
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; ?^103:RealSum(Succ Zero)n
;;       ([n0]x**(n--Pred n0)*(y**Pred n0*y)*Choose n(Pred n0))===
;;       RealSum(Succ Zero)n
;;       ([n0]x**(Succ n--n0)*(y**Pred n0*y)*Choose n(Pred n0))
(use "RealSumCompat")
(assume "l" "1<=l" "l<=n")
(ng #t)
(use "RealTimesCompat")
(use "RealTimesCompat")
(cases (pt "l"))
;; 160,161
(assume "l=0")
(simphyp-with-to "1<=l" "l=0" "Absurd")
(use "EfRealEq")
(use "Absurd")
;; 161
(assume "n1" "Useless")
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 91
(use "Truth")
(assume "l")
(autoreal)
;; 75
(use "Truth")
(assume "l")
(autoreal)
;; 60
(use "RealEqRefl")
(autoreal)
;; 53
(simp "n=Sm")
(use "Truth")
(assume "l")
(autoreal)
;; ?^50:RealSum Zero n([n0]x**(n--n0)*y**Succ n0*Choose n n0)===
;;      RealSum(Succ Zero)(Succ n)
;;      ([n0]x**(n--Pred n0)*y**Succ(Pred n0)*Choose n(Pred n0))
(use "RealEqSym")
(use-with "RealSumShiftPred"
(pt "([n0]x**(n--n0)*y**Succ n0*Choose n n0)") (pt "n") "?")
(assume "l")
(autoreal)
;; ?^48:RealSum Zero n([n0]y*(x**(n--n0)*y**n0*Choose n n0))===
;;      RealSum Zero n([n0]x**(n--n0)*y**Succ n0*Choose n n0)
(use "RealSumCompat")
(assume "l" "1<=l" "l<=n")
(ng #t)
(simpreal "RealTimesAssoc")
(use "RealTimesCompat")
(simpreal "RealTimesComm")
(simpreal "RealTimesAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; ?^46:RealSum Zero n([n0]x*(x**(n--n0)*y**n0*Choose n n0))===
;;      RealSum Zero n([n0]x**(Succ n--n0)*y**n0*Choose n n0)
(use "RealSumCompat")
(assume "l" "1<=l" "l<=n")
(ng #t)
(simpreal "RealTimesAssoc")
(use "RealTimesCompat")
(simpreal "RealTimesAssoc")
(use "RealTimesCompat")
(simpreal "RealTimesComm")
(simp "<-" "RealExp1CompRule")
(simp "SuccNatMinus")
(use "RealEqRefl")
(autoreal)
(use "l<=n")
(autoreal)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 43
(assume "l")
(autoreal)
;; 49
(assume "l")
(autoreal)
;; Proof finished.
;; (cdp)
(save "Binom")

