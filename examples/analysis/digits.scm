;; 2021-03-04.  examples/analysis/digits.scm

;; Dependency of files

;; sdmult       sddiv <--   div  -->  graydiv     graymult
;;    ^           ^                      ^           ^
;;      \         |                      |         /
;;         \      |                      |      /
;;            \   |                      |   / 
;;  sdav <--   sdavaux <--  JK  -->  grayavaux --> grayav
;;                ^                      ^
;;                  \                    |
;;                     \                 |
;;                        \              |
;;                         sdcode --> graycode
;;                           ^                            
;;                           |                            
;;                           |                            
;;                           |                            
;;                         digits

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "list.scm")
;; (libload "pos.scm")
;; (libload "int.scm")
;; (libload "rat.scm")
;; (libload "rea.scm")
;; ;; (set! COMMENT-FLAG #t)

(display "loading digits.scm ...") (newline)

(remove-var-name "d") ;will be used as variable name for integers
(add-var-name "d" "e" (py "int"))

;; Corresponding to
;; (display-alg "int")
;; int
;; 	IntPos:	pos=>int
;; 	IntZero:	int
;; 	IntNeg:	pos=>int
;; we add the algebra sd in the order positive (R), zero (M), negative (L)

(add-algs "sd" '("SdR" "sd") '("SdM" "sd") '("SdL" "sd"))
(add-var-name "s" (py "sd"))
(add-totality "sd")

;; This adds the predicate TotalSd with content of type sd and clauses
;; TotalSdSdR:	TotalSd SdR
;; TotalSdSdM:	TotalSd SdM
;; TotalSdSdL:	TotalSd SdL

(add-totalnc "sd")
(add-co "TotalSd")
(add-co "TotalSdNc")

(add-mr-ids "TotalSd")
(add-co "TotalSdMR")

(add-eqp "sd")
(add-eqpnc "sd")
(add-co "EqPSd")
(add-co "EqPSdNc")

(add-mr-ids "EqPSd")
(add-co "EqPSdMR")

;; SdTotalVar
(set-goal "all s TotalSd s")
(use "AllTotalIntro")
(assume "s^" "Ts")
(use "Ts")
;; Proof finished
(save "SdTotalVar")

;; SdEqToEqD
(set-goal "all s1,s2(s1=s2 -> s1 eqd s2)")
(cases)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
;; Proof finished.
(save "SdEqToEqD")

(add-ids
 (list (list "Sd" (make-arity (py "int")) "sd"))
 '("Sd(IntP One)" "InitSdSdR")
 '("Sd IntZero" "InitSdSdM")
 '("Sd(IntN One)" "InitSdSdL"))

(add-mr-ids "Sd")

;; EfSd
(set-goal "allnc d^(F -> Sd d^)")
(assume "d^" "Absurd")
(simp (pf "d^ eqd IntP 1"))
(use "InitSdSdR")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfSd")

;; SdBound
(set-goal "all d(Sd d -> abs d<=1)")
(assume "d" "Sdd")
(elim "Sdd")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdBound")

;; SdUMinus
(set-goal "allnc d(Sd d -> Sd(~d))")
(assume "d" "Sdd")
(elim "Sdd")
(use "InitSdSdL")
(use "InitSdSdM")
(use "InitSdSdR")
;; Proof finished.
(save "SdUMinus")

(add-sound "SdUMinus")
;; ok, SdUMinusSound has been added as a new theorem:

;; allnc d,s^(SdMR d s^ -> SdMR(~d)(cSdUMinus s^))

;; with computation rule

;; cSdUMinus eqd([s][if s SdL SdM SdR])

;; (cdp "SdUMinusSound")
(deanimate "SdUMinus")

;; Corresponding to (display-alg "int") int IntPos: pos=>int IntZero:
;; int IntNeg: pos=>int we add the algebra sdtwo in the order positive
;; (RT, RR for 1, 2), zero (MT), negative (LT, LL for -1, -2))

(add-algs "sdtwo"
	  '("RT" "sdtwo")
	  '("RR" "sdtwo")
	  '("MT" "sdtwo")
	  '("LT" "sdtwo")
	  '("LL" "sdtwo"))
(add-var-name "t" (py "sdtwo"))
(add-totality "sdtwo")

;; This adds the c.r. predicate TotalSdtwo of type sdtwo with clauses
;; TotalSdtwoRT:	TotalSdtwo RT
;; TotalSdtwoRR:	TotalSdtwo RR
;; TotalSdtwoMT:	TotalSdtwo MT
;; TotalSdtwoLT:	TotalSdtwo LT
;; TotalSdtwoLL:	TotalSdtwo LL

(add-totalnc "sdtwo")
(add-co "TotalSdtwo")
(add-co "TotalSdtwoNc")

(add-mr-ids "TotalSdtwo")
(add-co "TotalSdtwoMR")

(add-eqp "sdtwo")
(add-eqpnc "sdtwo")
(add-co "EqPSdtwo")
(add-co "EqPSdtwoNc")

(add-mr-ids "EqPSdtwo")
(add-co "EqPSdtwoMR")

;; SdtwoTotalVar
(set-goal "all t TotalSdtwo t")
(use "AllTotalIntro")
(assume "t^" "Tt")
(use "Tt")
;; Proof finished
(save "SdtwoTotalVar")

;; SdtwoEqToEqD
(set-goal "all t1,t2(t1=t2 -> t1 eqd t2)")
(cases)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
;; Proof finished.
(save "SdtwoEqToEqD")

(add-ids
 (list (list "Sdtwo" (make-arity (py "int")) "sdtwo"))
 '("Sdtwo(IntP One)" "InitSdtwoRT")
 '("Sdtwo(IntP(SZero One))" "InitSdtwoRR")
 '("Sdtwo IntZero" "InitSdtwoMT")
 '("Sdtwo(IntN One)" "InitSdtwoLT")
 '("Sdtwo(IntN(SZero One))" "InitSdtwoLL"))

(add-mr-ids "Sdtwo")

;; EfSdtwo
(set-goal "allnc d^(F -> Sdtwo d^)")
(assume "d^" "Absurd")
(simp (pf "d^ eqd IntP 1"))
(use "InitSdtwoRT")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfSdtwo")

;; SdtwoBound
(set-goal "all i(Sdtwo i -> abs i<=2)")
(assume "i" "Sdtwoi")
(elim "Sdtwoi")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdtwoBound")

;; SdtwoIntUMinus
(set-goal "allnc i(Sdtwo i -> Sdtwo(~i))")
(assume "i" "Sdtwoi")
(elim "Sdtwoi")
(use "InitSdtwoLT")
(use "InitSdtwoLL")
(use "InitSdtwoMT")
(use "InitSdtwoRT")
(use "InitSdtwoRR")
;; Proof finished.
(save "SdtwoIntUMinus")

(add-sound "SdtwoIntUMinus")
;; ok, SdtwoIntUMinusSound has been added as a new theorem:

;; allnc i,t^(SdtwoMR i t^ -> SdtwoMR(~i)(cSdtwoIntUMinus t^))

;; with computation rule

;; cSdtwoIntUMinus eqd([t][if t LT LL MT RT RR])

;; (cdp "SdtwoIntUMinusSound")
(deanimate "SdtwoIntUMinus")

;; To handle digit calculations without abundant case distinctions we
;; define (i) embeddings into the integers and (ii) inductive predicates
;; SdInj and SdtwoInj representing the graph of the injections of the
;; integers a with |a|<=1 (|a|<=2) into sd (sdtwo).  These predicates are
;; the same as the realizability predicates SdMR and SdtwoMR.  However,
;; usage of MR predicates is restricted to soundness proofs.

(add-program-constant "SdToInt" (py "sd=>int"))

(add-computation-rules
 "SdToInt SdR" "IntP 1"
 "SdToInt SdM" "IntZero"
 "SdToInt SdL" "IntN 1")

(set-totality-goal "SdToInt")
(use "AllTotalElim")
(cases)
(use "IntTotalVar")
(use "IntTotalVar")
(use "IntTotalVar")
;; Prove finished.
(save-totality)

(add-program-constant "IntToSd" (py "int=>sd"))

(add-computation-rules
 "IntToSd(IntP p)" "SdR"
 "IntToSd IntZero" "SdM"
 "IntToSd(IntN p)" "SdL")

(set-totality-goal "IntToSd")
(use "AllTotalElim")
(cases)
(assume "p")
(use "SdTotalVar")
(use "SdTotalVar")
(assume "p")
(use "SdTotalVar")
;; Prove finished.
(save-totality)

;; SdToIntToSdId
(set-goal "all s IntToSd(SdToInt s)=s")
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdToIntToSdId")

;; IntToSdToIntId
(set-goal "all d(abs d<=1 -> SdToInt(IntToSd d)=d)")
(cases)
(assume "p" "pBd")
(ng)
(simp "pBd")
(use "Truth")
(assume "Useless")
(use "Truth")
(assume "p" "pBd")
(ng)
(simp "pBd")
(use "Truth")
;; Proof finished.
(save "IntToSdToIntId")

;; IntTimesSdToSd
(set-goal "allnc d,e(Sd d -> Sd e -> Sd(d*e))")
(assume "d" "e")
(elim)
(elim)
(use "InitSdSdR")
(use "InitSdSdM")
(use "InitSdSdL")
(elim)
(use "InitSdSdM")
(use "InitSdSdM")
(use "InitSdSdM")
(elim)
(use "InitSdSdL")
(use "InitSdSdM")
(use "InitSdSdR")
;; Proof finished.
(save "IntTimesSdToSd")

(add-sound "IntTimesSdToSd")
;; ok, IntTimesSdToSdSound has been added as a new theorem:

;; allnc d,e,s^(
;;  SdMR d s^ -> allnc s^0(SdMR e s^0 -> SdMR(d*e)(cIntTimesSdToSd s^ s^0)))

;; with computation rule

;; cIntTimesSdToSd eqd([s,s0][if s s0 SdM [if s0 SdL SdM SdR]])

;; (cdp "IntTimesSdToSdSound")
(deanimate "IntTimesSdToSd")

(add-ids (list (list "SdInj" (make-arity (py "int") (py "sd"))))
	 '("SdInj 1 SdR" "InitSdSdRInj")
	 '("SdInj 0 SdM" "InitSdSdMInj")
	 '("SdInj(IntN 1)SdL" "InitSdSdLInj"))

(display-idpc "SdInj")
;; SdInj	non-computational
;; 	InitSdSdRInj:	SdInj 1 SdR
;; 	InitSdSdMInj:	SdInj 0 SdM
;; 	InitSdSdLInj:	SdInj(IntN 1)SdL

;; EfSdInj
(set-goal "allnc d^,s^(F -> SdInj d^ s^)")
(assume "d^" "s^" "Absurd")
(simp (pf "d^ eqd IntP 1"))
(simp (pf "s^ eqd SdR"))
(use "InitSdSdRInj")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfSdInj")

;; SdInjId
(set-goal "all d,s(SdInj d s -> SdToInt s=d)")
(assume "d" "s" "SdInjds")
(elim "SdInjds")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdInjId")

;; SdInjIntToSd
(set-goal "all d(abs d<=1 -> SdInj d(IntToSd d))")
(cases)
(assume "p" "pBd")
(ng)
(simp "pBd")
(use "InitSdSdRInj")
(assume "Useless")
(use "InitSdSdMInj")
(assume "p" "pBd")
(ng)
(simp "pBd")
(use "InitSdSdLInj")
;; Proof finished.
;; (cdp)
(save "SdInjIntToSd")

;; SdInjIntro
(set-goal "allnc d(Sd d -> exl s SdInj d s)")
(assume "d" "Sdd")
(elim "Sdd")
(intro 0 (pt "SdR"))
(use "InitSdSdRInj")
(intro 0 (pt "SdM"))
(use "InitSdSdMInj")
(intro 0 (pt "SdL"))
(use "InitSdSdLInj")
;; Proof finished.
;; (cdp)
(save "SdInjIntro")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [s]s

(animate "SdInjIntro")

;; SdInjElim
(set-goal "allnc d all s(SdInj d s -> Sd d)")
(assume "d")
(cases)
;; 3-5
(assume "SdInjSdRd")
(inst-with-to "SdInjId" (pt "d") (pt "SdR") "SdInjSdRd" "SdInjIdInst")
(simp "<-" "SdInjIdInst")
(use "InitSdSdR")
;; 4
(assume "SdInjSdMd")
(inst-with-to "SdInjId" (pt "d") (pt "SdM") "SdInjSdMd" "SdInjIdInst")
(simp "<-" "SdInjIdInst")
(use "InitSdSdM")
;; 5
(assume "SdInjSdLd")
(inst-with-to "SdInjId" (pt "d") (pt "SdL") "SdInjSdLd" "SdInjIdInst")
(simp "<-" "SdInjIdInst")
(use "InitSdSdL")
;; Proof finished.
;; (cdp)
(save "SdInjElim")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [s]s

(animate "SdInjElim")

;; We do the same for Sdtwo.

(add-program-constant "SdtwoToInt" (py "sdtwo=>int"))

(add-computation-rules
 "SdtwoToInt RT" "IntP 1"
 "SdtwoToInt RR" "IntP 2"
 "SdtwoToInt MT" "IntZero"
 "SdtwoToInt LT" "IntN 1"
 "SdtwoToInt LL" "IntN 2")

(set-totality-goal "SdtwoToInt")
(use "AllTotalElim")
(cases)
(use "IntTotalVar")
(use "IntTotalVar")
(use "IntTotalVar")
(use "IntTotalVar")
(use "IntTotalVar")
;; Prove finished.
(save-totality)

(add-program-constant "PosToSdtwo" (py "pos=>sdtwo"))

(add-computation-rules
 "PosToSdtwo One" "RT"
 "PosToSdtwo(SZero p)" "RR"
 "PosToSdtwo(SOne p)" "RR")

(set-totality-goal "PosToSdtwo")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(assume "p")
(use "SdtwoTotalVar")
(assume "p")
(use "SdtwoTotalVar")
;; Proof finished.
(save-totality) 

(add-program-constant "SdtwoUMinus" (py "sdtwo=>sdtwo"))

(add-computation-rules
 "SdtwoUMinus RT" "LT"
 "SdtwoUMinus RR" "LL"
 "SdtwoUMinus MT" "MT"
 "SdtwoUMinus LT" "RT"
 "SdtwoUMinus LL" "RR")

(set-totality-goal "SdtwoUMinus")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
;; Proof finished.
(save-totality) 

(add-program-constant "IntToSdtwo" (py "int=>sdtwo"))

(add-computation-rules
 "IntToSdtwo(IntP p)" "PosToSdtwo p"
 "IntToSdtwo IntZero" "MT"
 "IntToSdtwo(IntN p)" "SdtwoUMinus(PosToSdtwo p)")

(set-totality-goal "IntToSdtwo")
(use "AllTotalElim")
(cases)
(assume "p")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(assume "p")
(use "SdtwoTotalVar")
;; Proof finished.
(save-totality) 

;; SdtwoToIntToSdtwoId
(set-goal "all t IntToSdtwo(SdtwoToInt t)=t")
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdtwoToIntToSdtwoId")

;; IntToSdtwoToIntId
(set-goal "all i(abs i<=2 -> SdtwoToInt(IntToSdtwo i)=i)")
(cases)
(cases)
(assume "Useless")
(use "Truth")
(cases)
(assume "Useless")
(use "Truth")
(assume "p" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "p" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "p" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "Useless")
(use "Truth")
;; 4
(cases)
(assume "Useless")
(use "Truth")
(cases)
(assume "Useless")
(use "Truth")
(assume "p" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "p" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "p" "Absurd")
(use "EfAtom")
(use "Absurd")
;; Proof finished.
(save "IntToSdtwoToIntId")

(add-ids (list (list "SdtwoInj" (make-arity (py "int") (py "sdtwo"))))
	 '("SdtwoInj 1 RT" "InitSdtwoRTInj")
	 '("SdtwoInj 2 RR" "InitSdtwoRRInj")
	 '("SdtwoInj 0 MT" "InitSdtwoMTInj")
	 '("SdtwoInj(IntN 1)LT" "InitSdtwoLTInj")
	 '("SdtwoInj(IntN 2)LL" "InitSdtwoLLInj"))

(display-idpc "SdtwoInj")
;; SdtwoInj	non-computational
;; 	InitSdtwoRTInj:	SdtwoInj 1 RT
;; 	InitSdtwoRRInj:	SdtwoInj 2 RR
;; 	InitSdtwoMTInj:	SdtwoInj 0 MT
;; 	InitSdtwoLTInj:	SdtwoInj(IntN 1)LT
;; 	InitSdtwoLLInj:	SdtwoInj(IntN 2)LL

;; EfSdtwoInj
(set-goal "allnc d,t(F -> SdtwoInj d t)")
(assume "d" "t" "Absurd")
(simp (pf "d=1"))
(simp (pf "t=RT"))
(use "InitSdtwoRTInj")
(use "EfAtom")
(use "Absurd")
(use "EfAtom")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfSdtwoInj")

;; SdtwoInjId
(set-goal "all i,t(SdtwoInj i t -> SdtwoToInt t=i)")
(assume "i" "t" "SdtwoInjsit")
(elim "SdtwoInjsit")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "SdtwoInjId")

;; SdtwoInjIntro
(set-goal "allnc i(Sdtwo i -> exl t SdtwoInj i t)")
(assume "i" "Sdtwoi")
(elim "Sdtwoi")
;; 3-7
(intro 0 (pt "RT"))
(use "InitSdtwoRTInj")
;; 4
(intro 0 (pt "RR"))
(use "InitSdtwoRRInj")
;; 5
(intro 0 (pt "MT"))
(use "InitSdtwoMTInj")
;; 6
(intro 0 (pt "LT"))
(use "InitSdtwoLTInj")
;; 7
(intro 0 (pt "LL"))
(use "InitSdtwoLLInj")
;; Proof finished.
;; (cdp)
(save "SdtwoInjIntro")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [t]t

(animate "SdtwoInjIntro")

;; SdtwoInjElim
(set-goal "allnc i all t(SdtwoInj i t -> Sdtwo i)")
(assume "i")
(cases)
;; 3-7
(assume "SdtwoRTi")
(inst-with-to "SdtwoInjId" (pt "i") (pt "RT") "SdtwoRTi" "SdtwoInjIdInst")
(simp "<-" "SdtwoInjIdInst")
(use "InitSdtwoRT")
;; 4
(assume "SdtwoRRi")
(inst-with-to "SdtwoInjId" (pt "i") (pt "RR") "SdtwoRRi" "SdtwoInjIdInst")
(simp "<-" "SdtwoInjIdInst")
(use "InitSdtwoRR")
;; 5
(assume "SdtwoMTi")
(inst-with-to "SdtwoInjId" (pt "i") (pt "MT") "SdtwoMTi" "SdtwoInjIdInst")
(simp "<-" "SdtwoInjIdInst")
(use "InitSdtwoMT")
;; 6
(assume "SdtwoLTi")
(inst-with-to "SdtwoInjId" (pt "i") (pt "LT") "SdtwoLTi" "SdtwoInjIdInst")
(simp "<-" "SdtwoInjIdInst")
(use "InitSdtwoLT")
;; 7
(assume "SdtwoLLi")
(inst-with-to "SdtwoInjId" (pt "i") (pt "LL") "SdtwoLLi" "SdtwoInjIdInst")
(simp "<-" "SdtwoInjIdInst")
(use "InitSdtwoLL")
;; Proof finished.
;; (cdp)
(save "SdtwoInjElim")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [t]t

(animate "SdtwoInjElim")

;; SdtwoInjIntToSdtwo
(set-goal "all d(abs d<=2 -> SdtwoInj d(IntToSdtwo d))")
(cases)
;; 2-4
(cases)
(assume "Useless")
(use "InitSdtwoRTInj")
(cases)
(assume "Useless")
(use "InitSdtwoRRInj")
(assume "p" "Absurd")
(use "EfSdtwoInj")
(use "Absurd")
(assume "p" "Absurd")
(use "EfSdtwoInj")
(use "Absurd")
(assume "p" "Absurd")
(use "EfSdtwoInj")
(use "Absurd")
;; 3
(assume "Useless")
(use "InitSdtwoMTInj")
;; 4
(cases)
(assume "Useless")
(use "InitSdtwoLTInj")
(cases)
(assume "Useless")
(use "InitSdtwoLLInj")
(assume "p" "Absurd")
(use "EfSdtwoInj")
(use "Absurd")
(assume "p" "Absurd")
(use "EfSdtwoInj")
(use "Absurd")
(assume "p" "Absurd")
(use "EfSdtwoInj")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "SdtwoInjIntToSdtwo")

;; IntPlusSdToSdtwo
(set-goal "allnc d,e(Sd d -> Sd e -> Sdtwo(d+e))")
(assume "d" "e" "Sdd" "Sde")
(assert "exl s1 SdInj d s1")
(use "SdInjIntro")
(use "Sdd")
(assume "ExHyp1")
(by-assume "ExHyp1" "s1" "s1Prop")
(assert "exl s2 SdInj e s2")
(use "SdInjIntro")
(use "Sde")
(assume "ExHyp2")
(by-assume "ExHyp2" "s2" "s2Prop")
(use "SdtwoInjElim" (pt "IntToSdtwo(SdToInt s1+SdToInt s2)"))
(simp (pf "SdToInt s1+SdToInt s2=d+e"))
(use "SdtwoInjIntToSdtwo")
;; ?_20:abs(d+e)<=2
(use "IntLeTrans" (pt "abs d+abs e"))
(use "IntLeAbsPlus")
(use "IntLeTrans" (pt "IntP 1+IntP 1"))
(use "IntLeMonPlus")
(use "SdBound")
(use "Sdd")
(use "SdBound")
(use "Sde")
(use "Truth")
;; ?_19:SdToInt s1+SdToInt s2=d+e
(inst-with-to "SdInjId" (pt "d") (pt "s1") "s1Prop" "SdInjIdInst1")
(inst-with-to "SdInjId" (pt "e") (pt "s2") "s2Prop" "SdInjIdInst2")
(simp "SdInjIdInst1")
(simp "SdInjIdInst2")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "IntPlusSdToSdtwo")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [s,s0]IntToSdtwo(SdToInt s+SdToInt s0)

(add-sound "IntPlusSdToSdtwo")
;; ok, IntPlusSdToSdtwoSound has been added as a new theorem:

;; allnc d,e,s^(
;;  SdMR d s^ -> 
;;  allnc s^0(SdMR e s^0 -> SdtwoMR(d+e)(cIntPlusSdToSdtwo s^ s^0)))

;; with computation rule

;; cIntPlusSdToSdtwo eqd([s,s0]IntToSdtwo(SdToInt s+SdToInt s0))

;; (cdp "IntPlusSdToSdtwoSound")

(deanimate "IntPlusSdToSdtwo")

;; SdtwoToSdtwoToIntValue
(set-goal "allnc i(Sdtwo i -> exl t SdtwoToInt t=i)")
(assume "i" "Sdtwoi")
(inst-with-to "SdtwoInjIntro" (pt "i") "Sdtwoi" "SdtwoInjIntroInst")
(by-assume "SdtwoInjIntroInst" "t" "tProp")
(intro 0 (pt "t"))
(use "SdtwoInjId")
(use "tProp")
;; Proof finished.
;; (cdp)
(save "SdtwoToSdtwoToIntValue")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [t]t

(animate "SdtwoToSdtwoToIntValue")

;; For Gray code we also need proper signed digits

(add-ids
 (list (list "Psd" (make-arity (py "int")) "boole"))
 '("Psd(IntP One)" "InitPsdTrue")
 '("Psd(IntN One)" "InitPsdFalse"))

(add-mr-ids "Psd")

;; EfPsd
(set-goal "allnc d^(F -> Psd d^)")
(assume "d^" "Absurd")
(simp (pf "d^ eqd IntP 1"))
(use "InitPsdTrue")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfPsd")

;; PsdToAbsOne
(set-goal "all d(Psd d -> abs d=1)")
(assume "d" "Psdd")
(elim "Psdd")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "PsdToAbsOne")

;; PsdToSd
(set-goal "allnc d(Psd d -> Sd d)")
(assume "d" "Psdd")
(elim "Psdd")
(use "InitSdSdR")
(use "InitSdSdL")
;; Proof finished.
(save "PsdToSd")

(define eterm (proof-to-extracted-term))
(define neterm (nt eterm))
;; (pp neterm)
;; [boole0][if boole0 SdR SdL]

(add-sound "PsdToSd")
;; ok, PsdToSdSound has been added as a new theorem:

;; allnc d,boole^(PsdMR d boole^ -> SdMR d(cPsdToSd boole^))

;; with computation rule

;; cPsdToSd eqd([boole][if boole SdR SdL])

;; (cdp "PsdToSdSound")

(deanimate "PsdToSd")

;; PsdToSdtwo
(set-goal "allnc d(Psd d -> Sdtwo d)")
(assume "d" "Psdd")
(elim "Psdd")
(use "InitSdtwoRT")
(use "InitSdtwoLT")
;; Proof finished.
;; (cdp)
(save "PsdToSdtwo")

(define eterm (proof-to-extracted-term))
(define neterm (nt eterm))
;; (pp neterm)
;; [boole0][if boole0 RT LT]

(add-sound "PsdToSdtwo")
;; ok, PsdToSdtwoSound has been added as a new theorem:

;; allnc d,boole^(PsdMR d boole^ -> SdtwoMR d(cPsdToSdtwo boole^))

;; with computation rule

;; cPsdToSdtwo eqd([boole][if boole RT LT])

;; (cdp "PsdToSdtwoSound")

(deanimate "PsdToSdtwo")

;; PsdUMinus
(set-goal "allnc d(Psd d -> Psd(~d))")
(assume "d" "Psdd")
(elim "Psdd")
(use "InitPsdFalse")
(use "InitPsdTrue")
;; Proof finished.
;; (cdp)
(save "PsdUMinus")

(define eterm (proof-to-extracted-term))
(define neterm (nt eterm))
;; (pp neterm)
;; [boole0][if boole0 False True]

(add-sound "PsdUMinus")
;; > ok, PsdUMinusSound has been added as a new theorem:

;; allnc d,boole^(PsdMR d boole^ -> PsdMR(~d)(cPsdUMinus boole^))

;; with computation rule

;; cPsdUMinus eqd([boole][if boole False True])
;; ok, PsdUMinusSound has been added as a new theorem.

;; (pp "PsdUMinusSound")

(deanimate "PsdUMinus")

;; To handle digit calculations without abundant case distinctions we
;; define (i) embeddings into the integers and (ii) the inductive
;; predicate PsdInj representing the graph of the injection of the
;; integers a with |a|=1 into boole.  This predicate is the same as
;; the realizability predicate PsdMR.  However, usage of MR predicates
;; is restricted to soundness proofs.

(add-program-constant "BooleToInt" (py "boole=>int"))

(add-computation-rules
 "BooleToInt True" "IntP 1"
 "BooleToInt False" "IntN 1")

(set-totality-goal "BooleToInt")
(use "AllTotalElim")
(cases)
(use "IntTotalVar")
(use "IntTotalVar")
;; Prove finished.
(save-totality)

(add-program-constant "IntToBoole" (py "int=>boole"))

(add-computation-rules
 "IntToBoole(IntP p)" "True"
 "IntToBoole IntZero" "True"
 "IntToBoole(IntN p)" "False")

(set-totality-goal "IntToBoole")
(use "AllTotalElim")
(cases)
(assume "p")
(use "BooleTotalVar")
(use "BooleTotalVar")
(assume "p")
(use "BooleTotalVar")
;; Prove finished.
(save-totality)

;; BooleToIntToBooleId
(set-goal "all boole IntToBoole(BooleToInt boole)=boole")
(cases)
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "BooleToIntToBooleId")

;; IntToBooleToIntId
(set-goal "all d(abs d=1 -> BooleToInt(IntToBoole d)=d)")
(cases)
(assume "p" "pProp")
(ng)
(simp "pProp")
(use "Truth")
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "p" "pProp")
(ng)
(simp "pProp")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "IntToBooleToIntId")

(display-idpc "Psd")
;; Psd
;; 	InitPsdTrue:	Psd 1
;; 	InitPsdFalse:	Psd(IntN 1)

(add-ids (list (list "PsdInj" (make-arity (py "int") (py "boole"))))
	 '("PsdInj 1 True" "InitPsdTrueInj")
	 '("PsdInj(IntN 1)False" "InitPsdFalseInj"))

(display-idpc "PsdInj")
;; PsdInj	non-computational
;; 	InitPsdTrueInj:	PsdInj 1 True
;; 	InitPsdFalseInj:	PsdInj(IntN 1)False

;; EfPsdInj
(set-goal "allnc d^,boole^(F -> PsdInj d^ boole^)")
(assume "d^" "boole^" "Absurd")
(simp (pf "d^ eqd IntP 1"))
(simp (pf "boole^ eqd True"))
(use "InitPsdTrueInj")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfPsdInj")

;; PsdInjId
(set-goal "all d,boole(PsdInj d boole -> BooleToInt boole=d)")
(assume "d" "boole" "PsdInjHyp")
(elim "PsdInjHyp")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PsdInjId")

;; PsdInjIntro
(set-goal "allnc d(Psd d -> exl boole PsdInj d boole)")
(assume "d" "Psdd")
(elim "Psdd")
(intro 0 (pt "True"))
(use "InitPsdTrueInj")
(intro 0 (pt "False"))
(use "InitPsdFalseInj")
;; Proof finished.
;; (cdp)
(save "PsdInjIntro")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [boole]boole

(animate "PsdInjIntro")

;; PsdInjElim
(set-goal "allnc d all boole(PsdInj d boole -> Psd d)")
(assume "d")
(cases)
;; 3,4
(assume "PsdInjTrue")
(inst-with-to "PsdInjId" (pt "d") (pt "True") "PsdInjTrue" "PsdInjIdInst")
(simp "<-" "PsdInjIdInst")
(use "InitPsdTrue")
;; 4
(assume "PsdInjFalse")
(inst-with-to "PsdInjId" (pt "d") (pt "False") "PsdInjFalse" "PsdInjIdInst")
(simp "<-" "PsdInjIdInst")
(use "InitPsdFalse")
;; Proof finished.
; (cdp)
(save "PsdInjElim")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [boole]boole

(animate "PsdInjElim")

;; PsdToBooleToIntValue
(set-goal "allnc d(Psd d -> exl boole BooleToInt boole=d)")
(assume "d" "Psdd")
(inst-with-to "PsdInjIntro" (pt "d") "Psdd" "PsdInjIntroInst")
(by-assume "PsdInjIntroInst" "boole" "booleProp")
(intro 0 (pt "boole"))
(use "PsdInjId")
(use "booleProp")
;; Proof finished.
;; (cdp)
(save "PsdToBooleToIntValue")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [boole]boole

(animate "PsdToBooleToIntValue")

;; PsdInjIntToBoole
(set-goal "all d(abs d=1 -> PsdInj d(IntToBoole d))")
(cases)
(assume "p" "pProp")
(ng)
(simp "pProp")
(use "InitPsdTrueInj")
(assume "Absurd")
(use "EfPsdInj")
(use "Absurd")
(assume "p" "pProp")
(ng)
(simp "pProp")
(use "InitPsdFalseInj")
;; Proof finished.
;; (cdp)
(save "PsdInjIntToBoole")

;; IntTimesSdtwoPsdToSdtwo
(set-goal "allnc i,d(Sdtwo i -> Psd d -> Sdtwo(i*d))")
(assume "i" "d" "Sdtwoi")
(elim "Sdtwoi")
;; 3-7
(assume "Psdd")
(elim "Psdd")
;; 9,10
(ng)
(use "InitSdtwoRT")
;; 10
(ng)
(use "InitSdtwoLT")
;; 4
(assume "Psdd")
(elim "Psdd")
;; 14,15
(ng)
(use "InitSdtwoRR")
;; 15
(ng)
(use "InitSdtwoLL")
;; 5
(assume "Psdd")
(elim "Psdd")
;; 19,20
(ng)
(use "InitSdtwoMT")
;; 20
(ng)
(use "InitSdtwoMT")
;; 6
(assume "Psdd")
(elim "Psdd")
;; 24,25
(ng)
(use "InitSdtwoLT")
;; 25
(ng)
(use "InitSdtwoRT")
;; 7
(assume "Psdd")
(elim "Psdd")
;; 29,30
(ng)
(use "InitSdtwoLL")
;; 30
(ng)
(use "InitSdtwoRR")
;; Proof finished.
;; (cdp)
(save "IntTimesSdtwoPsdToSdtwo")

(define eterm (proof-to-extracted-term))
(define neterm (nt eterm))
;; (pp neterm)
;; [t0,boole1]
;;  [if t0
;;    [if boole1 RT LT]
;;    [if boole1 RR LL]
;;    MT
;;    [if boole1 LT RT]
;;    [if boole1 LL RR]]

(add-sound "IntTimesSdtwoPsdToSdtwo")
;; ok, IntTimesSdtwoPsdToSdtwoSound has been added as a new theorem:

;; allnc i,d,t^(
;;  SdtwoMR i t^ -> 
;;  allnc boole^(
;;   PsdMR d boole^ -> SdtwoMR(i*d)(cIntTimesSdtwoPsdToSdtwo t^ boole^)))

;; with computation rule

;; cIntTimesSdtwoPsdToSdtwo eqd
;; ([t,boole]
;;[if t [if boole RT LT] [if boole RR LL] MT [if boole LT RT] [if boole LL RR]])

;; (cdp "IntTimesSdtwoPsdToSdtwoSound")

(deanimate "IntTimesSdtwoPsdToSdtwo")

;; RealTimesPsdPsd
(set-goal "all d,x(Real x -> Psd d -> x*d*d===x)")
(assert "all d,x(Psd d -> x*d*d=+=x)")
(assume "d")
(cases)
(assume "as" "M" "Psdd")
(elim "Psdd")
;; 5,6
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; 6
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesPsdPsdEqS" "d" "x" "Rx" "Psdd")
(use "RealEqSToEq")
(autoreal)
(use "RealTimesPsdPsdEqS")
(use "Psdd")
;; Proof finished.
;; (cdp)
(save "RealTimesPsdPsd")

;; IntPlusPsdToSdtwo
(set-goal "allnc d,e(Psd d -> Psd e -> Sdtwo(d+e))")
(assume "d" "e")
(elim)
(elim)
(use "InitSdtwoRR")
(use "InitSdtwoMT")
(elim)
(use "InitSdtwoMT")
(use "InitSdtwoLL")
;; Proof finished.
;; (cdp)
(save "IntPlusPsdToSdtwo")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [boole,boole0][if boole [if boole0 RR MT] [if boole0 MT LL]]

(add-sound "IntPlusPsdToSdtwo")

;; ok, IntPlusPsdToSdtwoSound has been added as a new theorem:
;; allnc d,e,boole^(
;;  PsdMR d boole^ -> 
;;  allnc boole^0(
;;   PsdMR e boole^0 -> SdtwoMR(d+e)(cIntPlusPsdToSdtwo boole^ boole^0)))

;; with computation rule

;; cIntPlusPsdToSdtwo eqd
;; ([boole,boole0][if boole [if boole0 RR MT] [if boole0 MT LL]])

;; (cdp "IntPlusPsdToSdtwoSound")

(deanimate "IntPlusPsdToSdtwo")

;; IntTimesPsdToPsd
(set-goal "allnc d,e(Psd d -> Psd e -> Psd(d*e))")
(assume "d" "e")
(elim)
(elim)
(use "InitPsdTrue")
(use "InitPsdFalse")
(elim)
(use "InitPsdFalse")
(use "InitPsdTrue")
;; Proof finished.
;; (cdp)
(save "IntTimesPsdToPsd")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [boole,boole0][if boole boole0 [if boole0 False True]]
;; Corresponds to IntTimes (under BooleToInt IntToBoole)

(add-sound "IntTimesPsdToPsd")
;; ok, IntTimesPsdToPsdSound has been added as a new theorem:

;; allnc d,e,boole^(
;;  PsdMR d boole^ -> 
;;  allnc boole^0(
;;   PsdMR e boole^0 -> PsdMR(d*e)(cIntTimesPsdToPsd boole^ boole^0)))

;; with computation rule

;; cIntTimesPsdToPsd eqd([boole,boole0][if boole boole0 [if boole0 False True]])

;; (cdp "IntTimesPsdToPsdSound")

(deanimate "IntTimesPsdToPsd")

