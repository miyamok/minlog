;; 2020-12-17.  rea.scm

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "list.scm")
;; (libload "pos.scm")
;; (libload "int.scm")
;; (libload "rat.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")")
    (if (not (assoc "pos" ALGEBRAS))
	(myerror "First execute (libload \"pos.scm\")")
	(if (not (assoc "int" ALGEBRAS))
	    (myerror "First execute (libload \"int.scm\")")
	    (if (not (assoc "rat" ALGEBRAS))
		(myerror "First execute (libload \"rat.scm\")")))))

(display "loading rea.scm ...") (newline)

;; 1.  Real numbers
;; ================

;; We introduce the reals.  A real is a pair of a Cauchy sequence of
;; rationals and a modulus.  We view real as a data type (i.e., no
;; properties), and within this data type inductively define the
;; predicate Real x, meaning that x is a (proper) real.

(add-var-name "as" "bs" "cs" "ds" (py "nat=>rat"))
(add-var-name "M" "N" "L" (py "pos=>nat"))

(add-alg "rea" (list "RealConstr" "(nat=>rat)=>(pos=>nat)=>rea"))
(add-var-name "x" "y" "z" (py "rea"))

(add-eqp "rea")

;; (pp "EqPReaRealConstr")

;; allnc as^,as^0(
;;  allnc n^,n^0(EqPNat n^ n^0 -> EqPRat(as^ n^)(as^0 n^0)) -> 
;;  allnc M^,M^0(
;;   allnc p^,p^0(EqPPos p^ p^0 -> EqPNat(M^ p^)(M^0 p^0)) -> 
;;   EqPRea(RealConstr as^ M^)(RealConstr as^0 M^0)))

(add-eqpnc "rea")

;; We prefer to work with a simple direct definition of TotalRea and
;; then show its equivalence to the general definition x eqp x.

(add-ids
 (list (list "TotalRea" (make-arity (py "rea")) "rea"))
 '("allnc as^(allnc n^(TotalNat n^ -> TotalRat(as^ n^)) ->
    allnc M^(allnc p^(TotalPos p^ -> TotalNat(M^ p^)) ->
    TotalRea(RealConstr as^ M^)))"
   "TotalReaRealConstr"))

(add-ids
 (list (list "TotalReaNc" (make-arity (py "rea"))))
 '("allnc as^(allnc n^(TotalNatNc n^ -> TotalRatNc(as^ n^)) ->
    allnc M^(allnc p^(TotalPosNc p^ -> TotalNatNc(M^ p^)) ->
    TotalReaNc(RealConstr as^ M^)))"
   "TotalReaNcRealConstr"))

;; EqPTotalNatToRatLeft
(set-goal "allnc as^1,as^2(
     allnc n^1,n^2(EqPNat n^1 n^2 -> EqPRat(as^1 n^1)(as^2 n^2)) -> 
     allnc n^(TotalNat n^ -> TotalRat(as^1 n^)))")
(assume "as^1" "as^2" "EqPas1as2" "n^" "Tn")
(use "EqPRatToTotalLeft" (pt "as^2 n^"))
(use "EqPas1as2")
(use "EqPNatRefl")
(use "Tn")
;; Proof finished.
;; (cdp)
(save "EqPTotalNatToRatLeft")

;; EqPTotalNatToRatRight
(set-goal "allnc as^1,as^2(
     allnc n^1,n^2(EqPNat n^1 n^2 -> EqPRat(as^1 n^1)(as^2 n^2)) -> 
     allnc n^(TotalNat n^ -> TotalRat(as^2 n^)))")
(assume "as^1" "as^2" "EqPas1as2" "n^" "Tn")
(use "EqPRatToTotalRight" (pt "as^1 n^"))
(use "EqPas1as2")
(use "EqPNatRefl")
(use "Tn")
;; Proof finished.
;; (cdp)
(save "EqPTotalNatToRatRight")

;; EqPTotalPosToNatLeft
(set-goal "allnc M^1,M^2(
     allnc p^,p^0(EqPPos p^ p^0 -> EqPNat(M^1 p^)(M^2 p^0)) -> 
     allnc p^(TotalPos p^ -> TotalNat(M^1 p^)))")
(assume "M^1" "M^2" "EqPM1M2" "p^" "Tp")
(use "EqPNatToTotalLeft" (pt "M^2 p^"))
(use "EqPM1M2")
(use "EqPPosRefl")
(use "Tp")
;; Proof finished.
;; (cdp)
(save "EqPTotalPosToNatLeft")

;; EqPTotalPosToNatRight
(set-goal "allnc M^1,M^2(
     allnc p^,p^0(EqPPos p^ p^0 -> EqPNat(M^1 p^)(M^2 p^0)) -> 
     allnc p^(TotalPos p^ -> TotalNat(M^2 p^)))")
(assume "M^1" "M^2" "EqPM1M2" "p^" "Tp")
(use "EqPNatToTotalRight" (pt "M^1 p^"))
(use "EqPM1M2")
(use "EqPPosRefl")
(use "Tp")
;; Proof finished.
;; (cdp)
(save "EqPTotalPosToNatRight")

;; EqPReaToTotalLeft
(set-goal "allnc x^,y^(EqPRea x^ y^ -> TotalRea x^)")
(assume "x^" "y^" "EqPxy")
(elim "EqPxy")
(assume "as^1" "as^2" "EqPas1as2" "M^1" "M^2" "EqPM1M2")
(use "TotalReaRealConstr")
(use "EqPTotalNatToRatLeft" (pt "as^2"))
(use "EqPas1as2")
(use "EqPTotalPosToNatLeft" (pt "M^2"))
(use "EqPM1M2")
;; Proof finished.
;; (cdp)
(save "EqPReaToTotalLeft")

;; EqPReaToTotalRight
(set-goal "allnc x^,y^(EqPRea x^ y^ -> TotalRea y^)")
(assume "x^" "y^" "EqPxy")
(elim "EqPxy")
(assume "as^1" "as^2" "EqPas1as2" "M^1" "M^2" "EqPM1M2")
(use "TotalReaRealConstr")
(use "EqPTotalNatToRatRight" (pt "as^1"))
(use "EqPas1as2")
(use "EqPTotalPosToNatRight" (pt "M^1"))
(use "EqPM1M2")
;; Proof finished.
;; (cdp)
(save "EqPReaToTotalRight")

;; EqPReaRefl
(set-goal "allnc x^(TotalRea x^ -> EqPRea x^ x^)")
(assume "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(use "EqPReaRealConstr")
;; 5,6
(assume "n^1" "n^2" "EqPn1n2")
(simp "<-" (pf "n^1 eqd n^2"))
;; 8,9
(use "EqPRatRefl")
(use "Tas")
(use "EqPNatToTotalLeft" (pt "n^2"))
(use "EqPn1n2")
;; 9
(use "EqPNatNcToEqD")
(use "EqPn1n2")
;; 6
(assume "p^1" "p^2" "EqPp1p2")
(simp "<-" (pf "p^1 eqd p^2"))
;; 15,16
(use "EqPNatRefl")
(use "TM")
(use "EqPPosToTotalLeft" (pt "p^2"))
(use "EqPp1p2")
;; 16
(use "EqPPosToEqD")
(use "EqPp1p2")
;; Proof finished.
;; (cdp)
(save "EqPReaRefl")

;; End of proof of the equivalence of the simple direct definition of
;; TotalRea with the general definition x eqp x.

;; ReaTotalVar
(set-goal "all x TotalRea x")
(cases)
(assume "as" "M")
(use "TotalReaRealConstr")
(use "AllTotalElim")
(assume "n")
(use "RatTotalVar")
(use "AllTotalElim")
(assume "p")
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save "ReaTotalVar")

;; To conveniently access the two fields of a real, we provide seq and
;; mod as informative names to be used (postfix) in display strings.

(add-program-constant "RealSeq" (py "rea=>nat=>rat") t-deg-zero 'const 1)

(add-token
 "seq"
 'postfix-op
 (lambda (x)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "RealSeq"))
    x)))

(add-display
 (py "nat=>rat")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "RealSeq"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 1 (length args)))
	 (let ((arg (car args)))
	   (list
	    'postfix-op "seq"
	    (term-to-token-tree arg)))
	 #f))))

(add-computation-rules
 "(RealConstr as M)seq" "as")

(set-totality-goal "RealSeq")
(assume "x^" "Tx" "n^" "Tn")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(ng)
(use "Tas")
(use "Tn")
;; Proof finished.
;; (cdp)
(save-totality)

(add-program-constant "RealMod" (py "rea=>pos=>nat") t-deg-zero 'const 1)

(add-token
 "mod"
 'postfix-op
 (lambda (x)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "RealMod"))
    x)))

(add-display
 (py "pos=>nat")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "RealMod"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 1 (length args)))
	 (let ((arg (car args)))
	   (list
	    'postfix-op "mod"
	    (term-to-token-tree arg)))
	 #f))))

(add-computation-rules
 "(RealConstr as M)mod" "M")

;; RealModTotal
(set-totality-goal "RealMod")
(assume "x^" "Tx" "p^" "Tp")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(ng #t)
(use  "TM")
(use "Tp")
;; Proof finished.
;; (cdp)
(save-totality)

;; (pp (pt "x seq n"))
;; (pp (pt "x mod p"))

;; 2. Parsing and display for arithmetical operations
;; ==================================================

(add-item-to-algebra-edge-to-embed-term-alist
 "rat" "rea"
 (let ((var (make-var (make-alg "rat") -1 t-deg-one ""))
       (n (make-var (make-alg "nat") -1 t-deg-one ""))
       (l (make-var (make-alg "nat") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (mk-term-in-app-form
         (make-term-in-const-form
          (constr-name-to-constr "RealConstr"))
         (make-term-in-abst-form ;constant Cauchy sequence
          n (make-term-in-var-form var))
         (make-term-in-abst-form ;Zero modulus
          l (make-term-in-const-form
             (constr-name-to-constr "Zero")))))))

;; (alg-le? (make-alg "rat") (make-alg "rea"))

(add-program-constant "RealPlus" (py "rea=>rea=>rea"))
(add-program-constant "RealUMinus" (py "rea=>rea"))
(add-program-constant "RealMinus" (py "rea=>rea=>rea"))
(add-program-constant "RealTimes" (py "rea=>rea=>rea"))
(add-program-constant "RealUDiv" (py "rea=>pos=>rea"))
(add-program-constant "RealDiv" (py "rea=>rea=>rea"))
(add-program-constant "RealAbs" (py "rea=>rea"))
(add-program-constant "RealExp" (py "rea=>int=>rea"))
(add-program-constant "RealMax" (py "rea=>rea=>rea"))
(add-program-constant "RealMin" (py "rea=>rea=>rea"))

(add-token-and-type-to-name "+" (py "rea") "RealPlus")
(add-token-and-type-to-name "~" (py "rea") "RealUMinus")
(add-token-and-type-to-name "-" (py "rea") "RealMinus")
(add-token-and-type-to-name "*" (py "rea") "RealTimes")
(add-token-and-type-to-name "/" (py "rea") "RealDiv")
(add-token-and-type-to-name "abs" (py "rea") "RealAbs")

(add-token-and-types-to-name "**" (list (py "rea") (py "pos")) "RealExp")
(add-token-and-types-to-name "**" (list (py "rea") (py "nat")) "RealExp")
(add-token-and-types-to-name "**" (list (py "rea") (py "int")) "RealExp")

(add-token-and-type-to-name "max" (py "rea") "RealMax")
(add-token-and-type-to-name "min" (py "rea") "RealMin")

(add-display (py "rea") (make-display-creator "RealPlus" "+" 'add-op))
(add-display (py "rea") (make-display-creator1 "RealUMinus" "~" 'prefix-op))
(add-display (py "rea") (make-display-creator "RealMinus" "-" 'add-op))
(add-display (py "rea") (make-display-creator "RealTimes" "*" 'mul-op))
(add-display (py "rea") (make-display-creator "RealDiv" "/" 'mul-op))
(add-display (py "rea") (make-display-creator1 "RealAbs" "abs" 'prefix-op))
(add-display (py "rea") (make-display-creator "RealExp" "**" 'exp-op))
(add-display (py "rea") (make-display-creator "RealMax" "max" 'mul-op))
(add-display (py "rea") (make-display-creator "RealMin" "min" 'mul-op))

(add-display
 (py "rea")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "RealConstr"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 2 (length args))
	      (term-in-abst-form? (car args))
	      (not (member (term-in-abst-form-to-var (car args))
			   (term-to-free
			    (term-in-abst-form-to-kernel (car args))))))
	 (term-to-token-tree (term-to-original
			      (term-in-abst-form-to-kernel (car args))))
	 #f))))

;; (pp (pt "(IntN p#q)+RealConstr([n]1)([p]7)"))
;; (IntN p#q)+1

;; 3.  Arithmetic
;; ==============

;; RealPos is a decidable property and hence can be considered as a
;; program constant.

(add-program-constant "RealPos" (py "rea=>pos=>boole"))

(add-display
 (make-alg "boole")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "RealPos"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 2 (length args)))
	 (let ((arg1 (car args))
	       (arg2 (cadr args)))
	   (list
	    'appterm ""
	    (list
	     'appterm ""
	     (list 'const "RealPos")
	     (term-to-token-tree (term-to-original arg1)))
	    (term-to-token-tree (term-to-original arg2))))
	 #f))))

(add-computation-rules "RealPos(RealConstr as M)p" "(1#2**p)<=as(M(p+1))")

;; EqPReaAux reduces a goal allnc x^,y^(EqPRea x^ y^ -> (Pvar rea rea)x^ y^)
;; to another one with x^, y^ in RealConstr form.  This can be done since
;; rea has one constructor only.

;; EqPReaAux
(set-goal "allnc as^,M^,bs^,N^(
 EqPRea(RealConstr as^ M^)(RealConstr bs^ N^) ->
 (Pvar rea rea)(RealConstr as^ M^)(RealConstr bs^ N^)) -> 
 allnc x^,y^(EqPRea x^ y^ -> (Pvar rea rea)x^ y^)")
(assume "Hyp" "x^" "y^" "EqPxy")
(elim "EqPxy")
(assume "as^1" "as^2" "EqPas1as2" "M^1" "M^2" "EqPM1M2")
(use "Hyp")
(use "EqPReaRealConstr")
(use "EqPas1as2")
(use "EqPM1M2")
;; Proof finished.
;; (cdp)
(save "EqPReaAux")

;; 2020-07-13.  Changed because of pure unfolding of the premise.
;; EqPReaElimLeft
(set-goal "allnc x^,y^(EqP x^ y^ -> EqP(x^ seq)(y^ seq))")
(assume "x^" "y^" "EqPxy")
(elim "EqPxy")
(assume "as^1" "as^2" "EqPas1as2" "M^1" "M^2" "EqPM1M2")
(ng #t)
(assume "n^1" "n^2" "n1=n2")
(use "EqPas1as2")
(use "n1=n2")
;; Proof finished.
;; (cdp)
(save "EqPReaElimLeft")

;; 2020-07-13.  Changed because of pure unfolding of the premise.
;; EqPReaElimRight
(set-goal "allnc x^,y^(EqP x^ y^ -> EqP(x^ mod)(y^ mod))")
(assume "x^" "y^" "EqPxy")
(elim "EqPxy")
(assume "as^1" "as^2" "EqPas1as2" "M^1" "M^2" "EqPM1M2")
(ng #t)
(assume "p^1"  "p^2" "p1=p2")
(use "EqPM1M2")
(use "p1=p2")
;; Proof finished.
;; (cdp)
(save "EqPReaElimRight")

;; 2020-07-13.  Not needed any more.
;; ;; To be moved into libnat.scm
;; ;; AllEqPNatElim
;; (set-goal "allnc n^(TotalNat n^ -> (Pvar nat nat)n^ n^) ->
;;  allnc n^1,n^2(EqPNat n^1 n^2 -> (Pvar nat nat)n^1 n^2)")
;; (assume "THyp" "n^1" "n^2" "EqPn1n2")
;; ;; (search-about 'all "EqP" "Nat" "Sym")
;; (simp (pf "n^1 eqd n^2"))
;; (use "THyp")
;; (use "EqPNatToTotalRight" (pt "n^1"))
;; (use "EqPn1n2")
;; (use "EqPNatNcToEqD") ;provide EqPNatToEqD in libnat.scm
;; (use "EqPn1n2")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "AllEqPNatElim")

;; ;; To be moved into libpos.scm
;; ;; AllEqPPosElim
;; (set-goal "allnc p^(TotalPos p^ -> (Pvar pos pos)p^ p^) ->
;;  allnc p^1,p^2(EqPPos p^1 p^2 -> (Pvar pos pos)p^1 p^2)")
;; (assume "THyp" "p^1" "p^2" "EqPp1p2")
;; ;; (search-about 'all "EqP" "Pos" "Sym")
;; (simp (pf "p^1 eqd p^2"))
;; (use "THyp")
;; (use "EqPPosToTotalRight" (pt "p^1"))
;; (use "EqPp1p2")
;; (use "EqPPosToEqD")
;; (use "EqPp1p2")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "AllEqPPosElim")

;; EqPReaElimLeftRealConstr
(set-goal "allnc as^,M^,bs^,N^(
 EqPRea(RealConstr as^ M^)(RealConstr bs^ N^) ->
 allnc n^,m^(EqPNat n^ m^ -> EqPRat(as^ n^)(bs^ m^)))")
(assume "as^" "M^" "bs^" "N^" "EqPxy")
;; (use "AllEqPNatElim")
(use-with "EqPReaElimLeft"
	  (pt "(RealConstr as^ M^)") (pt "(RealConstr bs^ N^)")
	  "EqPxy")
;; Proof finished.
;; (cdp)
(save "EqPReaElimLeftRealConstr")

;; EqPReaElimRightRealConstr
(set-goal "allnc as^,M^,bs^,N^(
 EqPRea(RealConstr as^ M^)(RealConstr bs^ N^) ->
 allnc p^,q^(EqPPos p^ q^ -> EqPNat(M^ p^)(N^ q^)))")
(assume "as^" "M^" "bs^" "N^" "EqPxy")
;; (use "AllEqPPosElim")
(use-with "EqPReaElimRight"
	  (pt "(RealConstr as^ M^)") (pt "(RealConstr bs^ N^)")
	  "EqPxy")
;; Proof finished.
;; (cdp)
(save "EqPReaElimRightRealConstr")

;; RealPosTotal
(set-totality-goal "RealPos")
(assume "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(use "AllTotalElim")
(assume "p")
(ng #t)
(use "RatLeTotal")
(use "RatTotalVar")
(use "Tas")
(use "TM")
(use "PosTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; RealLt is a decidable property and hence can be considered as a
;; program constant.

(add-program-constant "RealLt" (py "rea=>rea=>pos=>boole"))

(add-display
 (make-alg "boole")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "RealLt"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 3 (length args)))
	 (let ((arg1 (car args))
	       (arg2 (cadr args))
	       (arg3 (caddr args)))
	   (list
	    'appterm ""
	    (list
	     'appterm ""
	     (list
	      'appterm ""
	      (list 'const "RealLt")
	      (term-to-token-tree (term-to-original arg1)))
	     (term-to-token-tree (term-to-original arg2)))
	    (term-to-token-tree (term-to-original arg3))))
	 #f))))

(add-computation-rules
 "RealLt(RealConstr as M)(RealConstr bs N)p"
 "RealPos(RealConstr bs N-RealConstr as M)p")

;; Rules for RealUMinus

(add-computation-rules
 "~(RealConstr as M)" "RealConstr([n]~(as n))M")

;; RealUMinusTotal
(set-totality-goal "RealUMinus")
(assume "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(ng #t)
(intro 0)
(use "AllTotalElim")
(assume "n")
(use "RatUMinusTotal")
(use "Tas")
(use "NatTotalVar")
(use "TM")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for RealPlus

(add-computation-rules
 "RealConstr as M+RealConstr bs N"
 "RealConstr([n]as n+bs n)([p]M(PosS p)max N(PosS p))")

;; RealPlusTotal
(set-totality-goal "RealPlus")
(assume "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(assume "y^" "Ty")
(elim "Ty")
(assume "bs^" "Tbs" "N^" "TN")
(ng #t)
(intro 0)
(use "AllTotalElim")
(assume "n")
(use "RatPlusTotal")
(use "Tas")
(use "NatTotalVar")
(use "Tbs")
(use "NatTotalVar")
;; 10
(use "AllTotalElim")
(assume "p")
(use "NatMaxTotal")
(use "TM")
(use "PosSTotal")
(use "PosTotalVar")
(use "TN")
(use "PosSTotal")
(use "PosTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for RealMinus

(add-computation-rules
 "x-y" "x+ ~y")

(set-totality-goal "RealMinus")
(assume "x^" "Tx"  "y^" "Ty")
(use "RealPlusTotal")
(use "Tx")
(use "RealUMinusTotal")
(use "Ty")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for RealUDiv
(add-computation-rules
 "RealUDiv(RealConstr as M)q" "RealConstr([n]RatUDiv(as n))([p]M(2*PosS q+p))")

;; RealUDivTotal
(set-totality-goal "RealUDiv")
(assume "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(use "AllTotalElim")
(assume "p")
(ng #t)
(intro 0)
(use "AllTotalElim")
(assume "n")
(use "RatUDivTotal")
(use "Tas")
(use "NatTotalVar")
(use "AllTotalElim")
(assume "p1")
(use "TM")
(use "PosTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; RealLtTotal
(set-totality-goal "RealLt")
(assume "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(assume "y^" "Ty")
(elim "Ty")
(assume "bs^" "Tbs" "N^" "TN")
(ng #t)
(use "AllTotalElim")
(assume "p")
(use "RatLeTotal")
(use "RatTotalVar")
(use "RatPlusTotal")
(use "Tbs")
(use "NatMaxTotal")
(use "TN")
(use "PosTotalVar")
(use "TM")
(use "PosTotalVar")
(use "RatUMinusTotal")
(use "Tas")
(use "NatMaxTotal")
(use "TN")
(use "PosTotalVar")
(use "TM")
(use "PosTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for RealAbs

(add-computation-rules
 "abs(RealConstr as M)" "RealConstr([n]abs(as n))M")

;; RealAbsTotal
(set-totality-goal "RealAbs")
(assume "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(ng #t)
(intro 0)
(use "AllTotalElim")
(assume "n")
(use "RatAbsTotal")
(use "Tas")
(use "NatTotalVar")
;; 7
(use "AllTotalElim")
(assume "p")
(use "TM")
(use "PosTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

(add-program-constant "RealInv" (py "rea=>pos=>rea"))

(add-computation-rules
 "RealInv(RealConstr as M)q"
 "RealConstr([n]1/as n)([p]M(2*PosS q+p)max M(PosS q))")

;; RealInvTotal
(set-totality-goal "RealInv")
(assume "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(use "AllTotalElim")
(assume "p")
(ng #t)
(intro 0)
;; 8,9
(use "AllTotalElim")
(assume "n")
(use "RatTimesTotal")
(use "RatTotalVar")
(use "RatUDivTotal")
(use "Tas")
(use "NatTotalVar")
;; 9
(use "AllTotalElim")
(assume "p1")
(use "NatMaxTotal")
(use "TM")
(use "PosTotalVar")
(use "TM")
(use "PosTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; ;; Rules for RealExp : rea=>int=>rea

;; (add-computation-rules
;;  "x**(IntP One)" "x"
;;  "x**(IntP(SZero p))" "(x**(IntP p))*(x**(IntP p))"
;;  "x**(IntP(SOne p))" "(x**(IntP(SZero p)))*x"
;;  "x**IntZero" "RealConstr([n](RatConstr(IntPos One)One))([p]Zero)")

;; Rules for RealTimes require the Archimedian property, in the form
;; of a pconst RealBd.  We first define an auxiliary function
;; ListNatMax, then RealBd and finally the computation rule for RealTimes.
;; Its properties require the predicate Cauchy, which we define first.

;; 4.  Inductive predicates Cauchy, Mon, Real
;; ==========================================

;; To work with reals, we use a predicate constant Cauchy which takes
;; two arguments, a sequence of rationals and a modulus.

;; We introduce Cauchy as an inductively defined predicate (which may
;; in this case also be called a record).

(add-ids
 (list (list "Cauchy" (make-arity (py "nat=>rat") (py "pos=>nat"))))
 '("allnc as,M(
    allnc p,n,m(M p<=n -> M p<=m -> abs(as n+ ~(as m))<=(1#2**p)) ->
    Cauchy as M)" "CauchyIntro"))

;; Similarly, we introduce a predicate constant Mon, taking a sequence
;; of positive numbers as argument, to express monotonicity.

(add-ids (list (list "Mon" (make-arity (py "pos=>nat"))))
	 '("allnc M(allnc p,q(p<=q -> M p<=M q) -> Mon M)" "MonIntro"))

;; CauchyElim
(set-goal
 "allnc as,M(Cauchy as M ->
             allnc p,n,m(M p<=n -> M p<=m -> abs(as n+ ~(as m))<=(1#2**p)))")
(assume "as" "M")
(elim)
(search)
;; Proof finished.
;; (cdp)
(save "CauchyElim")

;; MonElim
(set-goal "allnc M(Mon M -> allnc p,q(p<=q -> M p<=M q))")
(assume "M")
(elim)
(search)
;; Proof finished.
;; (cdp)
(save "MonElim")

;; EfCauchy
(set-goal "F -> allnc as,M Cauchy as M")
(assume "Absurd" "as" "M")
(intro 0)
(strip)
(use "EfAtom")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCauchy")

;; EfMon
(set-goal "F -> allnc M Mon M")
(assume "Absurd" "M")
(intro 0)
(strip)
(use "EfAtom")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfMon")

;; We introduce Real as an inductively defined predicate (which in this
;; case may also be called a record).  Then we can prove theorems:

;; RealIntro: allnc x(Cauchy(x seq)(x mod) -> Mon(x mod) -> Real x)
;; RealToCauchySeq: allnc as,M(Real(RealConstr as M) -> Cauchy as M)
;; RealToMonMod: allnc as,M(Real(RealConstr as M) -> Mon M)

;; Alternative formulation (worse, since usability is restricted)
;; RealIntro: allnc as,M(Cauchy as M -> Mon M -> Real RealConstr as M) 
;; RealToCauchySeq: allnc x(Real x -> Cauchy(x seq)(x mod))
;; RealToMonMod: allnc x(Real x -> Mon(x mod))

(add-ids
 (list (list "Real" (make-arity (py "rea"))))
 '("all x(Cauchy(x seq)(x mod) -> Mon(x mod) -> Real x)" "RealIntro"))

;; RealToCauchy
(set-goal "all x(Real x -> Cauchy(x seq)(x mod))")
(assume "x")
(elim)
(auto)
;; Proof finished.
;; (cdp)
(save "RealToCauchy")

;; RealToMon
(set-goal "all x(Real x -> Mon(x mod))")
(assume "x")
(elim)
(auto)
;; Proof finished.
;; (cdp)
(save "RealToMon")

;; The following variants will be more useful, because their heads will
;; be more often of the form of a given goal.

;; RealConstrToCauchy
(set-goal "all as,M(Real(RealConstr as M) -> Cauchy as M)")
(strip)
(use-with "RealToCauchy" (pt "RealConstr as M") 1)
;; Proof finished.
;; (cdp)
(save "RealConstrToCauchy")

;; RealConstrToMon
(set-goal "all as,M(Real(RealConstr as M) -> Mon M)")
(strip)
(use-with "RealToMon" (pt "RealConstr as M") 1)
;; Proof finished.
;; (cdp)
(save "RealConstrToMon")

;; EfReal
(set-goal "F -> all x Real x")
(assume "Absurd")
(cases)
(assume "as" "M")
(intro 0)
(ng)
(use "EfCauchy")
(use "Absurd")
(ng)
(use "EfMon")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfReal")

;; RealRat
(set-goal "allnc a Real a")
(assume "a")
(use "RealIntro")
(use "CauchyIntro")
(assume "p" "n" "m" "Useless1" "Useless2")
(ng #t)
(simprat (pf "a+ ~a==0"))
(use "Truth")
(use "Truth")
(use "MonIntro")
(assume "p" "q" "p<=q")
(ng)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealRat")

;; 4a.  RealTimes
;; ==============

;; We first define an auxiliary function ListNatMax, then RealBd and
;; finally the computation rule for RealTimes.

(add-var-name "ns" "ms" (py "list nat"))
(add-program-constant "ListNatMax" (py "list nat=>nat") t-deg-zero)

(add-computation-rules
 "ListNatMax(Nil nat)" "Zero"
 "ListNatMax(n:)" "n"
 "ListNatMax(n::m::ns)" "n max ListNatMax(m::ns)")

;; (pp (nt (pt "ListNatMax(2::6::1::3::4:)")))
;; Succ(Succ(Succ(Succ(Succ(Succ Zero)))))

(set-totality-goal "ListNatMax")
(use "AllTotalElim")
(ind)
;; 3,4
(use "NatTotalVar")
;; 4
(assume "n")
(cases)
;; 6,7
(assume "Useless")
(use "NatTotalVar")
;; 7
(assume "m" "ns" "IH")
(ng #t)
(use "NatMaxTotal")
(use "NatTotalVar")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

;; ListNatMaxEqP
(set-goal "allnc ns^1,ns^2(EqP ns^1 ns^2 ->
 EqP(ListNatMax ns^1)(ListNatMax ns^2))")
(assume "ns^1" "ns^2" "EqPns1ns2")
(elim "EqPns1ns2")
;; 3,4
(ng #t)
(use "EqPNatZero")
;; 4
(assume "n^1" "n^2" "EqPn1n2" "ns^3" "ns^4" "EqPns3ns4")
(elim "EqPns3ns4")
;; 7,8
(assume "Useless")
(ng #t)
(use "EqPn1n2")
;; 8
(assume "n^3" "n^4" "EqPn3n4" "ns^5" "ns^6" "EqPns5ns6" "Hyp1" "Hyp2")
(ng #t)
(use "NatMaxEqP")
(use "EqPn1n2")
(use "Hyp2")
;; Proof finished.
;; (cdp)
(save "ListNatMaxEqP")

;; (display-pconst "ListNatMax")

;; ListNatMaxUB
(set-goal "all ms,n(n<Lh ms -> ListNatProj n ms<=ListNatMax ms)")
(ind)
;; 2,3
(ng)
(assume "n" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "m")
(cases)
;; 8,9
(assume "Useless")
(cases)
;; 11,12
(ng)
(strip)
(use "Truth")
;; 12
(ng)
(assume "n" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 9
(assume "m1" "ms" "IH")
(cases)
;; 19,20
(assume "Useless")
(ng)
(use "NatMaxUB1")
;; 20
(ng)
(assume "n1" "n1Prop")
(use "NatLeTrans" (pt "ListNatMax(m1::ms)"))
(use "IH")
(use "n1Prop")
(use "NatMaxUB2")
;; Proof finished.
;; (cdp)
(save "ListNatMaxUB")

;; ListNatMaxFBar
(set-goal "all nat=>nat,n,l(n<l -> (nat=>nat)n<=ListNatMax((nat=>nat)fbar l))")
(assume "nat=>nat" "n" "l" "n<l")
(inst-with-to "ListNatProjFBar" (pt "l") (pt "n") (pt "nat=>nat") "n<l" "Inst")
(simp "<-" "Inst")
(drop "Inst")
(use "ListNatMaxUB")
(use "n<l")
;; Proof finished.
;; (cdp)
(save "ListNatMaxFBar")

;; We need some more auxiliary concepts.

(animate "RatLeBound")
(animate "RatLeAbsBound")
;; (display-pconst "cRatLeAbsBound")

;; cRatLeAbsBoundTotal
(set-totality-goal "cRatLeAbsBound")
(use "AllTotalElim")
(assume "a")
(ng)
(use "RatIfTotal")
(use "RatTotalVar")
(assume "k^" "p^" "Tk" "Tp")
(use "IntIfTotal")
(use "Tk")
(use "NatTotalVar")
;; 10
(use "AllTotalElim")
(assume "p1")
(use "NatMinusTotal")
(use "NatTotalVar")
(use "PosLogTotal")
(use "Tp")
;; 11
(use "AllTotalElim")
(assume "p1")
(use "NatMinusTotal")
(use "NatTotalVar")
(use "PosLogTotal")
(use "Tp")
;; Proof finished.
;; (cdp)
(save-totality)

(deanimate "RatLeBound")
(deanimate "RatLeAbsBound")

(set-totality-goal "cRatLeBound")
(use "AllTotalElim")
(assume "p")
(use "AllTotalElim")
(assume "q")
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save "cRatLeBoundTotal")

;; Every real has an upper bound, that is the reals are Archimedian ordered.

;; Use cNatPos instead of the pconst NatToPos to block unwanted unfoldings

;; NatPos
(set-goal "all n exl p p=NatToPos n")
(assume "n")
(intro 0 (pt "NatToPos n"))
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatPos")

(animate "NatPos")

;; NatPosExFree
(set-goal "all n cNatPos n=NatToPos n")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatPosExFree")

(deanimate "NatPos")

(set-totality-goal "cNatPos")
(use "AllTotalElim")
(assume "n")
(use "PosTotalVar")
;; Proof finished.
;; (cdp)
(save "cNatPosTotal")

(add-program-constant "RealBd" (py "(nat=>rat)=>(pos=>nat)=>nat") t-deg-zero)

;; It might be more uniform to take rea=>nat as type

(add-computation-rules
 "RealBd as M"
 "Succ(ListNatMax(cRatLeAbsBound map as fbar Succ(M 1)))")

(set-totality-goal "RealBd")
(assume "as^" "Tas" "M^" "TM")
(ng #t)
(use "TotalNatSucc")
(use "ListNatMaxTotal")
(use "TotalListCons")
;; 6,7
(use "cRatLeAbsBoundTotal")
(use "Tas")
(use "NatTotalVar")
;; 7
(use "ListMapTotal")
;; 10,11
(use "AllTotalElim")
(assume "a")
(use "NatTotalVar")
(use "ListFBarTotal")
(use "AllTotalElim")
(assume "n")
(use "Tas")
(use "NatTotalVar")
(use "TM")
(use "PosTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

(add-computation-rules
 "(RealConstr as M)*(RealConstr bs N)"
 "RealConstr([n]as n*bs n)
            ([p]M(PosS(p+cNatPos(RealBd bs N)))max
                N(PosS(p+cNatPos(RealBd as M))))")

;; (display-pconst "RealBd")

;; Parallel to RealBoundExFree (commented out below):

;; RealBdProp
(set-goal "all as,M(Cauchy as M -> all n abs(as n)<=2**RealBd as M)")
(assume "as" "M" "CasM" "n")
(ng)
(simp "SZeroPosPlus")
(cases (pt "n<=M 1"))
;; 5,6
(assume "n<=M 1")
(use "RatLeTrans"
     (pt "(2**ListNatMax(([n0]cRatLeAbsBound(as n0))fbar Succ(M 1)))#1"))
;; 8,9
;; ?^8:abs(as n)<=2**ListNatMax(([n0]cRatLeAbsBound(as n0))fbar Succ(M 1))
(use "RatLeTrans" (pt "(2**cRatLeAbsBound(as n))#1"))
;; 10,11
(use "RatLeAbsBoundExFree")
;;   as  M  CasM:Cauchy as M
;;   n  n<=M 1:n<=M 1
;; -----------------------------------------------------------------------------
;; ?^11:RatLe(2**cRatLeAbsBound(as n))
;;      (2**ListNatMax(([n0]cRatLeAbsBound(as n0))fbar Succ(M 1)))
(use "NatLeMonTwoExp")
;;   as  M  CasM:Cauchy as M
;;   n  n<=M 1:n<=M 1
;; -----------------------------------------------------------------------------
;; ?^12:cRatLeAbsBound(as n)<=
;;      ListNatMax
;;      (cRatLeAbsBound(as Zero)::([n0]cRatLeAbsBound(as(Succ n0)))fbar M 1)
(simp (pf "(cRatLeAbsBound(as Zero)::([n0]cRatLeAbsBound(as(Succ n0)))fbar M 1)
           eqd(([n0]cRatLeAbsBound(as n0))fbar Succ(M 1)) "))
(use-with "ListNatMaxFBar"
	  (pt "[n0]cRatLeAbsBound(as n0)") (pt "n") (pt "Succ(M 1)") "?")
(use "NatLeToLtSucc")
(use "n<=M 1")
(use "InitEqD")
;; 9
(simp (pf "(cRatLeAbsBound(as Zero)::([n0]cRatLeAbsBound(as(Succ n0)))fbar M 1)
           eqd(([n0]cRatLeAbsBound(as n0))fbar Succ(M 1)) "))
(use "Truth")
(use "InitEqD")
;; 6
(assume "n<=M 1 -> F")
(simp (pf "(cRatLeAbsBound(as Zero)::([n0]cRatLeAbsBound(as(Succ n0)))fbar M 1)
           eqd(([n0]cRatLeAbsBound(as n0))fbar Succ(M 1)) "))
(use "RatLeTrans" (pt "abs(as(M 1))+(abs(as n)+ ~(abs(as(M 1))))"))
(assert "all b,c b<=c+(b+ ~c)")
 (assume "b" "c")
 (simp "RatPlusComm")
 (simp "<-" "RatPlusAssoc")
 (simprat (pf "~c+c==0"))
 (use "Truth")
 (use "Truth") 
(assume "Assertion")
(use "Assertion")
(use "RatLeTrans"
     (pt "((2**ListNatMax(([n0]cRatLeAbsBound(as n0))fbar Succ(M 1)))#1)+
          (1#2**1)"))
(use "RatLeMonPlus")
;; 34,35
;; ?^34:abs(as(M 1))<=2**ListNatMax(([n]cRatLeAbsBound(as n))fbar Succ(M 1))
(use "RatLeTrans" (pt "(2**cRatLeAbsBound(as(M 1)))#1"))
(use "RatLeAbsBoundExFree")
(use "NatLeMonTwoExp")
(simp (pf "(cRatLeAbsBound(as Zero)::([n0]cRatLeAbsBound(as(Succ n0)))fbar M 1)
           eqd(([n0]cRatLeAbsBound(as n0))fbar Succ(M 1)) "))
(use-with "ListNatMaxFBar"
	  (pt "[n0]cRatLeAbsBound(as n0)") (pt "M 1") (pt "Succ(M 1)") "?")
(use "Truth")
(use "InitEqD")
;; ?^35:abs(as n)+ ~abs(as(M 1))<=(1#2**1)
(use "RatLeTrans" (pt "abs(abs(as n)+ ~abs(as(M 1)))"))
(use "Truth")
(use "RatLeTrans" (pt "abs(as n+ ~(as(M 1)))"))
(use "RatLeAbsMinusAbs")
;; ?^45:abs(as n+ ~(as(M 1)))<=(1#2**1)
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "NatNotLtToLe")
(assume "n<M 1")
(use "n<=M 1 -> F")
(use "NatLtToLe")
(use "n<M 1")
(use "Truth")
;; ?^33:2**ListNatMax(([n]cRatLeAbsBound(as n))fbar Succ(M 1))+(1#2**1)<=
;;      2**ListNatMax(([n]cRatLeAbsBound(as n))fbar Succ(M 1))+
;;      2**ListNatMax(([n]cRatLeAbsBound(as n))fbar Succ(M 1))
(use "Truth")
;; 21
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "RealBdProp")

;; RealBdPos
(set-goal "all as,M Zero<RealBd as M")
(assume "as" "M")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealBdPos")

;; RealTimesTotal
(set-totality-goal "RealTimes")
(assume "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(assume "y^" "Ty")
(elim "Ty")
(assume "bs^" "Tbs" "N^" "TN")
(ng #t)
(intro 0)
(use "AllTotalElim")
(assume "n")
(use "RatTimesTotal")
(use "Tas")
(use "NatTotalVar")
(use "Tbs")
(use "NatTotalVar")
(use "AllTotalElim")
(assume "p")
(use "NatMaxTotal")
(use "TM")
(use "PosSTotal")
(use "PosPlusTotal")
(use "PosTotalVar")
(use "cNatPosTotal")
(use "TotalNatSucc")
(use "ListNatMaxTotal")
(use "TotalListCons")
(use "cRatLeAbsBoundTotal")
(use "Tbs")
(use "NatTotalVar")
(use "ListMapTotal")
(use "AllTotalElim")
(assume "a")
(use "NatTotalVar")
(use "ListFBarTotal")
(use "AllTotalElim")
(assume "n")
(use "Tbs")
(use "NatTotalVar")
(use "TN")
(use "PosTotalVar")
;; 20
(use "TN")
(use "PosSTotal")
(use "PosPlusTotal")
(use "PosTotalVar")
(use "cNatPosTotal")
(use "TotalNatSucc")
(use "ListNatMaxTotal")
(use "TotalListCons")
(use "cRatLeAbsBoundTotal")
(use "Tas")
(use "NatTotalVar")
(use "ListMapTotal")
(use "AllTotalElim")
(assume "a")
(use "cRatLeAbsBoundTotal")
(use "RatTotalVar")
(use "ListFBarTotal")
(use "AllTotalElim")
(assume "n")
(use "Tas")
(use "NatTotalVar")
(use "TM")
(use "PosTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for RealExp : rea=>int=>rea

(add-computation-rules
 "x**(IntP One)" "x"
 "x**(IntP(SZero p))" "(x**(IntP p))*(x**(IntP p))"
 "x**(IntP(SOne p))" "(x**(IntP(SZero p)))*x"
 "x**IntZero" "RealConstr([n](RatConstr(IntPos One)One))([p]Zero)"
 "x**(IntN p)" "(x seq Zero)**(IntN p)")

;; Notice that RealExp is not generally compatible with real equality,
;; becausein the IntN case we refer to the first element of the Cauchy
;; sequence.

;; The totality proof can only proved here, sence we need RealTimesTotal.

(set-totality-goal "RealExp")
(use "AllTotalElim")
(assume "x")
(use "AllTotalElim")
(cases)
;; 5-7
(ind)
;; 8-10
(use "ReaTotalVar")
;; 9
(assume "p" "IH")
(ng)
(use "RealTimesTotal")
(use "IH")
(use "IH")
;; 10
(assume "p" "IH")
(ng)
(use "RealTimesTotal")
(use "RealTimesTotal")
(use "IH")
(use "IH")
(use "ReaTotalVar")
;; 6
(ng)
(use "ReaTotalVar")
;; 7
(ng)
(assume "p")
(intro 0)
(use "AllTotalElim")
(assume "n")
(use "RatTotalVar")
(use "AllTotalElim")
(assume "p1")
(use "NatTotalVar")
;; Proof finished.
(save-totality)

;; 5.  Equality and order
;; ======================

;; We introduce an inductively defined predicate RealEq x y

(add-ids
 (list (list "RealEq" (make-arity (py "rea") (py "rea"))))
 '("all x,y(Real x -> Real y ->
    all p abs(x seq(x mod(PosS p))+ ~(y seq(y mod(PosS p))))<=(1#2**p) ->
    RealEq x y)" "RealEqIntro"))

;; Notice that we cannot take = and use overloading, because the token
;; = has token type rel-op and hence produces a term, not a predicate.

;; predicate creator

(define (make-predicate-creator token min-type-string)
  (lambda (x y)
    (let* ((type1 (term-to-type x))
	   (type2 (term-to-type y))
	   (min-type (py min-type-string))
	   (type (types-lub type1 type2 min-type))
	   (internal-name (token-and-types-to-name token (list type))))
      (make-predicate-formula (make-idpredconst internal-name '() '()) x y))))

(add-token "===" 'pred-infix (make-predicate-creator "===" "rea"))

(add-token-and-type-to-name "===" (py "rea") "RealEq")

(add-idpredconst-display "RealEq" 'pred-infix "===")

;; We introduce an inductively defined predicate RealEqS x y
;; expressing extensional equality of the Cauchy sequences.

(add-ids
 (list (list "RealEqS" (make-arity (py "rea") (py "rea"))))
 '("all x,y(all n x seq n==y seq n -> RealEqS x y)" "RealEqSIntro"))

(add-token "=+=" 'pred-infix (make-predicate-creator "=+=" "rea"))

(add-token-and-type-to-name "=+=" (py "rea") "RealEqS")

(add-idpredconst-display "RealEqS" 'pred-infix "=+=")

;; Non-negative reals are defined inductively

(add-ids
 (list (list "RealNNeg" (make-arity (py "rea"))))
 '("all x(Real x -> all p 0<=x seq(x mod p)+(1#2**p) -> RealNNeg x)"
 "RealNNegIntro"))

;; We introduce an inductively defined predicate RealNNegS x
;; expressing the pointwise NNeg-property of the Cauchy sequence.

(add-ids
 (list (list "RealNNegS" (make-arity (py "rea"))))
 '("all x(all n 0<=x seq n -> RealNNegS x)" "RealNNegSIntro"))

;; For reals less-than-or-equal-to is undecidable and hence must be
;; treated as an inductively defined predicate.

(add-ids
 (list (list "RealLe" (make-arity (py "rea") (py "rea"))))
 '("all x,y(Real x -> Real y -> RealNNeg(y+ ~x) -> RealLe x y)" "RealLeIntro"))

;; Notice that we cannot take <= and use overloading, because the token
;; <= has token type rel-op and hence produces a term, not a predicate.

(add-token
 "<<="
 'pred-infix
 (lambda (x y)
   (make-predicate-formula (make-idpredconst "RealLe" '() '()) x y)))

(add-idpredconst-display "RealLe" 'pred-infix "<<=")

(add-ids
 (list (list "RealLeS" (make-arity (py "rea") (py "rea"))))
 '("all x,y(RealNNegS(y+ ~x) -> RealLeS x y)" "RealLeSIntro"))

(add-token "<+=" 'pred-infix (make-predicate-creator "<+=" "rea"))

(add-token-and-type-to-name "<+=" (py "rea") "RealLeS")

(add-idpredconst-display "RealLeS" 'pred-infix "<+=")

;; Properties of RealEq, RealEqS, RealNNeg and RealLe

;; RealEqElim0
(set-goal "all x,y(x===y -> Real x)")
(assume "x" "y" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqElim0")

;; RealEqElim1
(set-goal "all x,y(x===y -> Real y)")
(assume "x" "y" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqElim1")

;; RealEqElim2
(set-goal
 "all x,y(x===y ->
          all p abs(x seq(x mod(PosS p))+ ~(y seq(y mod(PosS p))))<=(1#2**p))")
(assume "x" "y" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqElim2")

;; The following variants will be useful, because their heads will be
;; more often of the form of a given goal.

;; RealConstrEqElim0
(set-goal
 "all as,M,bs,N(RealConstr as M===RealConstr bs N -> Real(RealConstr as M))")
(assume "as" "M" "bs" "N" "EqHyp")
(use "RealEqElim0" (pt "RealConstr bs N"))
(use "EqHyp")
;; Proof finished.
(save "RealConstrEqElim0")

;; RealConstrEqElim1
(set-goal
 "all as,M,bs,N(RealConstr as M===RealConstr bs N -> Real(RealConstr bs N))")
(assume "as" "M" "bs" "N" "EqHyp")
(use "RealEqElim1" (pt "RealConstr as M"))
(use "EqHyp")
;; Proof finished.
(save "RealConstrEqElim1")

;; RealConstrEqElim2
(set-goal
 "all as,M,bs,N(RealConstr as M===RealConstr bs N ->
                all p abs(as(M(PosS p))+ ~(bs(N(PosS p))))<=(1#2**p))")
(assume "as" "M" "bs" "N" "EqHyp" "p")
(use-with "RealEqElim2"
	  (pt "RealConstr as M") (pt "RealConstr bs N") "EqHyp" (pt "p"))
;; Proof finished.
(save "RealConstrEqElim2")

;; RealEqSElim
(set-goal "all x,y(x=+=y -> all n x seq n==y seq n)")
(assume "x" "y" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqSElim")

;; RealConstrEqSElim
(set-goal
 "all as,M,bs,N(RealConstr as M=+=RealConstr bs N -> all n as n==bs n)")
(assume "as" "M" "bs" "N" "EqSHyp" "n")
(use-with "RealEqSElim"
	  (pt "RealConstr as M") (pt "RealConstr bs N") "EqSHyp" (pt "n"))
;; Proof finished.
(save "RealConstrEqSElim")

;; TotalReaToEqD
(set-goal "allnc x^(TotalReaNc x^ -> x^ eqd RealConstr x^ seq x^ mod)")
(assume "x^")
(elim)
(ng)
(strip)
(use "InitEqD")
;; Proof finished.
(save "TotalReaToEqD")

;; RealNNegElim0
(set-goal "all x(RealNNeg x -> Real x)")
(assume "x" "NNegx")
(elim "NNegx")
(search)
;; Proof finished.
(save "RealNNegElim0")

;; RealNNegElim1
(set-goal "all x(RealNNeg x -> all p 0<=x seq(x mod p)+(1#2**p))")
(assume "x" "NNegx")
(elim "NNegx")
(search)
;; Proof finished.
(save "RealNNegElim1")

;; The following variants will be useful, because their heads will be
;; more often of the form of a given goal.

;; RealConstrNNegElim0
(set-goal
 "all as,M(RealNNeg(RealConstr as M) -> Real(RealConstr as M))")
(assume "as" "M" "NNegHyp")
(use "RealNNegElim0")
(use "NNegHyp")
;; Proof finished.
(save "RealConstrNNegElim0")

;; RealConstrNNegElim1
(set-goal
 "all as,M(RealNNeg(RealConstr as M) -> all p 0<=as(M p)+(1#2**p))")
(assume "as" "M" "NNegHyp" "p")
(use-with "RealNNegElim1" (pt "RealConstr as M") "NNegHyp" (pt "p"))
;; Proof finished.
(save "RealConstrNNegElim1")

;; RealLeElim0
(set-goal "all x,y(x<<=y -> Real x)")
(assume "x" "y" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
(save "RealLeElim0")

;; RealLeElim1
(set-goal "all x,y(x<<=y -> Real y)")
(assume "x" "y" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
(save "RealLeElim1")

;; RealLeElim2
(set-goal "all x,y(x<<=y -> RealNNeg(y+ ~x))")
(assume "x" "y" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
(save "RealLeElim2")

;; The following variants will be useful, because their heads will be
;; more often of the form of a given goal.

;; RealConstrLeElim0
(set-goal
 "all as,M,bs,N(RealConstr as M<<=RealConstr bs N -> Real(RealConstr as M))")
(assume "as" "M" "bs" "N" "LeHyp")
(use "RealLeElim0" (pt "RealConstr bs N"))
(use "LeHyp")
;; Proof finished.
(save "RealConstrLeElim0")

;; RealConstrLeElim1
(set-goal
 "all as,M,bs,N(RealConstr as M<<=RealConstr bs N -> Real(RealConstr bs N))")
(assume "as" "M" "bs" "N" "LeHyp")
(use "RealLeElim1" (pt "RealConstr as M"))
(use "LeHyp")
;; Proof finished.
(save "RealConstrLeElim1")

;; RealConstrLeElim2
(set-goal "all as,M,bs,N(
 RealConstr as M <<=RealConstr bs N ->
 RealNNeg(RealConstr([n]bs n+ ~(as n))([p]N(PosS p)max M(PosS p))))")
(assume "as" "M" "bs" "N" "LeHyp")
(use-with "RealLeElim2" (pt "RealConstr as M") (pt "RealConstr bs N") "LeHyp")
;; Proof finished.
(save "RealConstrLeElim2")

;; RealLeSElim
(set-goal "all x,y(x<+=y -> RealNNegS(y+ ~x))")
(assume "x" "y" "LeSxy")
(elim "LeSxy")
(search)
;; Proof finished.
(save "RealLeSElim")

;; We now prove further properties of RealEq, RealEqS, RealNNeg, RealLe

;; EfRealEq
(set-goal "F -> all x,y x===y")
(assume "Absurd" "x" "y")
(intro 0)
(use "EfReal")
(use "Absurd")
(use "EfReal")
(use "Absurd")
(ng)
(strip)
(use "EfAtom")
(use "Absurd")
;; Proof finished.
(save "EfRealEq")

;; EfRealEq$
(set-goal "F -> all x,y x=+=y")
(assume "Absurd" "x" "y")
(intro 0)
(assume "n")
(use "EfAtom")
(use "Absurd")
;; Proof finished.
(save "EfRealEqS")

;; EfRealNNeg
(set-goal "F -> all x RealNNeg x")
(assume "Absurd" "x")
(intro 0)
(use "EfReal")
(use "Absurd")
(assume "p")
(use "EfAtom")
(use "Absurd")
;; Proof finished.
(save "EfRealNNeg")

;; EfRealLe
(set-goal "F -> all x,y x<<=y")
(assume "Absurd" "x" "y")
(intro 0)
(use "EfReal")
(use "Absurd")
(use "EfReal")
(use "Absurd")
(use "EfRealNNeg")
(use "Absurd")
;; Proof finished.
(save "EfRealLe")

;; RealEqRefl
(set-goal "all x(Real x -> x===x)")
(cases)
(assume "as" "M" "Rx")
(use "RealEqIntro")
(use "Rx")
(use "Rx")
(assume "p")
(ng)
(simprat (pf "as(M(PosS p))+ ~(as(M(PosS p)))==0"))
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealEqRefl")

;; RealEqSym
(set-goal "all x,y(x===y -> y===x)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x=y")
(elim "x=y")
(cases)
(assume "as1" "M1")
(cases)
(assume "bs1" "N1" "Rx1" "Ry1" "LeHyp")
(intro 0)
(use "Ry1")
(use "Rx1")
(assume "p")
(ng)
(simp "<-" "RatAbs0RewRule")
(ng)
(simp "RatPlusComm")
(use "LeHyp")
;; Proof finished.
(save "RealEqSym")

;; To prove transitivity of equality, we need a characterization of
;; equality.

(set-goal "allnc as,bs all M,N(RealConstr as M===RealConstr bs N -> 
      all p exl n1 all n(n1<=n -> abs(as n+ ~(bs n))<=(1#2**p)))")
(assume "as" "bs" "M" "N" "x=y" "p")
(intro 0 (pt "M(PosS(PosS p))max N(PosS(PosS p))"))
(assume "n" "BdHyp")
(use "RatLeTrans"
     (pt "(1#2**(PosS(PosS p)))+(1#2**(PosS p))+(1#2**(PosS(PosS p)))"))
(use "RatLeTrans" (pt "abs(as n+ ~(as(M(PosS(PosS p)))))+
                       abs(as(M(PosS(PosS p)))+ ~(bs(N(PosS(PosS p)))))+
                       abs(bs(N(PosS(PosS p)))+ ~(bs n))"))
(assert "all a,b,c,c1 abs(a+ ~b)<=abs(a+ ~c)+abs(c+ ~c1)+abs(c1+ ~b)")
 (assume "a" "b" "c" "c1")
 (use "RatLeTrans" (pt "abs(a+ ~c1)+abs(c1+ ~b)"))
 (use "RatLeAbsMinus")
 (use "RatLeMonPlus")
 (use "RatLeAbsMinus")
 (use "Truth")
;; Assertion proved
(assume "RatLeAbsMinus3")
(use "RatLeAbsMinus3")
(assert
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")
 (assume "a1" "a2" "b1" "b2" "c1" "c2" "a1<=a2" "b1<=b2" "c1<=c2")
 (use "RatLeMonPlus")
 (use "RatLeMonPlus")
 (use "a1<=a2")
 (use "b1<=b2")
 (use "c1<=c2")
;; Assertion proved
(assume "RatLeMonPlus3")
(use "RatLeMonPlus3")
;; 25-27
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "RealConstrEqElim0" (pt "bs") (pt "N"))
(use "x=y")
(use "NatLeTrans" (pt "(M(PosS(PosS p)))max(N(PosS(PosS p)))"))
(use "NatMaxUB1")
(use "BdHyp")
(use "Truth")
;; 26
(use "RealConstrEqElim2")
(use "x=y")
;; 27
(use "CauchyElim" (pt "N"))
(use "RealConstrToCauchy")
(use "RealConstrEqElim0" (pt "as") (pt "M"))
(use "RealEqSym")
(use "x=y")
(use "Truth")
(use "NatLeTrans" (pt "(M(PosS(PosS p)))max(N(PosS(PosS p)))"))
(use "NatMaxUB2")
(use "BdHyp")
;; 6: (1#2**PosS(PosS p))+(1#2**PosS p)+(1#2**PosS(PosS p))<=(1#2**p)
;; Use RatPlusHalfExpPosS :
;; all p (1#2**PosS p)+(1#2**PosS p)==(1#2**p)
(assert "(1#2**PosS(PosS p))+(1#2**PosS p)=(1#2**PosS p)+(1#2**PosS(PosS p))")
 (use "RatPlusComm")
(assume "Assertion")
(simp "Assertion")
(drop "Assertion")
(simp "<-" "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(simprat "RatPlusHalfExpPosS")
(use "Truth")
;; Proof finished.
(save "RealEqCharOne")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [M,M0,p]M(PosS(PosS p))max M0(PosS(PosS p))

(animate "RealEqCharOne")

;; RealEqCharOneRealConstrFree
(set-goal "all x,y(x===y ->
  all p exl n1 all n(n1<=n -> abs(x seq n+ ~(y seq n))<=(1#2**p)))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealEqCharOne")
;; Proof finished.
(save "RealEqCharOneRealConstrFree")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [x,x0,p][case x (RealConstr as M ->
;;         [case x0 (RealConstr as0 M0 -> cRealEqCharOne M M0 p)])]

;; RealEqCharOneExFree
(set-goal "all as,bs,M,N(RealConstr as M===RealConstr bs N -> 
      all p,n(cRealEqCharOne M N p<=n -> abs(as n-bs n)<=(1#2**p)))")
(assume "as" "bs" "M" "N" "x=y" "p")
(ng)
(assume "n" "BdHyp")
(use "RatLeTrans"
     (pt "(1#2**(PosS(PosS p)))+(1#2**(PosS p))+(1#2**(PosS(PosS p)))"))
(use "RatLeTrans" (pt "abs(as n+ ~(as(M(PosS(PosS p)))))+
                       abs(as(M(PosS(PosS p)))+ ~(bs(N(PosS(PosS p)))))+
                       abs(bs(N(PosS(PosS p)))+ ~(bs n))"))
(assert "all a,b,c,d abs(a+ ~b)<=abs(a+ ~c)+abs(c+ ~d)+abs(d+ ~b)")
 (assume "a" "b" "c" "d")
 (use "RatLeTrans" (pt "abs(a+ ~d)+abs(d+ ~b)"))
 (use "RatLeAbsMinus")
 (use "RatLeMonPlus")
 (use "RatLeAbsMinus")
 (use "Truth")
;; Assertion proved
(assume "RatLeAbsMinus3")
(use "RatLeAbsMinus3")
(assert
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")
 (assume "a1" "a2" "b1" "b2" "c1" "c2" "a1<=a2" "b1<=b2" "c1<=c2")
 (use "RatLeMonPlus")
 (use "RatLeMonPlus")
 (use "a1<=a2")
 (use "b1<=b2")
 (use "c1<=c2")
;; Assertion proved
(assume "RatLeMonPlus3")
(use "RatLeMonPlus3")
;; 26-28
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "RealConstrEqElim0" (pt "bs") (pt "N"))
(use "x=y")
(use "NatLeTrans" (pt "(M(PosS(PosS p)))max(N(PosS(PosS p)))"))
(use "NatMaxUB1")
(use "BdHyp")
(use "Truth")
;; 27
(use "RealConstrEqElim2")
(use "x=y")
;; 28
(use "CauchyElim" (pt "N"))
(use "RealConstrToCauchy")
(use "RealConstrEqElim0" (pt "as") (pt "M"))
(use "RealEqSym")
(use "x=y")
(use "Truth")
(use "NatLeTrans" (pt "(M(PosS(PosS p)))max(N(PosS(PosS p)))"))
(use "NatMaxUB2")
(use "BdHyp")
;; 7: (1#2**PosS(PosS p))+(1#2**PosS p)+(1#2**PosS(PosS p))<=(1#2**p)
;; Use RatPlusHalfExpPosS :
;; all p (1#2**PosS p)+(1#2**PosS p)==(1#2**p)
(assert "(1#2**PosS(PosS p))+(1#2**PosS p)=(1#2**PosS p)+(1#2**PosS(PosS p))")
 (use "RatPlusComm")
(assume "Assertion")
(simp "Assertion")
(drop "Assertion")
(simp "<-" "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(simprat "RatPlusHalfExpPosS")
(use "Truth")
;; Proof finished.
(save "RealEqCharOneExFree")

(deanimate "RealEqCharOne")

;; RealEqChar2
(set-goal "all as,M,bs,N(Real(RealConstr as M) -> Real(RealConstr bs N) ->
           all p exnc n0 all n(n0<=n -> abs(as n+ ~(bs n))<=(1#2**p)) ->
           RealConstr as M===RealConstr bs N)")
(assume "as" "M" "bs" "N" "Rx" "Ry" "Est")
(use "RealEqIntro")
(use "Rx")
(use "Ry")
(ng #t)
(assume "p")
(use "RatLeAllPlusToLe")
(assume "q")
;; abs(as(M(PosS p))+ ~(bs(N(PosS p))))<=(1#2**p)+(1#2**q)
(inst-with-to "Est" (pt "q") "InstEst")
(drop "Est")
(by-assume "InstEst" "n0" "n0Prop")
;; We now want to use n as an abbreviation for the complex term
;; ((M(PosS p))max(N(PosS p)))max n0.  Hence we introduce via cut the
;; formula all n(n=term -> goal)
(cut "all n(n=((M(PosS p))max(N(PosS p)))max n0 ->
             abs(as(M(PosS p))+ ~(bs(N(PosS p))))<=(1#2**p)+(1#2**q))")
(assume "AllHyp")
(use "AllHyp" (pt "((M(PosS p))max(N(PosS p)))max n0"))
(use "Truth")
(assume "n" "nDef")
(use "RatLeTrans"
     (pt "abs(as(M(PosS p))+ ~(as n))+
          abs(as n+ ~(bs n))+
          abs(bs n+ ~(bs(N(PosS p))))"))
(assert "all a,b,c,c1 abs(a+ ~b)<=abs(a+ ~c)+abs(c+ ~c1)+abs(c1+ ~b)")
 (assume "a" "b" "c" "c1")
 (use "RatLeTrans" (pt "abs(a+ ~c1)+abs(c1+ ~b)"))
 (use "RatLeAbsMinus")
 (use "RatLeMonPlus")
 (use "RatLeAbsMinus")
 (use "Truth")
;; Assertion proved
(assume "RatLeAbsMinus3")
(use "RatLeAbsMinus3")
(use "RatLeTrans" (pt "(1#2**(PosS p))+(1#2**q)+(1#2**(PosS p))"))
(assert
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")
 (assume "a1" "a2" "b1" "b2" "c1" "c2" "a1<=a2" "b1<=b2" "c1<=c2")
 (use "RatLeMonPlus")
 (use "RatLeMonPlus")
 (use "a1<=a2")
 (use "b1<=b2")
 (use "c1<=c2")
;; Assertion proved
(assume "RatLeMonPlus3")
(use "RatLeMonPlus3")
;; 41-43
(drop "RatLeMonPlus3")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "Truth")
(simp "nDef")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS p)"))
(use "NatMaxUB1")
(use "NatMaxUB1")
;; 42
(use "n0Prop")
(simp "nDef")
(use "NatMaxUB2")
;; 43
(use "CauchyElim" (pt "N"))
(use "RealConstrToCauchy")
(use "Ry")
(simp "nDef")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS p)"))
(use "NatMaxUB2")
(use "NatMaxUB1")
(use "Truth")
;; 32 (1#2**PosS p)+(1#2**q)+(1#2**PosS p)<=(1#2**p)+(1#2**q)
;; Use RatPlusHalfExpPosS :
;; all p (1#2**PosS p)+(1#2**PosS p)==(1#2**p)
(simprat (pf "(1#2**PosS p)+(1#2**q)==(1#2**q)+(1#2**PosS p)"))
(simp "<-" "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(simp "RatPlusComm")
(use "Truth")
(simp "RatPlusComm")
(use "Truth")
;; Proof finished.
(save "RealEqChar2")

;; RealEqChar2RealConstrFree
(set-goal "all x,y(Real x -> Real y -> 
 all p exnc n0 all n(n0<=n -> abs(x seq n+ ~(y seq n))<=(1#2**p)) -> x===y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealEqChar2")
;; Proof finished.
(save "RealEqChar2RealConstrFree")

;; An immediate consequence of RealEqChar2 is that any two reals with the
;; same Cauchy sequence (but possibly different moduli) are equal.

;; RealSeqEqToEq
(set-goal "all x,y,n1(Real x -> Real y ->
 all n(n1<=n -> x seq n==y seq n) -> x===y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "n1" "Rx" "Ry" "SeqEqHyp")
(ng)
(use "RealEqChar2")
(use "Rx")
(use "Ry")
(assume "p")
(intro 0 (pt "n1"))
(assume "n" "n1<=n")
(simprat "SeqEqHyp")
(ng)
(simprat (pf "bs n+ ~(bs n)==0"))
(use "Truth")
(use "Truth")
(use "n1<=n")
;; Proof finished.
(save "RealSeqEqToEq")

;; RealEqSToEq
(set-goal "all x,y(Real x -> Real y -> x=+=y -> x===y)")
(assume "x" "y" "Rx" "Ry" "x=+=y")
(use "RealSeqEqToEq" (pt "Zero"))
(use "Rx")
(use "Ry")
(assume "n" "Useless")
(use "RealEqSElim")
(use "x=+=y")
;; Proof finished.
(save "RealEqSToEq")

;; Recall that two reals are equal if their Cauchy sequences coincide
;; from one point onwards.  We may increase moduli in Cauchy sequences
;; and in reals.

;; CauchyModIncr
(set-goal "all M,N,as(all p M p<=N p -> Cauchy as M -> Cauchy as N)")
(assume "M" "N" "as" "M<=N" "CasM")
(intro 0)
(assume "p" "n" "m" "NnBd" "NmBd")
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "NatLeTrans" (pt "N p"))
(use "M<=N")
(use "NnBd")
(use "NatLeTrans" (pt "N p"))
(use "M<=N")
(use "NmBd")
;; Proof finished.
(save "CauchyModIncr")

;; RealModIncr
(set-goal "all as,M,N(Real(RealConstr as M) ->
 all p M p<=N p -> Mon N -> RealConstr as M===RealConstr as N)")
(assume "as" "M" "N" "Rx" "ModIncr" "MonN")
(assert "Real(RealConstr as N)")
(use "RealIntro")
(ng)
(use "CauchyModIncr" (pt "M"))
(use "ModIncr")
(inst-with-to "RealToCauchy" (pt "RealConstr as M") "Rx" "RealToCauchyInst")
(ng)
(use "RealToCauchyInst")
(ng)
(use "MonN")
;; Assertion proved.
(assume "Rx1")
(use "RealSeqEqToEq" (pt "Zero"))
(use "Rx")
(use "Rx1")
(ng)
(strip)
(use "Truth")
;; Proof finished.
(save "RealModIncr")

;; RealEqTrans
(set-goal "all x,y,z(x===y -> y===z -> x===z)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "L" "x=y" "y=z")
(use "RealEqChar2")
(use "RealConstrEqElim0" (pt "bs") (pt "N"))
(use "x=y")
(use "RealConstrEqElim0" (pt "bs") (pt "N"))
(use "RealEqSym")
(use "y=z")
(assume "p")
;; Use RealEqCharOne for x=y
(assert "exl n all n0(n<=n0 -> abs(as n0-bs n0)<=(1#2**(PosS p)))")
 (use "RealEqCharOne" (pt "M") (pt "N"))
 (use "x=y")
(assume "xyExHyp")
(by-assume "xyExHyp" "m" "mProp")
;; Use RealEqCharOne for y=z
(assert "exl n all n0(n<=n0 -> abs(bs n0-cs n0)<=(1#2**(PosS p)))")
 (use "RealEqCharOne" (pt "N") (pt "L"))
 (use "y=z")
(assume "yzExHyp")
(by-assume "yzExHyp" "l" "lProp")
;; Take m max l for n
(intro 0 (pt "m max l"))
(assume "n" "BdHyp")
(use "RatLeTrans" (pt "abs(as n-bs n)+abs(bs n-cs n)"))
(use "Truth")
(simprat "<-" "RatPlusHalfExpPosS")
(use "RatLeMonPlus")
(use "mProp")
(use "NatLeTrans" (pt "m max l"))
(use "NatMaxUB1")
(use "BdHyp")
(use "lProp")
(use "NatLeTrans" (pt "m max l"))
(use "NatMaxUB2")
(use "BdHyp")
;; Proof finished.
(save "RealEqTrans")

;; RealNNegCharOne
(set-goal "allnc as all M(RealNNeg(RealConstr as M) -> 
      all p exl n1 all n(n1<=n -> ~(1#2**p)<=as n))")
(assume "as" "M" "0<=x" "p")
(intro 0 (pt "M(PosS p)"))
(assume "n" "BdHyp")
(use "RatLeTrans" (pt "~(1#2**(PosS p))+(as(M(PosS p))+ ~(as n))+as n"))
;; 5,6
(use "RatLeTrans" (pt "~(1#2**(PosS p))+as(M(PosS p))"))
(use "RatLePlusR")
(assert "(1#2**p)==(1#2**PosS p)+(1#2**PosS p)")
 (use "RatEqvSym")
 (use "RatPlusHalfExpPosS")
(assume "RatPlusHalfExpPosSCor")
(simprat "RatPlusHalfExpPosSCor")
(drop "RatPlusHalfExpPosSCor")
(simp "RatUMinus1RewRule")
(simp "RatUMinus2RewRule")
(simp "RatPlusAssoc")
(use "RatLeTrans" (pt "0+ ~(1#2**PosS p)"))
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "RatLeTrans" (pt "as(M(PosS p))+(1#2**PosS p)+ ~(1#2**PosS p)"))
(use "RatLeMonPlus")
(use "RealConstrNNegElim1")
(use "0<=x")
(use "Truth")
(simprat "RatEqvPlusMinusRev")
(use "RatLeRefl")
(use "Truth")
;; 8
(simp "<-" "RatPlusAssoc")
(use "RatLeMonPlus")
(ng)
(use "Truth")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; 6
;; The following argument is repeated in the proof of RealPosCharOne below
(assert
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")
 (assume "a1" "a2" "b1" "b2" "c1" "c2" "a1<=a2" "b1<=b2" "c1<=c2")
 (use "RatLeMonPlus")
 (use "RatLeMonPlus")
 (use "a1<=a2")
 (use "b1<=b2")
 (use "c1<=c2")
;; Assertion proved
(assume "RatLeMonPlus3")
(use "RatLeTrans" (pt "~(1#2**PosS p)+(1#2**PosS p)+as n"))
(use "RatLeMonPlus3")
(drop "RatLeMonPlus3")
(use "Truth")
(use "RatLeTrans" (pt "abs(as(M(PosS p))+ ~(as n))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "RealNNegElim0")
(use "0<=x")
(use "Truth")
(use "BdHyp")
(use "Truth")
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; Proof finished.
(save "RealNNegCharOne")

(pp (rename-variables
     (nt (proof-to-extracted-term (theorem-name-to-proof "RealNNegCharOne")))))
;; [M,p]M(PosS p)

(animate "RealNNegCharOne")

;; RealNNegCharOneRealConstrFree
(set-goal
 "all x(RealNNeg x -> all p exl n all n0(n<=n0 -> ~(1#2**p)<=x seq n0))")
(cases)
(assume "as" "M" "NNegx")
(ng)
(assume "p")
(simp (pf "(IntN 1#2**p)= ~(1#2**p)"))
(use "RealNNegCharOne" (pt "M"))
(use "NNegx")
(ng)
(use "Truth")
;; Proof finished.
(save "RealNNegCharOneRealConstrFree")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)
;; [x,p][case x (RealConstr as M -> cRealNNegCharOne M p)]

;; RealNNegCharOneExFree
(set-goal "all as,M(RealNNeg(RealConstr as M) -> 
      all p,n(cRealNNegCharOne M p<=n -> ~(1#2**p)<=as n))")
(assume "as" "M" "0<=x" "p" "n" "BdHyp")
(use "RatLeTrans" (pt "~(1#2**(PosS p))+(as(M(PosS p))+ ~(as n))+as n"))
;; 3,4
(use "RatLeTrans" (pt "~(1#2**(PosS p))+as(M(PosS p))"))
(use "RatLePlusR")
(assert "(1#2**p)==(1#2**PosS p)+(1#2**PosS p)")
 (use "RatEqvSym")
 (use "RatPlusHalfExpPosS")
(assume "RatPlusHalfExpPosSCor")
(simprat "RatPlusHalfExpPosSCor")
(drop "RatPlusHalfExpPosSCor")
(simp "RatUMinus1RewRule")
(simp "RatUMinus2RewRule")
(simp "RatPlusAssoc")
(use "RatLeTrans" (pt "0+ ~(1#2**PosS p)"))
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "RatLeTrans" (pt "as(M(PosS p))+(1#2**PosS p)+ ~(1#2**PosS p)"))
(use "RatLeMonPlus")
(use "RealConstrNNegElim1")
(use "0<=x")
(use "Truth")
(simprat "RatEqvPlusMinusRev")
(use "RatLeRefl")
(use "Truth")
;; 6
(simp "<-" "RatPlusAssoc")
(use "RatLeMonPlus")
(ng)
(use "Truth")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; 4
;; The following argument is repeated in the proof of RealPosCharOne below
(assert
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")
 (assume "a1" "a2" "b1" "b2" "c1" "c2" "a1<=a2" "b1<=b2" "c1<=c2")
 (use "RatLeMonPlus")
 (use "RatLeMonPlus")
 (use "a1<=a2")
 (use "b1<=b2")
 (use "c1<=c2")
;; Assertion proved
(assume "RatLeMonPlus3")
(use "RatLeTrans" (pt "~(1#2**PosS p)+(1#2**PosS p)+as n"))
(use "RatLeMonPlus3")
(drop "RatLeMonPlus3")
(use "Truth")
(use "RatLeTrans" (pt "abs(as(M(PosS p))+ ~(as n))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "RealNNegElim0")
(use "0<=x")
(use "Truth")
(use "BdHyp")
(use "Truth")
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; Proof finished.
(save "RealNNegCharOneExFree")

(deanimate "RealNNegCharOne")

;; RealNNegChar2
(set-goal "all as,M(Real(RealConstr as M) ->
      all p exnc n1 all n(n1<=n -> ~(1#2**p)<=as n) ->
      RealNNeg(RealConstr as M))")
(assume "as" "M" "Rx" "Est")
(use "RealNNegIntro")
(use "Rx")
(ng #t)
(assume "p")
(use "RatLeAllPlusToLe")
(assume "q")
(inst-with-to "Est" (pt "q") "EstInst")
(drop "Est")
(by-assume "EstInst" "n0" "n0Prop")
(inst-with-to "n0Prop" (pt "M(p)max n0") "EstInstInst")
(use "RatLeTrans" (pt "as(M p)+(1#2**p)+ ~(as(M p max n0))"))
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(use "RatLeTrans" (pt "~(1#2**p)+(1#2**p)"))
(use "Truth")
(use "RatLeMonPlus")
(simp "<-" "RatLeUMinus")
(ng #t)
(use "RatLeTrans" (pt "abs(as(M p max n0)+ ~(as(M p)))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "NatMaxUB1")
(use "Truth")
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(simp "<-" "RatLeUMinus")
(use "EstInstInst")
(use "NatMaxUB2")
;; Proof finished.
(save "RealNNegChar2")

;; RealNNegChar2RealConstrFree
(set-goal
 "all x(Real x -> all p exnc n all n0(n<=n0 -> ~(1#2**p)<=(x seq) n0) ->
        RealNNeg(x))")
(cases)
(assume "as" "M" "Rx" "Char")
(use "RealNNegChar2")
(use "Rx")
(use "Char")
;; Proof finished.
(save "RealNNegChar2RealConstrFree")

;; RealNNegSElim
(set-goal "all x(RealNNegS x -> all n 0<=x seq n)")
(assume "x" "NNegSx")
(elim "NNegSx")
(search)
;; Proof finished.
(save "RealNNegSElim")

;; RealNNegSToNNeg
(set-goal "all x(Real x -> RealNNegS x -> RealNNeg x)")
(assume "x" "Rx" "NNegSx")
(use "RealNNegIntro")
(use "Rx")
(assume "p")
(elim "NNegSx")
(assume "x1" "NNegSx1")
(use "RatLeTrans" (pt "x1 seq(x1 mod p)"))
(use "NNegSx1")
(use "RatLeTrans" (pt "x1 seq(x1 mod p)+(0#1)"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealNNegSToNNeg")

;; RealPosChar1
(set-goal "all as,M,p(
 Real(RealConstr as M) -> RealPos(RealConstr as M)p ->
 all n(M(PosS p)<=n -> (1#2**PosS p)<=as n))")
(assume "as" "M" "p" "Rx" "xPos" "n" "BdHyp")
(use "RatLeTrans" (pt "~(1#2**(PosS p))+(as(M(PosS p))+ ~(as n))+as n"))
;; 3,4
(use "RatLePlusR")
(ng)
(simp "RatPlusComm")
(simp "<-" "RatPlusAssoc")
(simp "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(use "RatLeTrans" (pt "as(M(PosS p))+(~(as(M(PosS p)))+as n)"))
(use "RatLeMonPlus")
(use "xPos")
(use "Truth")
(ng)
(simp "RatPlusComm")
(ng)
(simprat "RatEqvPlusMinusRev")
(use "Truth")
;; 4
;; The following is similar to what was done for RealNNegCharOne
(assert
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")
 (assume "a1" "a2" "b1" "b2" "c1" "c2" "a1<=a2" "b1<=b2" "c1<=c2")
 (use "RatLeMonPlus")
 (use "RatLeMonPlus")
 (use "a1<=a2")
 (use "b1<=b2")
 (use "c1<=c2")
;; Assertion proved
(assume "RatLeMonPlus3")
(use "RatLeTrans" (pt "~(1#2**PosS p)+(1#2**PosS p)+as n"))
(use "RatLeMonPlus3")
(drop "RatLeMonPlus3")
(use "Truth")
(use "RatLeTrans" (pt "abs(as(M(PosS p))+ ~(as n))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "Truth")
(use "BdHyp")
(use "Truth")
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; Proof finished.
(save "RealPosChar1")

;; RealPosChar1RealConstrFree
(set-goal "all x,p(Real x -> RealPos x p ->
                   all n(x mod(PosS p)<=n -> (1#2**PosS p)<=x seq n))")
(cases)
(assume "as" "M" "p" "Rx" "x ppos" "n" "Char")
(use "RealPosChar1" (pt "M"))
(ng)
(use "Rx")
(ng)
(use "x ppos")
(use "Char")
;; Proof finished.
(save "RealPosChar1RealConstrFree")

;; RealPosChar2
(set-goal "all as,M,n1,q(Real(RealConstr as M) -> 
                               all n(n1<=n -> (1#2**q)<=as n) ->
                               RealPos(RealConstr as M)(PosS q))")
(assume "as" "M" "n1" "q" "Rx" "Est")
(ng)
(use "RatLeTrans" (pt "~(1#2**(PosS(PosS q)))+(1#2**q)"))
(use "RatLeTrans" (pt "~(1#2**(PosS q))+(1#2**q)"))
(simprat (pf "(1#2**q)==(1#2**PosS q)+(1#2**PosS q)"))
(simp "RatPlusComm")
(simprat "RatEqvPlusMinusRev")
(use "Truth")
(use "RatEqvSym")
(use "RatPlusHalfExpPosS")
(use "RatLeMonPlus")
(simp "RatLeUMinus")
(ng)
(assert "all p 2**p<=2**PosS p")
 (assume "p")
 (simp "PosSSucc")
 (ng)
 (use "Truth")
(assume "Assertion")
(use "Assertion")
(use "Truth")
;; 5
;; We now want to use n as an abbreviation for n1 max M(PosS(PosS q)).
;; Hence we introduce via cut the formula all n(n=term -> goal)
(cut "all n(n=n1 max M(PosS(PosS q)) ->
             ~(1#2**PosS(PosS q))+(1#2**q)<=as(M(PosS(PosS q))))")
(assume "AllHyp")
(use "AllHyp" (pt "n1 max M(PosS(PosS q))"))
(use "Truth")
(assume "n" "nDef")
(use "RatLeTrans" (pt "~(1#2**PosS(PosS q))+as n"))
(use "RatLeMonPlus")
(use "Truth")
(use "Est")
(simp "nDef")
(use "NatMaxUB1")
(use "RatLeTrans" (pt "as(M(PosS(PosS q)))+ ~(as n) +as n"))
(use "RatLeMonPlus")
(simp "<-" "RatLeUMinus")
(ng)
(simp "RatPlusComm")
(use "RatLeTrans" (pt "abs(as n+ ~(as(M(PosS(PosS q)))))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(simp "nDef")
(use "NatMaxUB2")
(use "Truth")
(use "Truth")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; Proof finished.
(save "RealPosChar2")

;; 6.  Closure properties
;; ======================

;; RealPlusReal
(set-goal "all x,y(Real x -> Real y -> Real(RealPlus x y))")
(assume "x" "y" "Rx" "Ry")
(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(elim "Ry")
(cases)
(assume "bs" "N" "CbsN" "MonN")
(use "RealIntro")
(ng)
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
(simp (pf "as n+ bs n+ ~(as m)+ ~(bs m)=as n+ ~(as m)+(bs n+ ~(bs m))"))
;; Could also use == here.
;; 15,16
(use "RatLeTrans" (pt "abs(as n+ ~(as m))+abs(bs n+ ~(bs m))"))
(use "RatLeAbsPlus")
(use "RatLeTrans" (pt "(1#2**(PosS p))+(1#2**(PosS p))"))
(use "RatLeMonPlus")

(use "CauchyElim" (pt "M"))
(use "CasM")
(use "NatLeTrans" (pt "(M(PosS p))max(N(PosS p))"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "(M(PosS p))max(N(PosS p))"))
(use "NatMaxUB1")
(use "mBd")

;; ?_22:abs(bs n+ ~(bs m))<=(1#2**PosS p)
(use "CauchyElim" (pt "N"))
(use "CbsN")
(use "NatLeTrans" (pt "(M(PosS p))max(N(PosS p))"))
(use "NatMaxUB2")
(use "nBd")
(use "NatLeTrans" (pt "(M(PosS p))max(N(PosS p))"))
(use "NatMaxUB2")
(use "mBd")

;; ?_20:(1#2**PosS p)+(1#2**PosS p)<=(1#2**p)
(simprat "RatPlusHalfExpPosS")
(use "Truth")

;; ?_16:as n+bs n+ ~(as m)+ ~(bs m)=as n+ ~(as m)+(bs n+ ~(bs m))
(ng)
(simp (pf "as n+bs n+ ~(as m)=as n+ ~(as m)+bs n"))
(use "Truth")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp (pf "bs n+ ~(as m)= ~(as m)+bs n"))
(use "Truth")
(use "RatPlusComm")

;; ?_10:Mon(RealMod(RealConstr as M+RealConstr bs N))
(ng)
(use "MonIntro")
(ng)
(assume "p" "q" "p<=q")
(use "NatMaxLUB")
(use "NatLeTrans" (pt "M(PosS q)"))
(use "MonElim")
(use "MonM")
(ng)
(use "p<=q")
(use "NatMaxUB1")
(use "NatLeTrans" (pt "N(PosS q)"))
(use "MonElim")
(use "MonN")
(ng)
(use "p<=q")
(use "NatMaxUB2")
;; Proof finished.
(save "RealPlusReal")

;; RealUMinusReal
(set-goal "all x(Real x -> Real(~x))")
(assume "x" "Rx")
(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(use "RealIntro")
(ng)
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
(simp "RatPlusComm")
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "mBd")
(use "nBd")
;; ?_7:Mon(RealMod~(RealConstr as M))
(ng)
(use "MonM")
;; Proof finished.
(save "RealUMinusReal")

;; RealUMinusRealInv
(set-goal "all x(Real(~ x) -> Real x)")
(cases)
(ng)
(assume "as" "M" "RHyp")
(use "RealIntro")
;; 5,6
(ng)
(inst-with-to "RealToCauchy" (pt "RealConstr([n]~(as n))M") "RHyp" "C~asM")
(ng)
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(inst-with-to "CauchyElim" (pt "[n]~(as n)") (pt "M") "C~asM"
	      (pt "p") (pt "n") (pt "m") "nBd" "mBd" "CauchyElimInst")
(ng "CauchyElimInst")
(simp "<-" "RatAbs0RewRule")
(ng)
(use "CauchyElimInst")
;; 6
(inst-with-to "RealToMon" (pt "RealConstr([n]~(as n))M") "RHyp" "MonM")
(ng)
(use "MonM")
;; Proof finished.
(save "RealUMinusRealInv")

;; RealAbsReal
(set-goal "all x(Real x -> Real(abs x))")
(assume "x" "Rx")
(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(use "RealIntro")
(ng)
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
(use "RatLeAbs")
;; 12,13
(use "RatLeTrans" (pt "abs(as n+ ~(as m))"))
(use "RatLeMinusAbs")
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "nBd")
(use "mBd")
;; 13
(ng)
(simp "RatPlusComm")
(use "RatLeTrans" (pt "abs(as m+ ~(as n))"))
(use "RatLeMinusAbs")
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "mBd")
(use "nBd")
;; ?_7:Mon(RealMod abs(RealConstr as M))
(ng)
(use "MonM")
;; Proof finished.
(save "RealAbsReal")

;; RealUDivReal
(set-goal "all x,q(Real x -> RealPos abs x q -> Real(RealUDiv x q))")
(assume "x" "q" "Rx" "PosHyp")
(assert "all n((abs x)mod(PosS q)<=n -> (1#2**PosS q)<=(abs x)seq n)")
(use-with "RealPosChar1RealConstrFree" (pt "abs x") (pt "q") "?" "?")
(use "RealAbsReal")
(use "Rx")
(use "PosHyp")
;; Assertion proved.
(cases (pt "x"))
(ng)
(assume "as" "M" "x=(as,M)" "asProp")
(use "RealIntro")
(use "CauchyIntro")
(ng)
(assume "p" "n" "m" "nBd" "mBd")
(simprat (pf "RatUDiv(as n)==(as m)*RatUDiv((as n)*(as m))"))
(simprat (pf "RatUDiv(as m)==(as n)*RatUDiv((as n)*(as m))"))
(simprat "RatUDivTimes")
(simp "<-" "RatTimes4RewRule")
(simprat "<-" "RatTimesPlusDistrLeft")
(simp "RatAbsTimes")
(simp "RatAbsTimes")
(simp "RatTimesAssoc")
;; ?_25:abs(as m+ ~(as n))*abs(RatUDiv(as n))*abs(RatUDiv(as m))<=(1#2**p)
(simprat (pf "(1#2**p)==(1#2**(SZero(PosS q)+p))*2**PosS q*2**PosS q"))
(use "RatLeMonTimesTwo")
(simp "<-" "RatAbsTimes")
(use "Truth")
(simp "RatLe9RewRule")
(use "Truth")
(use "RatLeMonTimesTwo")
(use "Truth")
(simp "RatLe9RewRule")
(use "Truth")
;; ?_36:abs(as m+ ~(as n))<=(1#2**(SZero(PosS q)+p))
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(simp "<-" "x=(as,M)")
(use "Rx")
(use "mBd")
(use "nBd")
;; ?_37:abs(RatUDiv(as n))<=2**PosS q
(ng)
(simprat (pf "2**PosS q==RatUDiv(RatUDiv(2**PosS q))"))
(use "RatLeUDiv")
(ng)
(use "Truth")
(ng)
(use "asProp")
(use "NatLeTrans" (pt "M(SZero(PosS q)+p)"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(simp "<-" "x=(as,M)")
(use "Rx")
(use "PosLeTrans" (pt "SZero(PosS q)"))
(use "Truth")
(use "Truth")
(use "nBd")
(simp "RatEqvSym")
(use "Truth")
(use "RatUDivUDiv")
;; ?_31:abs(RatUDiv(as m))<=2**PosS q
(ng)
(simprat (pf "2**PosS q==RatUDiv(RatUDiv(2**PosS q))"))
(use "RatLeUDiv")
(ng)
(use "Truth")
(ng)
(use "asProp")
(use "NatLeTrans" (pt "M(SZero(PosS q)+p)"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(simp "<-" "x=(as,M)")
(use "Rx")
(use "PosLeTrans" (pt "SZero(PosS q)"))
(use "Truth")
(use "Truth")
(use "mBd")
(simp "RatEqvSym")
(use "Truth")
(use "RatUDivUDiv")
;; ?_27:(1#2**p)==(1#2**(SZero(PosS q)+p))*2**PosS q*2**PosS q
(ng)
(simp "<-" "PosExpTwoPosPlus")
;; ?_81:2**SZero(PosS q)*2**p=2**PosS q*2**PosS q*2**p
(assert "all r(SZero r=r+r andi SOne r=PosS(r+r))")
 (ind)
 (split)
 (use "Truth")
 (use "Truth")
 (assume "r" "IH")
 (split)
 (use "IH")
 (use "IH")
 (assume "r" "IH")
 (split)
 (use "IH")
 (use "IH")
(assume "Assertion")
(simp (pf "SZero(PosS q)=PosS q+PosS q"))
(simp "<-" "PosExpTwoPosPlus")
(use "Truth")
(use "Assertion")
;; ?_19:RatUDiv(as m)==as n*RatUDiv(as n*as m)
(use "RatUDivExpandL")
;; ?_99:0<abs(as n)
(use "RatLtLeTrans" (pt "(1#2**PosS q)"))
(use "Truth")
(use "asProp")
(use "NatLeTrans" (pt "M(SZero(PosS q)+p)"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(simp "<-" "x=(as,M)")
(use "Rx")
(use "PosLeTrans" (pt "SZero(PosS q)"))
(use "Truth")
(use "Truth")
(use "nBd")
;; ?_17:RatUDiv(as n)==as m*RatUDiv(as n*as m)
(use "RatUDivExpandR")
;; ?_111:0<abs(as m)
(use "RatLtLeTrans" (pt "(1#2**PosS q)"))
(use "Truth")
(use "asProp")
(use "NatLeTrans" (pt "M(SZero(PosS q)+p)"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(simp "<-" "x=(as,M)")
(use "Rx")
(use "PosLeTrans" (pt "SZero(PosS q)"))
(use "Truth")
(use "Truth")
(use "mBd")
;; ?_12:Mon((RealConstr([n]RatUDiv(as n))([p]M(SZero(PosS q)+p)))mod)
(use "MonIntro")
(ng)
(assume "p1" "p2" "p1<=p2")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(simp "<-" "x=(as,M)")
(use "Rx")
(ng)
(use "p1<=p2")
;; Proof finished.
(save "RealUDivReal")

;; CauchyTimes
(set-goal "all as,M,bs,N,p1,p2(
      Cauchy as M -> 
      Cauchy bs N -> 
      Mon M -> 
      Mon N -> 
      all n abs(as n)<=2**p1 -> 
      all n abs(bs n)<=2**p2 -> 
      Cauchy([n]as n*bs n)([p]M(PosS(p+p2))max N(PosS(p+p1))))")
(assume "as" "M" "bs" "N" "p1" "p2" "CasM" "CbsN" "MonM" "MonN" "p1Bd" "p2Bd")
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
(simprat
 (pf "as n*bs n+ ~(as m*bs m)==as n*(bs n+ ~(bs m))+(as n+ ~(as m))*bs m"))
;; 6,7
(use "RatLeTrans" (pt "abs(as n*(bs n+ ~(bs m)))+abs((as n+ ~(as m))*bs m)"))
;; 8,9
(use "RatLeAbsPlus")
(use "RatLeTrans" (pt "(1#2**PosS p)+(1#2**PosS p)"))
;; 10,11
(use "RatLeMonPlus")
;; 12,13

;; ?_12:abs(as n*(bs n+ ~(bs m)))<=(1#2**PosS p)
(simp "RatAbsTimes")
(use "RatLeTrans" (pt "(2**p1)*(1#2**(p+p1+1))"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "p1Bd")

;; ?_20:abs(bs n+ ~(bs m))<=(1#2**(p+p1+1))
(use "CauchyElim" (pt "N"))
(use "CbsN")
(use "NatLeTrans" (pt "M(PosS(p+p2))max N(PosS(p+p1))"))
(use "NatMaxUB2")
(use "nBd")
(use "NatLeTrans" (pt "M(PosS(p+p2))max N(PosS(p+p1))"))
(use "NatMaxUB2")
(use "mBd")

;; ?_16:2**p1*(1#2**(p+p1+1))<=(1#2**PosS p)
(ng)
(simp "PosSSucc")
(simp "PosSSucc")
(ng)
(simp "PosExpTwoPosPlus")
(simp "PosPlusComm")
(use "Truth")

;; ?_13:abs((as n+ ~(as m))*bs m)<=(1#2**PosS p)
(simp "RatAbsTimes")
(use "RatLeTrans" (pt "(1#2**(p+p2+1))*(2**p2)"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")

;; ?_39:abs(as n+ ~(as m))<=(1#2**(p+p2+1))
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "NatLeTrans" (pt "M(PosS(p+p2))max N(PosS(p+p1))"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "M(PosS(p+p2))max N(PosS(p+p1))"))
(use "NatMaxUB1")
(use "mBd")
(use "p2Bd")

;; ?_36:(1#2**(p+p2+1))*2**p2<=(1#2**PosS p)
(ng)
(simp "PosSSucc")
(simp "PosSSucc")
(ng)
(simp "PosExpTwoPosPlus")
(simp "PosPlusComm")
(use "Truth")

;; ?_11:(1#2**PosS p)+(1#2**PosS p)<=(1#2**p)
(simprat "RatPlusHalfExpPosS")
(use "Truth")

;; ?_7:as n*bs n+ ~(as m*bs m)==as n*(bs n+ ~(bs m))+(as n+ ~(as m))*bs m
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistrLeft")
(ng)
(assert "as n*bs n+ ~(as n*bs m)+as n*bs m==as n*bs n+(~(as n*bs m)+as n*bs m)")
 (use "RatPlusAssoc" (pt "as n*bs n") (pt "~(as n*bs m)") (pt "as n*bs m"))
(assume "Assertion")
(simprat "Assertion")
(drop "Assertion")
(assert "~(as n*bs m)+as n*bs m==0")
 (use "Truth")
(assume "Assertion1")
(simprat "Assertion1")
(use "Truth")
;; Proof finished.
(save "CauchyTimes")

;; RealTimesReal
(set-goal "all x,y(Real x -> Real y -> Real(x*y))")
(assume "x" "y" "Rx" "Ry")
(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(elim "Ry")
(cases)
(assume "bs" "N" "CbsN" "MonN")
(ng)
(use "RealIntro")
(ng)
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
(use-with "CauchyElim"
	  (pt "[n]as n*bs n")
	  (pt "[p]M(PosS(p+cNatPos(RealBd bs N)))max
                  N(PosS(p+cNatPos(RealBd as M)))")
	  "?" (pt "p") (pt "n") (pt "m") "?" "?")
(use "CauchyTimes")
(use "CasM")
(use "CbsN")
(use "MonM")
(use "MonN")
;; ?^23:all n abs(as n)<=2**cNatPos(RealBd as M)
(assert "PosToNat(cNatPos(RealBd as M))=RealBd as M")
 (simp "NatPosExFree")
 (use "PosToNatToPosId")
 (use "Truth")
(assume "EqHyp")
(simp "EqHyp")
(use "RealBdProp")
(use "CasM")
;; ?^24:all n abs(bs n)<=2**cNatPos(RealBd bs N)
(assert "PosToNat(cNatPos(RealBd bs N))=RealBd bs N")
 (simp "NatPosExFree")
 (use "PosToNatToPosId")
 (use "Truth")
(assume "EqHyp")
(simp "EqHyp")
(use "RealBdProp")
(use "CbsN")
;; 17
(ng #t)
(use "nBd")
(use "mBd")
;; 11
(use "MonIntro")
(ng)
(assume "p" "q" "p<=q")
(use "NatMaxLUB")
;; 43,44
(use "NatLeTrans" (pt "M
     (PosS
      (q+
       cNatPos
       (Succ
        (ListNatMax
         (cRatLeAbsBound(bs Zero)::([n]cRatLeAbsBound(bs(Succ n)))fbar N 1)))))"))
(use "MonElim")
(use "MonM")
(ng)
(use "p<=q")
(use "NatMaxUB1")
;; 44
(use "NatLeTrans" (pt "N
     (PosS
      (q+
       cNatPos
       (Succ
        (ListNatMax
         (cRatLeAbsBound(as Zero)::([n]cRatLeAbsBound(as(Succ n)))fbar M 1)))))"))
(use "MonElim")
(use "MonN")
(ng)
(use "p<=q")
(use "NatMaxUB2")
;; Proof finished.
(save "RealTimesReal")

;; RealNNegPlusNNeg
(set-goal "all x,y(RealNNeg x -> RealNNeg y -> RealNNeg(x+y))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "NNegx" "NNegy")
(use "RealNNegChar2RealConstrFree")
(realproof)
(assume "p")
(inst-with-to "RealNNegCharOne"
	      (pt "as") (pt "M") "NNegx" (pt "PosS p") "RealNNegCharOneInstx")
(by-assume "RealNNegCharOneInstx" "n1" "n1Prop")
(inst-with-to "RealNNegCharOne"
	      (pt "bs") (pt "N") "NNegy" (pt "PosS p") "RealNNegCharOneInsty")
(by-assume "RealNNegCharOneInsty" "n2" "n2Prop")
(intro 0 (pt "n1 max n2"))
(assume "n" "nBd")
(simprat "<-" "RatPlusHalfExpPosS")
(simp "RatUMinus2RewRule")
(use "RatLeTrans" (pt "as n+bs n"))
(use "RatLeMonPlus")
(use "n1Prop")
(use "NatLeTrans" (pt "n1 max n2"))
(use "NatMaxUB1")
(use "nBd")
(use "n2Prop")
(use "NatLeTrans" (pt "n1 max n2"))
(use "NatMaxUB2")
(use "nBd")
(ng)
(use "Truth")
;; Proof finished.
(save "RealNNegPlusNNeg")
;; (cdp)
;; ok

;; RealNNegTimesNNeg
(set-goal "all x,y (RealNNeg x -> RealNNeg y -> RealNNeg(x*y))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "0<=x" "0<=y")
(inst-with-to "RealNNegCharOneExFree" (pt "as") (pt "M") "0<=x" "aProp")
(inst-with-to "RealNNegCharOneExFree" (pt "bs") (pt "N") "0<=y" "bProp")
(cut "all n(n=(RealBd as M)max(RealBd bs N) ->
               RealNNeg(RealConstr as M*RealConstr bs N))")
(assume "EqHyp")
(use "EqHyp" (pt "(RealBd as M)max(RealBd bs N)"))
(use "Truth")
(assume "n" "nDef")
(use "RealNNegChar2RealConstrFree")
(realproof)
(assume "p")
(cut "all m(
 m=cRealNNegCharOne M(NatToPos(p+n))max cRealNNegCharOne N(NatToPos(p+n)) ->
 exnc n all l(n<=l -> ~(1#2**p)<=(RealConstr as M*RealConstr bs N)seq l))")
(assume "EqHyp")
(use "EqHyp"
 (pt "cRealNNegCharOne M(NatToPos(p+n))max cRealNNegCharOne N(NatToPos(p+n))"))
(use "Truth")
(assume "m" "mDef")
(intro 0 (pt "m"))
(assume "l" "m<=l")
(ng #t)
;;   x45609  as  M  y45613  bs  N  Rx:
;;     Real(RealConstr as M)
;;   Ry:Real(RealConstr bs N)
;;   0<=x:RealNNeg(RealConstr as M)
;;   0<=y:RealNNeg(RealConstr bs N)
;;   aProp:all p,n(cRealNNegCharOne M p<=n -> ~(1#2**p)<=as n)
;;   bProp:all p,n(cRealNNegCharOne N p<=n -> ~(1#2**p)<=bs n)
;;   n  nDef:n=RealBd as M max RealBd bs N
;;   p  m  mDef:m=cRealNNegCharOne M(NatToPos(p+n))max 
;;              cRealNNegCharOne N(NatToPos(p+n))
;;   l  m<=l:m<=l
;; -----------------------------------------------------------------------------
;; ?^25:(IntN 1#2**p)<=as l*bs l
;; Now the case distinctions
(casedist (pt "as l<=0"))
(assume "as l<=0")
(casedist (pt "bs l<=0"))
(assume "bs l<=0")
;; Case a<=0 & b<=0
(use "RatLeTrans" (pt "0#1"))
(use "Truth")
(simp (pf "(0<=as l*bs l)=(0* ~(bs l)<= ~(as l)* ~(bs l))"))
(use "RatLeMonTimes")
(simp "<-" "RatLeUMinus")
(use "bs l<=0")
(simp "<-" "RatLeUMinus")
(use "as l<=0")
(ng #t)
(use "RatLeCompat")
(simprat (pf "0*bs l==0"))
(use "Truth")
(use "RatTimesZeroL")
(use "Truth")
(assume "bs l<=0 -> F")
;; Case a<=0 & 0<b
(assert "0<bs l")
(use "RatNotLeToLt")
(use "bs l<=0 -> F")
(assume "0<bs l")
(assert "bs l<=2**n")
(use "RatLeTrans" (pt "(2**RealBd bs N#1)"))
(use "RatLeTrans" (pt "abs(bs l)"))
(use "Truth")
(use "RealBdProp")
(use "RealConstrToCauchy")
(realproof)
(simp "nDef")
(ng #t)
(use "PosLeMonPosExp")
(use "NatMaxUB2")
(assume "bs l<=2**n")
(use "RatLeTrans" (pt "~(1#2**(NatToPos(p+n)))*2**n"))
(simp (pf "NatToPos(p+n)=p+n"))
(ng #t)
(simp "PosExpTwoNatPlus")
(simp "NatPlusComm")
(use "Truth")
(use "PosToNatToPosId")
(use "NatLtLeTrans" (pt "Succ Zero"))
(use "Truth")
(use "NatLeTrans" (pt "PosToNat p"))
(simp (pf "Succ Zero=PosToNat 1"))
(simp "PosToNatLe")
(use "Truth")
(use "Truth")
(use "Truth")
(use "RatLeTrans" (pt "as l*2**n"))
(use "RatLeMonTimes")
(use "Truth")
(use "aProp")
(use "NatLeTrans" (pt "m"))
(simp "mDef")
(use "NatMaxUB1")
(use "m<=l")
(simp "<-" "RatLeUMinus")
(simprat (pf "~(as l*bs l)==bs l* ~(as l)"))
(simprat (pf "~(as l*2**n)==2**n* ~(as l)"))
(use "RatLeMonTimes")
(simp "<-" "RatLeUMinus")
(use "as l<=0")
(use "bs l<=2**n")
(ng #t)
(simp "RatTimesComm")
(use "Truth")
(ng #t)
(simp "RatTimesComm")
(use "Truth")
;; Case 0<a
(assume "as l<=0 -> F")
(assert "0<as l")
(use "RatNotLeToLt")
(use "as l<=0 -> F")
(assume "0<as l")
(casedist (pt "0<=bs l"))
;; Case 0<a & 0<=b
(assume "0<=bs l")
(use "RatLeTrans" (pt "0#1"))
(use "Truth")
(use "RatLeTrans" (pt "0*(0#1)"))
(use "Truth")
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "RatLtToLe")
(use "0<as l")
(use "0<=bs l")
;; Case 0<a & b<=0
(assume "0<=bs l -> F")
(assert "bs l<=0")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "0<=bs l -> F")
(assume "bs l<=0")
(assert "as l<=2**n")
(use "RatLeTrans" (pt "(2**RealBd as M#1)"))
(use "RatLeTrans" (pt "abs(as l)"))
(use "Truth")
(use "RealBdProp")
(use "RealConstrToCauchy")
(realproof)
(simp "nDef")
(ng #t)
(use "PosLeMonPosExp")
(use "NatMaxUB1")
(assume "as l<=2**n")
(use "RatLeTrans" (pt "~(1#2**(NatToPos(p+n)))*2**n"))
(simp (pf "NatToPos(p+n)=p+n"))
(ng #t)
(simp "PosExpTwoNatPlus")
(simp "NatPlusComm")
(use "Truth")
(use "PosToNatToPosId")
(use "NatLtLeTrans" (pt "Succ Zero"))
(use "Truth")
(use "NatLeTrans" (pt "PosToNat p"))
(simp (pf "Succ Zero=PosToNat 1"))
(simp "PosToNatLe")
(use "Truth")
(use "Truth")
(use "Truth")
(use "RatLeTrans" (pt "bs l*2**n"))
(use "RatLeMonTimes")
(use "Truth")
(use "bProp")
(use "NatLeTrans" (pt "m"))
(simp "mDef")
(use "NatMaxUB2")
(use "m<=l")
(simp "<-" "RatLeUMinus")
(simprat (pf "~(as l*bs l)==as l* ~(bs l)"))
(simprat (pf "~(bs l*2**n)==2**n* ~(bs l)"))
(use "RatLeMonTimes")
(simp "<-" "RatLeUMinus")
(use "bs l<=0")
(use "as l<=2**n")
(ng #t)
(simp "RatTimesComm")
(use "Truth")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealNNegTimesNNeg")

;; RealLeSChar1
(set-goal "all x,y(all n x seq n<=y seq n-> x<+=y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "AllHyp")
(ng)
(use "RealLeSIntro")
(use "RealNNegSIntro")
(assume "n")
(ng)
(use "RatLePlusR")
(ng)
(use "AllHyp")
;; Proof finished.
(save "RealLeSChar1")

;; RealLeSToLe
(set-goal "all x,y(Real x -> Real y -> x<+=y -> x<<=y)")
(assume "x" "y" "Rx" "Ry" "LeSxy")
(use "RealLeIntro")
(use "Rx")
(use "Ry")
(use "RealNNegSToNNeg")
(realproof)
(use "RealLeSElim")
(use "LeSxy")
;; Proof finished.
(save "RealLeSToLe")

;; RealPosChar2RealConstrFree
(set-goal "all x,n,q(Real x -> all n0(n<=n0 -> (1#2**q)<=x seq n0) ->
                     RealPos x(PosS q))")
(cases)
(assume "as" "M" "n" "q" "Rx" "hyp")
(use "RealPosChar2" (pt "n"))
(use "Rx")
(assume "n0" "n<=n0")
(inst-with-to "hyp" (pt "n0") "hypInst")
(simp "RatLeCompat" (pt "(1#2**q)") (pt "(RealConstr as M)seq n0"))
(use "hypInst")
(use "n<=n0")
(ng)
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealPosChar2RealConstrFree")

;; We transfer properties of RealNNeg to RealLe

;; RealLeCharOneRealConstrFree
(set-goal "all x,y(x<<=y -> 
 all p exl n all n0(n<=n0 -> x seq n0<=y seq n0+(1#2**p)))")
(assume "x" "y" "x<=y")
(assert "RealNNeg(y+ ~x)")
 (use "RealLeElim2")
 (use "x<=y")
(assume "NNeg(y-x)")
(cut "all p exl n all n0(n<=n0 -> ~(1#2**p)<=(y+ ~x)seq n0)")
(cases (pt "x"))
(assume "as" "M")
(cases (pt "y"))
(assume "bs" "N")
(assume "yDef" "xDef")
(ng)
(assume "AllExHyp" "p")
(inst-with-to "AllExHyp" (pt "p") "ExHyp")
(by-assume "ExHyp" "n" "nProp")
(intro 0 (pt "n"))
(assume "n0" "n<=n0")
(inst-with-to "nProp" (pt "n0") "n<=n0" "nPropInst")
(simphyp-to "nPropInst" (pf "(IntN 1#2**p)= ~(1#2**p)") "nPropInstSimp")
(assert "all a,b,c(~c<=b+ ~a -> a<=b+c)")
(assume "a" "b" "c" "~c<=b+ ~a")
(use "RatLePlusCancelR" (pt "~c"))
(simprat "RatEqvPlusMinusRev")
(simp "RatPlusComm")
(use "RatLePlusCancelR" (pt "~a"))
(simprat "RatEqvPlusMinusRev")
(use "~c<=b+ ~a")
;; Assertion proved.
(assume "Assertion")
(use "Assertion")
(use "nPropInstSimp")
(use "Truth")
(use "RealNNegCharOneRealConstrFree")
(use "NNeg(y-x)")
;; Proof finished.
(save "RealLeCharOneRealConstrFree")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)
;; [x,x0]cRealNNegCharOneRealConstrFree(x0+ ~x)

;; RealLeIntroNNegFreeRealConstrFree
(set-goal "all x,y(Real x -> Real y -> 
 all p exnc n all n0(n<=n0 -> ~(1#2**p)<=(y+ ~x)seq n0) -> x<<=y)")
(assume "x" "y" "Rx" "Ry" "AllExHyp")
(use "RealLeIntro")
(use "Rx")
(use "Ry")
(use "RealNNegChar2RealConstrFree")
(realproof)
(use "AllExHyp")
;; Proof finished.
(save "RealLeIntroNNegFreeRealConstrFree")

;; Now we can prove RealLeChar2RealConstrFree

;; RealLeChar2RealConstrFree
(set-goal "all x,y(Real x -> Real y -> 
 all p exnc n all n0(n<=n0 -> x seq n0<=y seq n0+(1#2**p)) -> x<<=y)")
(assume "x" "y" "Rx" "Ry" "AllExHyp")
(use "RealLeIntroNNegFreeRealConstrFree")
(use "Rx")
(use "Ry")
(assume "p")
(inst-with-to "AllExHyp" (pt "p") "ExHyp")
(by-assume "ExHyp" "n" "nProp")
(intro 0 (pt "n"))
(assume "n0" "n<=n0")
(inst-with-to "nProp" (pt "n0") "n<=n0" "LeHyp")
(drop "AllExHyp" "nProp")
(cut "x seq n0<=y seq n0+(1#2**p)")
(cases (pt "x"))
(assume "as" "M" "xDef")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(assert "all a,b,c(a<=b+c -> ~c<=b+ ~a)")
(assume "a" "b" "c" "a<=b+c")
(simprat (pf "~c== ~c+a+ ~a"))
(ng #t)
(simp "RatPlusComm")
(simprat (pf "b==b+c+ ~c"))
(ng #t)
(use "a<=b+c")
(simp "RatEqvSym")
(use "Truth")
(use "RatEqvPlusMinusRev")
(simp "RatEqvSym")
(use "Truth")
(use "RatEqvPlusMinusRev")
;; Assertion proved.
(assume "Assertion")
(ng #t)
(simp (pf "(IntN 1#2**p)= ~(1#2**p)"))
(use "Assertion")
(use "Truth")
(use "LeHyp")
;; Proof finished.
(save "RealLeChar2RealConstrFree")

;; 7.  Compatibilities
;; ===================

;; RealEqCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x===z -> y===z1)")
(assume "x" "y" "z" "z1" "x=y" "z=z1" "x=z")
(use "RealEqTrans" (pt "x"))
(use "RealEqSym")
(use "x=y")
(use "RealEqTrans" (pt "z"))
(use "x=z")
(use "z=z1")
;; Proof finished.
(save "RealEqCompat")

;; RealPosCompat
(set-goal "all as,M,bs,N(
     RealConstr as M===RealConstr bs N -> all p(
     RealPos(RealConstr as M)p ->
     RealPos(RealConstr bs N)(PosS(PosS p))))")
(assume "as" "M" "bs" "N" "x=y" "p" "0<x")
(ng)
;; (1#2**PosS(PosS p))<=bs(N(PosS(PosS(PosS p))))
(use "RatLeTrans" (pt "(1#2**PosS p)+ ~(1#2**PosS(PosS p))"))
;; 4,5
(inst-with-to "RatPlusHalfExpPosS" (pt "PosS p") "RatPlusHalfExpPosSInst")
(simprat "<-" "RatPlusHalfExpPosSInst")
(simp "<-" "RatPlusAssoc")
(use "Truth")
;; ?_5:(1#2**PosS p)+ ~(1#2**PosS(PosS p))<=bs(N(PosS(PosS(PosS p))))
(inst-with-to "RatEqvPlusMinus"
	      (pt "bs(N(PosS(PosS(PosS p))))")
	      (pt "as(M(PosS(PosS(PosS p))))")
	      "RatEqvPlusMinusInst")
(simphyp-to "RatEqvPlusMinusInst" "RatPlusComm" "RatEqvPlusMinusInstSimp")
(drop "RatEqvPlusMinusInst")
(simprat "<-" "RatEqvPlusMinusInstSimp")
(drop "RatEqvPlusMinusInstSimp")
(use "RatLeMonPlus")
;; 17,18
;; ?_17:(1#2**PosS p)<=as(M(PosS(PosS(PosS p))))
(use "RealPosChar1" (pt "M"))
(use "RealEqElim0" (pt "RealConstr bs N"))
(use "x=y")
(use "0<x")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "RealEqElim0" (pt "RealConstr bs N"))
(use "x=y")
(use "PosLeTrans" (pt "PosS(PosS p)"))
(use "Truth")
(use "Truth")
;; ?_18:~(1#2**PosS(PosS p))<=
;;      bs(N(PosS(PosS(PosS p))))+ ~(as(M(PosS(PosS(PosS p)))))
(use "RatLeTrans"
     (pt "~(as(M(PosS(PosS(PosS p))))+ ~(bs(N(PosS(PosS(PosS p))))))"))
(simp "RatLeUMinus")
(use "RatLeTrans"
     (pt "abs(as(M(PosS(PosS(PosS p))))+ ~(bs(N(PosS(PosS(PosS p))))))"))
(use "Truth")
(use "RealConstrEqElim2")
(use "x=y")
(simp "RatPlusComm")
(use "Truth")
;; Proof finished.
(save "RealPosCompat")

;; RealPosCompatRealConstrFree
(set-goal "all x,y(x===y -> all p(RealPos x p -> RealPos y(PosS(PosS p))))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x=y" "p" "0<x")
(use "RealPosCompat" (pt "as") (pt "M"))
(use "x=y")
(use "0<x")
;; Proof finished.
(save "RealPosCompatRealConstrFree")

;; RealNNegCompat
(set-goal "all x,y(x===y -> RealNNeg x -> RealNNeg y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x=y" "0<=x")
(use "RealNNegChar2")
(use "RealEqElim1" (pt "RealConstr as M"))
(use "x=y")
(assume "p")
(inst-with-to "RealNNegCharOne"
	      (pt "as") (pt "M") "0<=x" (pt "PosS p") "CharOneInst")
(by-assume "CharOneInst" "n0" "n0Prop")
(inst-with-to "RealEqCharOne" (pt "as") (pt "bs") (pt "M") (pt "N")
	      "x=y" (pt "PosS p") "EqCharOneInst")
(by-assume "EqCharOneInst" "n1" "n1Prop")
(intro 0 (pt "n0 max n1"))
(assume "n" "nBd")
(use "RatLeTrans" (pt "~(1#2**PosS p)+(as n)"))
(simprat "<-" "RatPlusHalfExpPosS")
(simp "RatUMinus2RewRule")
(use "RatLeMonPlus")
(use "Truth")
(use "n0Prop")
(use "NatLeTrans" (pt "n0 max n1"))
(use "NatMaxUB1")
(use "nBd")
(use "RatLePlusRInv")
(use "RatLeTrans" (pt "abs(as n-bs n)+bs n"))
(use "RatLeTrans" (pt "(as n-bs n)+bs n"))
(ng)
(simprat "RatEqvPlusMinus")
(use "Truth")
(use "RatLeMonPlus")
(ng)
(use "Truth")
(use "Truth")
(use "RatLeMonPlus")
(use "n1Prop")
(use "NatLeTrans" (pt "n0 max n1"))
(use "NatMaxUB2")
(use "nBd")
(use "Truth")
;; Proof finished.
(save "RealNNegCompat")

;; In the proof of RealPlusCompat we use RealPlusComm, whose proof
;; (via realproof) uses RealPlusReal.

;; RealPlusComm
(set-goal "all x,y(Real x -> Real y -> x+y===y+x)")
(assert "all x,y x+y=+=y+x")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealEqSIntro")
(assume "n")
(ng)
(simp "RatPlusComm")
(use "Truth")
;; Assertion proved.
(assume "RealPlusCommEqS")
(assume "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealPlusCommEqS")
;; Proof finished.
(save "RealPlusComm")

;; RealPlusCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x+z===y+z1)")
;; We first proof RealPlusCompatAux
(assert "all x,y,z(Real z -> x===y -> x+z===y+z)")
(assume "x" "y" "z" "Rz" "x=y")
(assert "Real x")
(use "RealEqElim0" (pt "y"))
(use "x=y")
(assume "Rx")
(assert  "Real y")
(use "RealEqElim1" (pt "x"))
(use "x=y")
(assume "Ry")

(assert "Real(y+z)")
(use "RealPlusReal")
(use "Ry")
(use "Rz")
(assert "Real (x+z)")
(use "RealPlusReal")
(use "Rx")
(use "Rz")
(assert "x===y")
(use "x=y")

(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(elim "Ry")
(cases)
(assume "bs" "N" "CbsN" "MonN")
(elim "Rz")
(cases)
(assume "cs" "L" "CcsL" "MonL" "asM=bsN" "Rx+z" "Ry+z")
(ng)
(use "RealEqChar2")
(use "Rx+z")
(use "Ry+z")
;; ?_35:all p 
;;      exl n 
;;       all n0(
;;        n<=n0 -> abs(([n1]as n1+cs n1)n0-([n1]bs n1+cs n1)n0)<=(1#2**p))
(assume "p")
;; n0=cRealEqCharOne M N p
(intro 0 (pt "cRealEqCharOne M N p"))
(assume "n" "n0<=n")
(ng)
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp-with "RatPlusComm" (pt "cs n") (pt "~(bs n)+ ~(cs n)"))
(simp "RatPlusAssoc")
(simp "RatPlusAssoc")
(simprat "RatEqvPlusMinus")
(use "RealEqCharOneExFree" (pt "M") (pt "N"))
(use "asM=bsN")
(use "n0<=n")
;; Assertion proved.
(assume "RealPlusCompatAux")
(assume "x" "y" "z" "z1" "x=y" "z=z1")
(assert "Real y")
(use "RealEqElim1" (pt "x"))
(use "x=y")
(assume "Ry")
(assert "Real z")
(use "RealEqElim0" (pt "z1"))
(use "z=z1")
(assume "Rz")
(use "RealEqTrans" (pt "y+z"))
(use "RealPlusCompatAux")
(use "Rz")
(use "x=y")
(use "RealEqTrans" (pt "z+y"))
(use "RealPlusComm")
(use "Ry")
(use "Rz")
(use "RealEqTrans" (pt "z1+y"))
(use "RealPlusCompatAux")
(use "Ry")
(use "z=z1")
(use "RealPlusComm")
(use "RealEqElim1" (pt "z"))
(use "z=z1")
(use "Ry")
;; Proof finished
(save "RealPlusCompat")

;; RealUMinusCompat
(set-goal "all x,y(x===y -> ~x=== ~y)")
(assert "all x,y(x=+=y -> ~x=+= ~y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x=+=y")
(assert "all n as n==bs n")
 (use "RealConstrEqSElim" (pt "M") (pt "N"))
 (use "x=+=y")
(assume "xyAllHyp")
(drop "x=+=y")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "RatUMinusCompat")
(use "xyAllHyp")
;; Assertion proved.
(assume "RealUMinusCompatEqS" "x" "y" "x=y")
(assert  "Real x")
(use "RealEqElim0" (pt "y"))
(use "x=y")
(assume "Rx")
(assert "Real y")
(use "RealEqElim1" (pt "x"))
(use "x=y")
(assume "Ry")
(use "RealEqIntro")
;; ?_11: Real(~x)
(use "RealUMinusReal")
(use "Rx")
;; ?_12: Real(~y)
(use "RealUMinusReal")
(use "Ry")
;; all p abs((~x)seq((~x)mod(PosS p))+ ~((~y)seq((~y)mod(PosS p))))<=(1#2**p)
(assume "p")
(assert "x===y")
(use "x=y")
(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(elim "Ry")
(cases)
(assume "bs" "N" "CbsN" "MonN" "RasM=RbsN")
(ng)
(assert "all c abs(~c)=abs(c)")
(assume "c")
(use "Truth")
(assume "RatAbsUMinus")
(simp-with "RatAbsUMinus" (pt "as (M(PosS p)) - bs (N(PosS p))"))
(use "RealConstrEqElim2")
(use "RasM=RbsN")
;; Proof finished.
(save "RealUMinusCompat")

;; RealUMinusUMinus
(set-goal "all x(Real x -> ~ ~x===x)")
(assume "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x"))
(assume "as" "M" "xDef")
(use "RealEqSIntro")
(assume "n")
(use "Truth")
;; Proof finished.
(save "RealUMinusUMinus")

;; RealUMinusInj
(set-goal "all x,y(~x=== ~y -> x=== y)")
(assume "x" "y" "EqHyp")
(assert "Real x")
(use "RealUMinusRealInv")
(realproof)
(assume "Rx")
(use "RealEqTrans" (pt "~ ~x"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(realproof)
(use "RealEqTrans" (pt "~ ~y"))
(use "RealUMinusCompat")
(use "EqHyp")
(use "RealUMinusUMinus")
(use "RealUMinusRealInv")
(realproof)
;; Proof finished.
(save "RealUMinusInj")

;; The proof of RealUDivCompat is similar to the one for RealUDivReal

;; RealUDivCompat
(set-goal "all x,y,q(x===y -> RealPos abs x q -> RealPos abs y q -> 
                     RealUDiv x q===RealUDiv y q)")
(assume "x" "y" "q" "x=y" "0<|x|" "0<|y|")
(use "RealEqChar2RealConstrFree")
(use "RealUDivReal")
(realproof)
(use "0<|x|")
(use "RealUDivReal")
(realproof)
(use "0<|y|")
(assert "all p exl n1 all n(n1<=n -> abs(y seq n+ ~(x seq n))<=(1#2**p))")
(use "RealEqCharOneRealConstrFree")
(use "RealEqSym")
(use "x=y")
;; Assertion proved.
(assert "all n((abs y)mod(PosS q)<=n -> (1#2**PosS q)<=(abs y)seq n)")
(use-with "RealPosChar1RealConstrFree" (pt "abs y") (pt "q") "?" "?")
(realproof)
(use "0<|y|")
;; Assertion proved.
(assert "all n((abs x)mod(PosS q)<=n -> (1#2**PosS q)<=(abs x)seq n)")
(use-with "RealPosChar1RealConstrFree" (pt "abs x") (pt "q") "?" "?")
(realproof)
(use "0<|x|")
;; Assertion proved.
(cases (pt "x"))
(assume "as" "M" "x=(as,M)" "asProp")
(cases (pt "y"))
(assume "bs" "N" "y=(bs,N)" "bsProp" "EqChar" "p")
(ng)
;;   asProp:all n(M(PosS q)<=n -> (1#2**PosS q)<=abs(as n))
;;   bsProp:all n(N(PosS q)<=n -> (1#2**PosS q)<=abs(bs n))
;;   EqChar:all p exl n all n0(n<=n0 -> abs(bs n0+ ~(as n0))<=(1#2**p))
;; -----------------------------------------------------------------------------
;; ?^26:exnc n all n0(n<=n0 -> abs(RatUDiv(as n0)+ ~(RatUDiv(bs n0)))<=(1#2**p))
(inst-with-to "EqChar" (pt "SZero(PosS q)+p") "EqCharInst")
(by-assume "EqCharInst" "l" "lProp")
(intro 0 (pt "l max M(PosS q)max N(PosS q)"))
(assume "n" "nBd")
;;   asProp:all n(M(PosS q)<=n -> (1#2**PosS q)<=abs(as n))
;;   bsProp:all n(N(PosS q)<=n -> (1#2**PosS q)<=abs(bs n))
;;   p  l  lProp:all n(l<=n -> abs(bs n+ ~(as n))<=(1#2**(SZero(PosS q)+p)))
;;   n  nBd:l max M(PosS q)max N(PosS q)<=n
;; -----------------------------------------------------------------------------
;; ?^33:abs(RatUDiv(as n)+ ~(RatUDiv(bs n)))<=(1#2**p)
(simprat (pf "RatUDiv(as n)==(bs n)*RatUDiv((as n)*(bs n))"))
(simprat (pf "RatUDiv(bs n)==(as n)*RatUDiv((as n)*(bs n))"))
(simprat "RatUDivTimes")
(simp "<-" "RatTimes4RewRule")
(simprat "<-" "RatTimesPlusDistrLeft")
(simp "RatAbsTimes")
(simp "RatAbsTimes")
(simp "RatTimesAssoc")
;; ?^43:abs(bs n+ ~(as n))*abs(RatUDiv(as n))*abs(RatUDiv(bs n))<=(1#2**p)
(simprat (pf "(1#2**p)==(1#2**(SZero(PosS q)+p))*2**PosS q*2**PosS q"))
(use "RatLeMonTimesTwo")
(simp "<-" "RatAbsTimes")
(use "Truth")
(simp "RatLe9RewRule")
(use "Truth")
(use "RatLeMonTimesTwo")
(use "Truth")
(simp "RatLe9RewRule")
(use "Truth")
;; ?^54:abs(bs n+ ~(as n))<=(1#2**(SZero(PosS q)+p))
(use "lProp")
(use "NatLeTrans" (pt "l max(M(PosS q)max N(PosS q))"))
(use "NatMaxUB1")
(use "nBd")
;; ?^55:abs(RatUDiv(as n))<=2**PosS q
(ng)
(simprat (pf "2**PosS q==RatUDiv(RatUDiv(2**PosS q))"))
(use "RatLeUDiv")
(ng)
(use "Truth")
(ng)
(use "asProp")
(use "NatLeTrans" (pt "l max M(PosS q)"))
(use "NatMaxUB2")
(use "NatLeTrans" (pt "l max M(PosS q)max N(PosS q)"))
(use "NatMaxUB1")
(use "nBd")
;; ?^62:2**PosS q==RatUDiv(RatUDiv(2**PosS q))
(use "RatEqvSym")
(use "RatUDivUDiv")
;; ?^49:abs(RatUDiv(bs n))<=2**PosS q
(ng)
(simprat (pf "2**PosS q==RatUDiv(RatUDiv(2**PosS q))"))
(use "RatLeUDiv")
(ng)
(use "Truth")
(ng)
(use "bsProp")
(use "NatLeTrans" (pt "l max M(PosS q)max N(PosS q)"))
(use "NatMaxUB2")
(use "nBd")
;; ?^75:2**PosS q==RatUDiv(RatUDiv(2**PosS q))
(use "RatEqvSym")
(use "RatUDivUDiv")
;; ?^45:(1#2**p)==(1#2**(SZero(PosS q)+p))*2**PosS q*2**PosS q
(ng)
(simp "<-" "PosExpTwoPosPlus")
;; ?^85:2**SZero(PosS q)*2**p=2**PosS q*2**PosS q*2**p
(assert "all r(SZero r=r+r andi SOne r=PosS(r+r))")
 (ind)
 (split)
 (use "Truth")
 (use "Truth")
 (assume "r" "IH")
 (split)
 (use "IH")
 (use "IH")
 (assume "r" "IH")
 (split)
 (use "IH")
 (use "IH")
(assume "Assertion")
(simp (pf "SZero(PosS q)=PosS q+PosS q"))
(simp "<-" "PosExpTwoPosPlus")
(use "Truth")
(use "Assertion")
;; ?^37:RatUDiv(bs n)==as n*RatUDiv(as n*bs n)
(use "RatUDivExpandL")
;; ?^103:0<abs(as n)
(use "RatLtLeTrans" (pt "(1#2**PosS q)"))
(use "Truth")
(use "asProp")
(use "NatLeTrans" (pt "l max M(PosS q)"))
(use "NatMaxUB2")
(use "NatLeTrans" (pt "l max M(PosS q)max N(PosS q)"))
(use "NatMaxUB1")
(use "nBd")
;; ?^35:RatUDiv(as n)==bs n*RatUDiv(as n*bs n)
(use "RatUDivExpandR")
;; ?^111:0<abs(bs n)
(use "RatLtLeTrans" (pt "(1#2**PosS q)"))
(use "Truth")
(use "bsProp")
(use "NatLeTrans" (pt "l max M(PosS q)max N(PosS q)"))
(use "NatMaxUB2")
(use "nBd")
;; Proof finished.
;; (cdp)
(save "RealUDivCompat")

;; RealAbsCompat
(set-goal  "all x,y(x===y -> abs x===abs y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x=y")
(use "RealEqIntro")
(use "RealAbsReal")
(realproof)
(use "RealAbsReal")
(realproof)
(assume "p")
(ng)
(use "RatLeTrans" (pt "abs(as(M(PosS p))+ ~(bs(N(PosS p))))"))
(use "RatLeAbsMinusAbs")
(use "RealConstrEqElim2")
(use "x=y")
;; Proof finished.
;; (cdp)
(save "RealAbsCompat")

;; In the proof of RealTimesCompat we use RealTimesComm, whose proof
;; (via realproof) uses RealTimesReal.

;; RealTimesComm
(set-goal "all x,y(Real x -> Real y -> x*y===y*x)")
(assert "all x,y x*y=+=y*x")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealEqSIntro")
(assume "n")
(ng)
(simp "RatTimesComm")
(use "Truth")
;; Assertion proved.
(assume "RealTimesCommEqS" "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesCommEqS")
;; Proof finished.
(save "RealTimesComm")

;; RealTimesCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x*z===y*z1)")
;; We first prove RealTimesCompatAux
(assert  "all x,y,z(Real z -> x===y -> x*z===y*z)")
(assume "x" "y" "z" "Rz" "x=y")
(assert "Real x")
(use "RealEqElim0" (pt "y"))
(use "x=y")
(assume "Rx")
(assert "Real y")
(use "RealEqElim1" (pt "x"))
(use "x=y")
(assume "Ry")

(assert "Real (y*z)")
(use "RealTimesReal")
(use "Ry")
(use "Rz")
(assert "Real (x*z)")
(use "RealTimesReal")
(use "Rx")
(use "Rz")
(assert "x===y")
(use "x=y")

(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(elim "Ry")
(cases)
(assume "bs" "N" "CbsN" "MonN")
(elim "Rz")
(cases)
(assume "cs" "L" "CcsL" "MonL" "asM=bsN" "Rxz" "Ryz")
(ng)
(use "RealEqChar2")
(use "Rxz")
(use "Ryz")
;; ?_35:all p 
;;      exl n 
;;       all n0(
;;        n<=n0 -> abs(([n1]as n1*cs n1)n0-([n1]bs n1*cs n1)n0)<=(1#2**p))
(assume "p")
;; n0=cRealEqCharOne M N (p+RealBd cs L)
(intro 0 (pt "cRealEqCharOne M N (p+cNatPos(RealBd cs L))"))
(assume "n" "n0<=n")
(ng)
(simp (pf "~(bs n*cs n)= ~(bs n)*cs n"))
(simprat-with "<-" "RatTimesPlusDistrLeft"
	      (pt "as n")(pt "~(bs n)") (pt "cs n"))
(simp "RatAbsTimes")
(use "RatLeTrans"
     (pt "(1#2**(p+cNatPos(RealBd cs L)))*(2**RealBd cs L)"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
;; ?_48:abs(as n+ ~(bs n))<=(1#2**(p+cNatPos(RealBd cs L)))
(use "RealEqCharOneExFree" (pt "M") (pt "N"))
(use "asM=bsN")
(use "n0<=n")
;; ?_49:abs(cs n)<=2**RealBd cs L
(use "RealBdProp")
(use "CcsL")
(ng)
(simp "<-" "PosExpTwoPosPlus")
(assert "PosToNat(cNatPos(RealBd cs L))=RealBd cs L")
 (simp "NatPosExFree")
 (use "PosToNatToPosId")
(use "RealBdPos")
(assume "EqHyp")
(simp "EqHyp")
(simp "PosTimesComm")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "RealTimesCompatAux")
(assume "x" "y" "z" "z1" "x=y" "z=z1")
(assert "Real y")
(use "RealEqElim1" (pt "x"))
(use "x=y")
(assume "Ry")
(assert "Real z")
(use "RealEqElim0" (pt "z1"))
(use "z=z1")
(assume "Rz")
(use "RealEqTrans" (pt "y*z"))
(use "RealTimesCompatAux")
(use "Rz")
(use "x=y")
(use "RealEqTrans" (pt "z*y"))
(use "RealTimesComm")
(use "Ry")
(use "Rz")
(use "RealEqTrans" (pt "z1*y"))
(use "RealTimesCompatAux")
(use "Ry")
(use "z=z1")
(use "RealTimesComm")
(use "RealEqElim1" (pt "z"))
(use "z=z1")
(use "Ry")
;; Proof finished
(save "RealTimesCompat")

;; RealLeCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x<<=z -> y<<=z1)")
(assume "x" "y" "z" "z1" "x=y" "z=z1" "x<<=z")
(use "RealLeIntro")
(use "RealEqElim1" (pt "x"))
(use "x=y")
(use "RealEqElim1" (pt "z"))
(use "z=z1")
(use "RealNNegCompat" (pt "z+ ~x"))
(use "RealPlusCompat")
(use "z=z1")
(use "RealUMinusCompat")
(use "x=y")
(use "RealLeElim2")
(use "x<<=z")
;; Proof finished.
(save "RealLeCompat")

;; 8.  Further properties
;; ======================

;; RealPlusAssoc
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x+(y+z)===x+y+z)")
(assert "all x,y,z x+(y+z)=+=x+y+z")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "L")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealPlusAssocEqS" "x" "y" "z" "Rx" "Ry" "Rz")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealPlusAssocEqS")
;; Proof finished.
(save "RealPlusAssoc")

;; RealTimesAssoc
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x*(y*z)===x*y*z)")
(assert "all x,y,z x*(y*z)=+=x*y*z")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "L")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesAssocEqS" "x" "y" "z" "Rx" "Ry" "Rz")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesAssocEqS")
;; Proof finished.
(save "RealTimesAssoc")

;; RealTimesPlusDistr
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x*(y+z)===x*y+x*z)")
(assert "all x,y,z x*(y+z)=+=x*y+x*z")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "L")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "RatTimesPlusDistr")
;; Assertion proved.
(assume "RealTimesPlusDistrEqS" "x" "y" "z" "Rx" "Ry" "Rz")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesPlusDistrEqS")
;; Proof finished.
(save "RealTimesPlusDistr")

;; RealTimesPlusDistrLeft
(set-goal "all x,y,z(Real x -> Real y -> Real z -> (x+y)*z===x*z+y*z)")
(assert "all x,y,z (x+y)*z=+=x*z+y*z")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "L")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "RatTimesPlusDistrLeft")
;; Assertion proved
(assume "RealTimesPlusDistrLeftEqS" "x" "y" "z" "Rx" "Ry" "Rz")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesPlusDistrLeftEqS")
;; Proof finished.
(save "RealTimesPlusDistrLeft")

;; RealTimesOne
(set-goal "all x(Real x -> x*1===x)")
(assert "all x x*1=+=x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesOneEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesOneEqS")
;; Proof finished.
(save "RealTimesOne")

;; RealOneTimes
(set-goal "all x(Real x -> 1*x===x)")
(assert "all x 1*x=+=x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealOneTimesEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealOneTimesEqS")
;; Proof finished.
(save "RealOneTimes")

;; RealTimesIntNOne
(set-goal "all x(Real x -> x*IntN 1=== ~x)")
(assert "all x x*IntN 1=+= ~x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesIntNOneEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesIntNOneEqS")
;; Proof finished.
(save "RealTimesIntNOne")

;; RealIntNOneTimes
(set-goal "all x(Real x -> IntN 1*x=== ~x)")
(assert "all x IntN 1*x=+= ~x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealIntNOneTimesEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealIntNOneTimesEqS")
;; Proof finished.
(save "RealIntNOneTimes")

;; RealTimesIdUMinus
(set-goal "all x,y(Real x -> Real y -> x* ~y=== ~(x*y))")
(assert "all x,y x* ~y=+= ~(x*y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesIdUMinusEqS" "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesIdUMinusEqS")
;; Proof finished.
(save "RealTimesIdUMinus")

;; RealTimesIdRatUMinus
(set-goal "all x,k(Real x -> x* ~k=== ~(x*k))")
(assert "all x,k x* ~k=+= ~(x*k)")
(cases)
(assume "as" "M" "k")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesIdRatUMinusEqS" "x" "k" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesIdRatUMinusEqS")
;; Proof finished.
(save "RealTimesIdRatUMinus")

;; RealPosAbs
(set-goal "all p,x(RealPos x p -> RealPos(abs x)p)")
(assume "p")
(cases)
(assume "as" "M" "PosHyp")
(ng)
(use "RatLeTrans" (pt "as(M(PosS p))"))
(use "PosHyp")
(use "Truth")
;; Proof finished.
(save "RealPosAbs")

;; RealTimesUDiv
(set-goal "all x,p(Real x -> RealPos x p -> x*RealUDiv x p===1)")
(assume "x" "p" "Rx" "0<x")
(use "RealEqChar2RealConstrFree")
(use "RealTimesReal")
(use "Rx")
(use "RealUDivReal")
(use "Rx")
(use "RealPosAbs")
(use "0<x")
(use "RealRat")
(assume "q")
(inst-with-to "RealPosChar1RealConstrFree"
	      (pt "x")  (pt "p") "Rx" "0<x" "RealPosChar1RealConstrFreeInst")
(intro 0 (pt "x mod(PosS p)"))
(assume "n" "nBd")
(assert "(1#2**PosS p)<=x seq n")
 (use "RealPosChar1RealConstrFreeInst")
 (use "nBd")
(drop "RealPosChar1RealConstrFreeInst")
(cases (pt "x"))
(assume "as" "M" "Useless")
(ng)
(assume "(1#2**PosS p)<=as n")
;; ?_23:abs(as n*RatUDiv(as n)+IntN 1)<=(1#2**q)
(simprat "RatTimesUDivR")
(use "Truth")
(use "RatLtLeTrans" (pt "(1#2**PosS p)"))
(use "Truth")
(use "RatLeTrans" (pt "as n"))
(use "(1#2**PosS p)<=as n")
(use "Truth")
;; Proof finished.
(save "RealTimesUDiv")

;; RealTimesUMinusId
(set-goal "all x,y(Real x -> Real y -> ~x*y=== ~(x*y))")
(assert "all x,y ~x*y=+= ~(x*y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesUMinusIdEqS" "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesUMinusIdEqS")
;; Proof finished.
(save "RealTimesUMinusId")

;; RealUMinusPlus
(set-goal "all x,y(Real x -> Real y -> ~(x+y)=== ~x+ ~y)")
(assert "all x,y(Real x -> Real y -> ~(x+y)=+= ~x+ ~y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "Rx" "Ry")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealUMinusPlusEqS" "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealUMinusPlusEqS")
(use "Rx")
(use "Ry")
;; Proof finished.
(save "RealUMinusPlus")

;; RealUMinusPlusRat
(set-goal "all x,k(Real x -> ~(x+k)=== ~x+ ~k)")
(assert "all x,k(Real x -> ~(x+k)=+= ~x+ ~k)")
(cases)
(assume "as" "M" "k" "Rx")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealUMinusPlusRatEqS" "x" "k" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealUMinusPlusRatEqS")
(use "Rx")
;; Proof finished.
(save "RealUMinusPlusRat")

;; RealAbsUMinus
(set-goal "all x(Real x -> abs~x===abs x)")
(assert "all x abs~x=+=abs x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(use "Truth")
;; Assertion proved.
(assume "RealAbsUMinusEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealAbsUMinusEqS")
;; Proof finished.
(save "RealAbsUMinus")

;; RealLeUMinus
(set-goal "all x,y(x<<=y -> ~y<<= ~x)")
(assume "x" "y" "x<=y")
(use "RealLeIntro")
(realproof)
(realproof)
(inst-with-to "RealLeElim2" (pt "x") (pt "y") "x<=y" "RealLeElimInst")
(simpreal "RealUMinusUMinus")
(simpreal "RealPlusComm")
(use "RealLeElimInst")
(realproof)
(realproof)
(realproof)
;; Proof finished.
(save "RealLeUMinus")

;; RealLeUMinusInv
(set-goal "all x,y(~y<<= ~x -> x<<=y)")
(assume "x" "y" "~y<=~x")
(assert "Real x")
(use "RealUMinusRealInv")
(realproof)
(assume "Rx")
(assert "Real y")
(use "RealUMinusRealInv")
(realproof)
(assume "Ry")
(simpreal (pf "x=== ~ ~x")) ;here we need RealLeCompat
(simpreal (pf "y=== ~ ~y"))
(use "RealLeUMinus")
(use "~y<=~x")
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "Ry")
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "Rx")
;; Proof finished.
(save "RealLeUMinusInv")

;; Similar to  RealSeqEqToEq we have a pointwise criterium for RealNNeg

;; For RealLeTrans we need a stronger form of RealSeqLeToLe: it
;; suffices to have x seq n<=y seq n from one point onwards.

;; RealSeqLeNNegToNNeg
(set-goal "all x,y,n1(Real y ->
 all n(n1<=n -> x seq n<=y seq n) -> RealNNeg x -> RealNNeg y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "n1" "Ry" "LeHyp" "xNNeg")
(use "RealNNegChar2")
(use "Ry")
(assume "p")
(inst-with-to "RealNNegCharOne" (pt "as") (pt "M") "xNNeg" (pt "p")
	      "RealNNegCharOneInst")
(by-assume "RealNNegCharOneInst" "n2" "n2Prop")
(intro 0 (pt "n1 max n2"))
(assume "n" "nBd")
(use "RatLeTrans" (pt "as n"))
(use "n2Prop")
(use "NatLeTrans" (pt "n1 max n2"))
(use "NatMaxUB2")
(use "nBd")
(use "LeHyp")
(use "NatLeTrans" (pt "n1 max n2"))
(use "NatMaxUB1")
(use "nBd")
;; Proof finished.
(save "RealSeqLeNNegToNNeg")

;; RealNNegPos
(set-goal "all p,q RealNNeg(p#q)")
(assume "p" "q")
(use "RealNNegIntro")
(use "RealRat")
(assume "p1")
(use "Truth")
;; Proof finished.
(save "RealNNegPos")

;; RatNNegToRealNNeg
(set-goal "all a(0<=a -> RealNNeg a)")
(cases)
(cases)
;; 3-5
(strip)
(use "RealNNegPos")
;; 4
(assume "q" "Useless")
(use "RealNNegIntro")
(use "RealRat")
(assume "p1")
(use "Truth")
;; 5
(assume "p" "q" "Absurd")
(use "RealNNegIntro")
(use "RealRat")
(assume "p1")
(use "EfAtom")
(use "Absurd")
;; Proof finished.
(save "RatNNegToRealNNeg")

;; For int, pos and nat the corresponding lemma are easy consequences.

;; RealNNegToRatNNeg
(set-goal "all a(RealNNeg a -> 0<=a)")
(cases)
(cases)
;; 3-5
(strip)
(use "Truth")
;; 4
(strip)
(use "Truth")
;; 5
(assert "all p,q(p*2**q<=q -> q<q)")
(assume "p" "q" "p*2**q<=q")
(use "PosLtLeTrans" (pt "p*2**q"))
(use "PosLtLeTrans" (pt "2**q"))
(use "Truth")
(use "PosLeTrans" (pt "1*2**q"))
(use "Truth")
(use "PosLeMonTimes")
(use "Truth")
(use "Truth")
(use "p*2**q<=q")
;; Assertion proved.
(assume "Assertion" "p" "q" "0<<=-a")
(use "Assertion" (pt "p") (pt "q"))
(inst-with-to "RealNNegCharOneExFree" (pt "[n](IntN p#q)") (pt "[p]Zero")
	      "0<<=-a" (pt "q") (pt "cRealNNegCharOne([p]Zero)q")
	      "Truth" "Absurd")
(drop "0<<=-a")
(ng)
(use "Absurd")
;; Proof finished.
(save "RealNNegToRatNNeg")

;; RealNNegToIntNNeg
(set-goal "all k(RealNNeg k -> 0<=k)")
(assume "k" "NNegHyp")
(assert "RealNNeg(k#1)")
 (use "NNegHyp")
(assume "NNegRatHyp")
(inst-with-to "RealNNegToRatNNeg" (pt "(k#1)") "NNegRatHyp"
	      "RealNNegToRatNNegInst")
(use "RealNNegToRatNNegInst")
;; Proof finished.
(save "RealNNegToIntNNeg")

;; RealSeqLeToLe
(set-goal "all x,y,n1(Real x -> Real y ->
 all n(n1<=n -> x seq n<=y seq n) -> x<<=y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "n1" "Rx" "Ry" "SeqLeHyp")
(ng)
(use "RealLeIntro")
(use "Rx")
(use "Ry")
(inst-with-to "RealSeqLeNNegToNNeg"
	      (pt "RealConstr([n](0#1))([p]Zero)")
	      (pt "RealConstr bs N+ ~(RealConstr as M)") (pt "n1")
	      "RealSeqLeNNegToNNegInst")
(use "RealSeqLeNNegToNNegInst")
(realproof)
(assume "n" "nBd")
(ng)
(assert "all a,b(a<=b -> 0<=b+ ~a)")
 (assume "a" "b" "a<=b")
 (use "RatLeTrans" (pt "a+ ~a"))
 (simprat (pf "a+ ~a==0"))
 (use "Truth")
 (use "Truth")
 (use "RatLeMonPlus")
 (use "a<=b")
 (use "Truth")
(assume "RatLeToZeroLePlusMinus")
(use "RatLeToZeroLePlusMinus")
(use "SeqLeHyp")
(use "nBd")
(drop "RealSeqLeNNegToNNegInst")
(use "RealNNegIntro")
(use "RealRat")
(assume "p")
(ng)
(use "Truth")
;; Proof finished.
(save "RealSeqLeToLe")

;; RatLeToRealLe
(set-goal "all a,b(a<=b -> a<<=b)")
(assume "a" "b" "a<=b")
(use "RealLeIntro")
(use "RealRat")
(use "RealRat")
(use "RatNNegToRealNNeg")
(use "RatLePlusR")
(simp "<-" "RatLeUMinus")
(use "a<=b")
;; Proof finished.
(save "RatLeToRealLe")

;; RealLeToRatLe
(set-goal "all a,b(a<<=b -> a<=b)")
(assume "a" "b" "a<<=b")
(inst-with-to "RealLeElim2"
	      (pt "RealConstr([n]a)([p]Zero)")
	      (pt "RealConstr([n]b)([p]Zero)")
	      "a<<=b" "RealLeElim2Inst")
(inst-with-to "RealNNegToRatNNeg"
	      (pt "b+ ~a")
	      "RealLeElim2Inst"
	      "RealNNegToRatNNegInst")
(assert "a+ ~a<=b+ ~a")
 (simprat (pf "a+ ~a==0"))
 (use "RealNNegToRatNNegInst")
 (use "Truth")
(assume "Assertion")
(use "Assertion")
;; Proof finished.
(save "RealLeToRatLe")

;; RealLeToIntLe
(set-goal "all k,j(k<<=j -> k<=j)")
(assume "k" "j" "k<<=j")
(assert "(k#1)<<=(j#1)")
 (use "k<<=j")
(assume "(k#1)<<=(j#1)")
(inst-with-to "RealLeToRatLe" (pt "(k#1)") (pt "(j#1)") "(k#1)<<=(j#1)"
	      "RealLeToRatLeInst")
(use "RealLeToRatLeInst")
;; Proof finished.
(save "RealLeToIntLe")

;; IntLeToRealLe
(set-goal "all k,j(k<=j -> k<<=j)")
(assume "k" "j" "k<=j")
(use "RatLeToRealLe")
(use "k<=j")
;; Proof finished.
;; (cdp)
(save "IntLeToRealLe")

;; RealLeAbsPlus
(set-goal "all x,y(Real x -> Real y -> abs(x+y)<<=abs x+abs y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "Rx" "Ry")
(use "RealSeqLeToLe" (pt "Zero"))
(use "RealAbsReal")
(use "RealPlusReal")
(use "Rx")
(use "Ry")
(use "RealPlusReal")
(use "RealAbsReal")
(use "Rx")
(use "RealAbsReal")
(use "Ry")
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
(save "RealLeAbsPlus")

;; 2016-11-30.  Additions to rea.scm from Nils Koepp

;; RealPlusMinusZero
(set-goal "all x(Real x -> x+ ~x===0)")
(assert "all x x+ ~x=+=0")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealPlusMinusZeroEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealPlusMinusZeroEqS")
;; Proof finished.
(save "RealPlusMinusZero")

;; RealNNegToEq
(set-goal "all x(RealNNeg x -> RealNNeg(~x) -> x===0)")
(cases)
(assume "as" "M" "NNegx" "NNeg~x")
(use "RealEqIntro")
(realproof)
(use "RealRat")
(assume "p")
(ng)
(use "RatLeAbs")
(use "RatLeTrans" (pt "(1#2**PosS p)"))
(simprat (pf "as(M(PosS p))== ~(([n]~(as n))(M(PosS p)))+0"))
(use "RatLePlusRInv")
(use "RealConstrNNegElim1")
(use "NNeg~x")
(use "Truth")
(simp "<-" "RatLeUMinus")
(simprat "<-" "RatPlusHalfExpPosS")
(simp "RatLeUMinus")
(use "Truth")
(use "RatLeTrans" (pt "(1#2**PosS p)"))
(simprat (pf "~(as(M(PosS p)))== ~(as(M(PosS p)))+0"))
(use "RatLePlusRInv")
(use "RealConstrNNegElim1")
(use "NNegx")
(use "Truth")
(simp "<-" "RatLeUMinus")
(simprat "<-" "RatPlusHalfExpPosS")
(simp "RatLeUMinus")
(use "Truth")
;; Proof finished.
(save "RealNNegToEq")

;; RealAbsId
(set-goal "all x(RealNNeg x -> abs x<<=x)")
(cases)
(assume "as" "M" "0<=x")
(use "RealLeIntro")
(realproof)
(realproof)
(use "RealNNegChar2RealConstrFree")
(realproof)
(assume "p")
(ng)
(inst-with-to "RealNNegCharOne"
	      (pt "as") (pt "M") "0<=x" (pt "PosS p") "RealNNegCharOneInst")
(by-assume "RealNNegCharOneInst" "n" "nProp")
(intro 0 (pt "n"))
(assume "n0" "n0Bd")
(simprat (pf "(IntN 1#2**p)== ~((1#2**PosS p)+(1#2**PosS p))"))
(cases (pt "0<= as n0"))
(assume "0<=a")
(simp "RatAbsId")
(use "RatLeTrans" (pt "(0#1)"))
(use "Truth")
(assert "(as n0+ ~(as n0))==0")
(use "RatEqv2RewRule" (pt "as n0"))
(assume "EqHyp")
(simprat "EqHyp")
(use "Truth")
(use "0<=a")
(assume "0<=a -> F")
(assert "all a ~(a+a)== ~a+ ~a")
(cases)
(strip)
(use "Truth")
(assume "Assertion")
(simprat "Assertion")
(use "RatLeMonPlus")
(use "nProp")
(use "n0Bd")
(drop "Assertion")
(simp "RatLe7RewRule")
(use "RatLeAbs")
(use "RatLeTrans" (pt "(0#1)"))
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "0<=a -> F")
(use "Truth")
(simp (pf "(1#2**PosS p)= ~ ~(1#2**PosS p)"))
(simp "RatLe7RewRule")
(use "nProp")
(use "n0Bd")
(use "Truth")
(simprat "RatPlusHalfExpPosS")
(use "Truth")
;; Proof finished.
(save "RealAbsId")

;; RealLeAbsId
(set-goal "all x(Real x -> x<<=abs x)")
(cases)
(assume "as" "M" "Rx")
(use "RealSeqLeToLe" (pt "Zero"))
(use "Rx")
(realproof)
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
(save "RealLeAbsId")

;; RealAbsAbs
(set-goal "all x abs abs x eqd abs x")
(cases)
(assume "as" "M")
(ng)
(use "InitEqD")
;; Proof finished.
(add-rewrite-rule "abs abs x" "abs x")

;; RealAbsUDiv
(set-goal "all x,p(Real x -> RealPos x p -> 
                   abs(RealUDiv x p)===RealUDiv(abs x)p)")
(assume "x" "p" "Rx" "0<x")
(use "RealEqChar2RealConstrFree")
(use "RealAbsReal")
(use "RealUDivReal")
(use "Rx")
(use "RealPosAbs")
(use "0<x")
(use "RealUDivReal")
(realproof)
(use "RealPosAbs")
(use "RealPosAbs")
(use "0<x")
;; ?_5:all p0 
;;      exnc n 
;;       all n0(
;;        n<=n0 -> 
;;        abs((abs(RealUDiv x p))seq n0+ ~((RealUDiv abs x p)seq n0))<=
;;        (1#2**p0))
(assume "q")
(intro 0 (pt "Zero"))
(assume "n" "Useless")
(cases (pt "x"))
(assume "as" "M" "xDef")
(ng)
(simprat (pf "(RatUDiv abs(as n)+ ~(RatUDiv abs(as n)))==0"))
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealAbsUDiv")

;; RealNNegAbs
(set-goal "all x(Real x -> RealNNeg(abs x))")
(assume "x" "Rx")
(use "RealNNegChar2RealConstrFree")
(realproof)
(assume "p")
(intro 0 (pt "Zero"))
(assume "n" "Useless")
(cases (pt "x"))
(assume "as" "M" "xDef")
(ng #t)
(use "RatLeTrans" (pt "(0#1)"))
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealNNegAbs")

;; RealPosToNNeg
(set-goal "all x,q(Real x -> RealPos x q -> RealNNeg x)")
(assume "x" "q" "Rx" "0<x")
(use "RealNNegChar2RealConstrFree")
(use "Rx")
(assume "p")
(intro 0 (pt "x mod(PosS q)"))
(assume "n" "nBd")
(use "RatLeTrans" (pt "(0#1)"))
(use "Truth")
(use "RatLeTrans" (pt "(1#2**PosS q)"))
(use "Truth")
(use "RealPosChar1RealConstrFree")
(use "Rx")
(use "0<x")
(use "nBd")
;; Proof finished.
(save "RealPosToNNeg")

;; RealPosToNNegUDiv
(set-goal "all x,q(Real x -> RealPos x q -> RealNNeg(RealUDiv x q))")
(cases)
(assume "as" "M" "q" "Rx" "0<x")
(use "RealNNegChar2RealConstrFree")
(use "RealUDivReal")
(use "Rx")
(use "RealPosAbs")
(use "0<x")
(assume "p")
(intro 0 (pt "M(PosS q)"))
(assume "n" "nBd")
(ng)
(use "RatLeTrans" (pt "(0#1)"))
(use "Truth")
(inst-with-to "RealPosChar1"
	      (pt "as") (pt "M") (pt "q") "Rx" "0<x" (pt "n") "nBd"
	      "RealPosChar1Inst")
(assert "all a(0<a -> 0<RatUDiv a)")
 (cases)
 (cases)
 (assume "p1" "q1" "Useless")
 (use "Truth")
 (assume "q1" "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "p1" "q1" "Absurd")
 (use "EfAtom")
 (use "Absurd")
(assume "RatPosUDiv")
(use "RatLtToLe")
(use "RatPosUDiv")
(use "RatLtLeTrans" (pt "(1#2**PosS q)"))
(use "Truth")
(use "RealPosChar1Inst")
;; Proof finished.
(save "RealPosToNNegUDiv")

;; RealLeToPos
(set-goal "all x,p((1#2**p)<<=x -> RealPos x(PosS p))")
(cases)
(assume "as" "M" "p" "LeHyp")
(ng)
(inst-with-to "RealLeElim2"
	      (pt "RealConstr([n](1#2**p))([p]Zero)")
	      (pt "RealConstr as M") "LeHyp"
	      "RealLeElim1Inst")
(inst-with-to "RealNNegElim1" (pt "(RealConstr as M+ ~(1#2**p))")
	      "RealLeElim1Inst" (pt "PosS p") "RealNNegElim1Inst")
(drop "RealLeElim1Inst")
(ng)
(use "RatLeTrans" (pt "0+(1#2**PosS p)"))
(use "Truth")
(use "RatLeTrans"
     (pt "as(M(PosS(PosS p)))+(IntN 1#2**p)+(1#2**PosS p)+(1#2**PosS p)"))
(use "RatLeMonPlus")
(use "RealNNegElim1Inst")
(use "Truth")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(ng)
(simprat "RatPlusZero")
(use "Truth")
;; Proof finished.
(save "RealLeToPos")

;; RealPosMonPlus
(set-goal "all x,y,p,q(Real x -> Real y -> RealPos x p -> RealPos y q ->
                       RealPos(x+y)(PosS(PosS(p min q))))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "p" "q" "Rx" "Ry" "x ppos" "y qpos")
(use "RealPosChar2RealConstrFree" (pt "M(PosS p)max N(PosS q)"))
(realproof)
(assume "n" "n0<=n")
(assert "(1#2**PosS p)<=as n")
(use "RealPosChar1" (pt "M"))
(use "Rx")
(use "x ppos")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS q)"))
(use "NatMaxUB1")
(use "n0<=n")
(assume "ineq01")
(assert "(1#2**PosS q)<=bs n")
(use "RealPosChar1" (pt "N"))
(use "Ry")
(use "y qpos")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS q)"))
(use "NatMaxUB2")
(use "n0<=n")
(assume "ineq02")
(use "RatLeTrans" (pt "(1#2**PosS p)+(1#2**PosS q)"))
(casedist (pt "p<=q"))
(assume "p<=q")
(assert "p min q=p")
(use "PosMinEq2")
(use "p<=q")
(assume "hyp")
(simp "hyp")
(simp "RatPlusComm")
(use "Truth")
(assume "p<=q -> F")
(assert "q<=p")
(use "PosNotLtToLe")
(assume "p<q")
(use "p<=q -> F")
(use "PosLtToLe")
(use "p<q")
(assume "q<=p")
(assert "p min q=q")
(use "PosMinEq1")
(use "q<=p")
(assume "hyp")
(simp "hyp")
(use "Truth")
(simp "RatLeCompat" (pt "(1#2**PosS p)+(1#2**PosS q)") (pt "as n+bs n"))
(use "RatLeMonPlus")
(use "ineq01")
(use "ineq02")
(ng)
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealPosMonPlus")

;; RealApprox
(set-goal "all x,p(Real x -> exl a abs(a+ ~x)<<=(1#2**p))")
(cases)
(assume "as" "M" "p" "Rx")
(intro 0 (pt "as (M p)"))
(use "RealLeIntro")
(realproof)
(use "RealRat")
(use "RealNNegIntro")
(realproof)
(assume "p0")
(ng)
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(use "RatLePlusR")
(simp "<-" "RatLeUMinus")
(simprat (pf "~ ~abs(as(M p)+ ~(as(M(PosS(PosS p0)))))==
              abs(as(M p)+ ~(as(M(PosS(PosS p0)))))"))
(simprat (pf "~(~((1#2**p0)+(1#2**p))+0)==(1#2**p0)+(1#2**p)"))
(use "RatLeTrans" (pt "abs(as(M p)+ ~(as(M (p+(PosS(PosS p0))))))+
                       abs(as(M(p+(PosS(PosS p0))))+ ~(as(M(PosS(PosS p0)))))"))
(use "RatLeAbsMinus")
(simp "RatPlusComm")
(use "RatLeMonPlus")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "(PosS(PosS p0))"))
(use "PosLeTrans" (pt "PosS p0"))
(use "Truth")
(use "Truth")
(ng)
(use "Truth")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "PosS p0"))
(use "Truth")
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(ng)
(use "Truth")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "(PosS(PosS p))"))
(use "PosLeTrans" (pt "PosS p"))
(use "Truth")
(use "Truth")
(ng)
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealApprox")

(define eterm (proof-to-extracted-term))
(define RealApprox-neterm (rename-variables (nt eterm)))
(pp RealApprox-neterm)
;; [x,p][if x ([as,M]as(M p))]

(animate "RealApprox")

;; CRealApproxDef
(set-goal "all x,p cRealApprox x p eqd [if x ([as,M]as(M p))]")
(strip)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CRealApproxDef")

;; RealApproxSound
(set-goal (real-and-formula-to-mr-formula
	   (pt "cRealApprox")
	   (proof-to-formula (theorem-name-to-proof "RealApprox"))))
(use (proof-to-soundness-proof (theorem-name-to-proof "RealApprox")))
;; Proof finished.
;; (cdp)
(save "RealApproxSound")

;; RealApproxSoundCor
(set-goal "allnc x,p(
 Real x ->
 exnc a(a eqd cRealApprox x p andnc abs(a+ ~x)<<=(1#2**p)))")
(assume "x" "p" "Rx")
(intro 0 (pt "cRealApprox x p"))
(split)
(use "InitEqD")
(use-with
 "ExLTMRElim" (py "rat")
 (make-cterm (pv "a") (pf "abs(a+ ~x)<<=(1#2**p)"))
 (pt "cRealApprox x p")
 "?")
(use "RealApproxSound")
;; (use (proof-to-soundness-proof (theorem-name-to-proof "DC")))
(auto)
;; Proof finished.
;; (cdp)
(save "RealApproxSoundCor")

(deanimate "RealApprox")

;; RealLeRefl
(set-goal "all x(Real x -> x<<=x)")
(cases)
(assume "as" "M" "Rx")
(use "RealLeIntro")
(use "Rx")
(use "Rx")
(use "RealNNegIntro")
(realproof)
(assume "p")
(ng)
(simprat (pf "as(M(PosS p))+ ~(as(M(PosS p)))==0"))
(ng)
(use "Truth")
(ng)
(use "Truth")
;; Proof finished.
(save "RealLeRefl")
;; (cdp)

;; RealPlusZero
(set-goal "all x(Real x -> x+0===x)")
(assert "all x x+0=+=x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealPlusZeroEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealPlusZeroEqS")
;; Proof finished.
(save "RealPlusZero")

;; RealZeroPlus
(set-goal "all x(Real x -> 0+x===x)")
(assert "all x 0+x=+=x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealZeroPlusEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealZeroPlusEqS")
;; Proof finished.
(save "RealZeroPlus")

;; RealTimesZero
(set-goal "all x(Real x -> x*0===0)")
(assert "all x x*0=+=0")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "RatTimesZeroR")
;; Assertion proved.
(assume "RealTimesZeroEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesZeroEqS")
;; Proof finished.
(save "RealTimesZero")

;; RealZeroTimes
(set-goal "all x(Real x -> 0*x===0)")
(assert "all x 0*x=+=0")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "RatTimesZeroL")
;; Assertion proved.
(assume "RealZeroTimesEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealZeroTimesEqS")
;; Proof finished.
(save "RealZeroTimes")

;; RealEqPlusMinus
(set-goal "all x,y(Real x -> Real y -> x+ ~y+y===x)")
(assume "x" "y" "Rx" "Ry")
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "~y+y===y+ ~y"))
(simpreal "RealPlusMinusZero")
(use "RealPlusZero")
(use "Rx")
(use "Ry")
(use "RealPlusComm")
(realproof)
(use "Ry")
(use "Ry")
(realproof)
(use "Rx")
;; Proof finished.
(save "RealEqPlusMinus")

;; RealNNegLeToNNeg
(set-goal "all x,y(RealNNeg x -> x<<=y -> RealNNeg y)")
(assume "x" "y" "NNegx" "x<=y")
(simpreal "<-" (pf "y+ ~x+x===y"))
(use "RealNNegPlusNNeg")
(use "RealLeElim2")
(use "x<=y")
(use "NNegx")
(use "RealEqPlusMinus")
(realproof)
(realproof)
;; Proof finished.
(save "RealNNegLeToNNeg")

;; RealPlusInsert (added 2020-08-15)
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x+z===x+ ~y+(y+z))")
(assume "x" "y" "z" "Rx" "Ry" "Rz")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusAssoc")
(simpreal (pf "~y+y===0"))
(simpreal "RealZeroPlus")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusComm")
(use "RealPlusMinusZero")
(autoreal)
;; Proof finished.
(save "RealPlusInsert")

;; RealLeAntiSym
(set-goal "allnc x,y(x<<=y -> y<<=x -> x===y)")
(assume "x" "y" "x<=y" "y<=x")
(assert "x+ ~y===0")
(assert "RealNNeg(y+ ~x)")
(use "RealLeElim2")
(use "x<=y")
(assume "y-x>=0")
(assert "RealNNeg(x+ ~y)")
(use "RealLeElim2")
(use "y<=x")
(assume "x-y>=0")
(use "RealNNegToEq" (pt "x+ ~y"))
(use "x-y>=0")
(use "RealNNegCompat" (pt "y+ ~x"))
(use "RealEqSym")
(use "RealEqTrans" (pt "~x + ~ ~y"))
(use "RealUMinusPlus")
(realproof)
(realproof)
(use "RealEqTrans" (pt "~x +y"))
(use "RealPlusCompat" (pt "~x") (pt "~x") (pt "~ ~y") (pt "y"))
(use "RealEqRefl")
(realproof)
(use "RealUMinusUMinus")
(realproof)
(use "RealPlusComm")
(realproof)
(realproof)
(use "y-x>=0")
(assume "x-y=0")
(use "RealEqTrans" (pt "x+0"))
(use "RealEqSym")
(use "RealPlusZero")
(realproof)
(use "RealEqTrans" (pt "x+ ~y+y"))
(use "RealEqTrans" (pt "x+(~y+y)"))
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealEqSym")
(use "RealEqTrans" (pt "y+ ~y"))
(use "RealPlusComm")
(realproof)
(realproof)
(use "RealPlusMinusZero")
(realproof)
(use "RealPlusAssoc")
(realproof)
(realproof)
(realproof)
(use "RealEqTrans" (pt "0+y"))
(use "RealPlusCompat")
(use "x-y=0")
(use "RealEqRefl")
(realproof)
(use "RealEqTrans" (pt "y+0"))
(use "RealPlusComm")
(use "RealRat")
(realproof)
(use "RealPlusZero")
(realproof)
;; Proof finished.
(save "RealLeAntiSym")

;; RealEqAbs
(set-goal "all x(RealNNeg x -> abs x===x)")
(assume "x" "0<=x")
(use "RealLeAntiSym")
(use "RealAbsId")
(use "0<=x")
(use "RealLeAbsId")
(realproof)
;; Proof finished.
(save "RealEqAbs")

;; RealNNegToUDivAbs
(set-goal "all x,q(RealNNeg x -> RealPos abs x q ->
 RealUDiv abs x q===RealUDiv x q)")
(assume "x" "q" "0<=x" "0<|x|")
(use "RealUDivCompat")
(use "RealEqAbs")
(use "0<=x")
(ng)
(use "0<|x|")
(use "0<|x|")
;; Proof finished.
(save "RealNNegToUDivAbs")

;; RealLeTrans
(set-goal "allnc x,y,z(x<<=y -> y<<=z -> x<<=z)")
(assume "x" "y" "z" "x<=y" "y<=z")
(use "RealLeIntro")
(realproof)
(realproof)
(use "RealNNegCompat" (pt "z+ ~y+(y+ ~x)"))
;;z-y+(y-x)=z-x
(use "RealEqTrans" (pt "z+(~y+(y+ ~x))"))
(use "RealEqSym")
(use "RealPlusAssoc")
(realproof)
(use "RealUMinusReal")
(realproof)
(use "RealPlusReal")
(realproof)
(use "RealUMinusReal")
(realproof)
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealEqTrans" (pt "~y+y+ ~x"))
(use "RealPlusAssoc")
(use "RealUMinusReal")
(realproof)
(realproof)
(use "RealUMinusReal")
(realproof)
(use "RealEqTrans" (pt "0+ ~x"))
(use "RealPlusCompat")
(use "RealEqTrans" (pt "y+ ~y"))
(use "RealPlusComm")
(use "RealUMinusReal")
(realproof)
(realproof)
(use "RealPlusMinusZero")
(realproof)
(use "RealEqRefl")
(use "RealUMinusReal")
(realproof)
(use "RealEqTrans" (pt "~x +0"))
(use "RealPlusComm")
(use "RealRat")
(use "RealUMinusReal")
(realproof)
(use "RealPlusZero")
(use "RealUMinusReal")
(realproof)
;; arithmetic done
(use "RealNNegPlusNNeg")
(use "RealLeElim2")
(use "y<=z")
(use "RealLeElim2")
(use "x<=y")
;; Proof finished.
(save "RealLeTrans")

;; RealLeMonPlus
(set-goal "allnc x,y,z,z0(x<<=y -> z<<=z0 -> x+z<<=y+z0)")
;; First we prove a special case
(assert "allnc x,y,z(Real z -> x<<=y -> x+z<<=y+z)")
(assume "x" "y" "z" "Rz" "x<=y")
(use "RealLeIntro")
(realproof)
(realproof)
(use "RealNNegCompat" (pt "y+ ~x"))
(use "RealEqSym")
(use "RealEqTrans" (pt "y+z+( ~x+ ~z)"))
(use "RealPlusCompat" (pt "y+z") (pt "y+z"))
(use "RealEqRefl")
(realproof)
(use "RealUMinusPlus")
(realproof)
(use "Rz")
(use "RealEqTrans" (pt "y+(z+(~x+ ~z))"))
(use "RealEqSym")
(use "RealPlusAssoc")
(realproof)
(use "Rz")
(realproof)
(use "RealEqTrans" (pt "y+(z+(~z+ ~x))" ))
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealPlusCompat")
(use "RealEqRefl")
(use "Rz")
(use "RealPlusComm")
(realproof)
(realproof)
(use "RealEqTrans" (pt "y+(z+ ~z+ ~x)"))
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealPlusAssoc")
(use "Rz")
(use "RealUMinusReal")
(use "Rz")
(use "RealUMinusReal")
(realproof)
(use "RealEqTrans" (pt "y+(0+ ~x)"))
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealPlusCompat")
(use "RealPlusMinusZero")
(use "Rz")
(use "RealEqRefl")
(use "RealUMinusReal")
(realproof)
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealEqTrans" (pt "~x+0"))
(use "RealPlusComm")
(use "RealRat")
(use "RealUMinusReal")
(realproof)
(use "RealPlusZero")
(use "RealUMinusReal")
(realproof)
(use "RealLeElim2")
(use "x<=y")
;; Assertion proved.
(assume "RealLeMonPlusAux" "x" "y" "z" "z0" "x<=y" "z<=z0")
(use "RealLeTrans" (pt "y+z"))
(use "RealLeMonPlusAux")
(realproof)
(use "x<=y")
(simpreal "RealPlusComm")
(simpreal (pf "y+z0===z0+y"))
(use "RealLeMonPlusAux")
(realproof)
(use "z<=z0")
(use "RealPlusComm")
(realproof)
(realproof)
(realproof)
(realproof)
;; Proof finished.
(save "RealLeMonPlus")

;; RealLeMonTimes
(set-goal "all x,y,z(RealNNeg x -> y<<=z -> x*y<<=x*z)")
(assume "x" "y" "z" "NNegx" "y<=z")
(use "RealLeIntro")
(realproof)
(realproof)
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
(use "RealNNegTimesNNeg")
(use "NNegx")
(use "RealLeElim2")
(use "y<=z")
(realproof)
(realproof)
(realproof)
(realproof)
(realproof)
;; Proof finished.
(save "RealLeMonTimes")

;; RealLeMonTimesL
(set-goal "all x,y,z(RealNNeg z -> x<<=y -> x*z<<=y*z)")
(assume "x" "y" "z" "NNegz" "x<=y")
(simpreal (pf "x*z===z*x"))
(simpreal (pf "y*z===z*y"))
(use "RealLeMonTimes")
(use "NNegz")
(use "x<=y")
(use "RealTimesComm")
(realproof)
(realproof)
(use "RealTimesComm")
(realproof)
(realproof)
;; Proof finished.
(save "RealLeMonTimesL")

;; RealLeMonTimesTwo
(set-goal
 "all x,y,z,z0(RealNNeg x -> RealNNeg z -> x<<=y -> z<<=z0 -> x*z<<=y*z0)")
(assume "x" "y" "z" "z0" "NNegx" "NNegz" "x<=y" "z<=z0")
(use "RealLeTrans" (pt "x*z0"))
(use "RealLeMonTimes")
(use "NNegx")
(use "z<=z0")
(simpreal "RealTimesComm")
(simpreal (pf "y*z0===z0*y"))
(use "RealLeMonTimes")
(use "RealNNegLeToNNeg" (pt "z"))
(use "NNegz")
(use "z<=z0")
(use "x<=y")
(use "RealTimesComm")
(realproof)
(realproof)
(realproof)
(realproof)
;; Proof finished.
(save "RealLeMonTimesTwo")

;; ApproxSplit
(set-goal "all x,y,z,p(Real x -> Real y -> Real z -> RealLt x y p ->
                       z<<=y ori x<<=z)")
(cases)
(assume "as" "M")
(cases)
(assume "as0" "M0")
(cases)
(assume "as1" "M1" "p" "Rx" "Ry" "Rz" "y<x")
(cut "all n,m(n=M0(PosS(PosS p))max M(PosS(PosS p)) -> 
 m=M1(PosS(PosS p))max M0(PosS(PosS p))max M(PosS(PosS p)) -> 
 RealConstr as1 M1<<=RealConstr as0 M0 ori
 RealConstr as M<<=RealConstr as1 M1)")
(assume "allhyp")
(use "allhyp" (pt "M0(PosS(PosS p))max M(PosS(PosS p))")
     (pt "M1(PosS(PosS p))max M0(PosS(PosS p))max M(PosS(PosS p))"))
(use "Truth")
(use "Truth")
(assume "n" "m" "n=" "m=")
(casedist (pt "as1 m <= (as n+as0 n)*(1#2)"))
(assume "hyp")
(intro 0)
(use "RealLeIntro")
(use "Rz")
(use "Ry")
(use "RealNNegChar2RealConstrFree")
(realproof)
(assume "p0")
(intro 0 (pt "m"))
(assume "l" "m<=l")
(use "RatLeTrans" (pt "(0#1)"))
(use "Truth")
(simprat (pf "(RealConstr as0 M0+ ~(RealConstr as1 M1))seq l==as0 l+ ~(as1 l)"))
(simp "RatPlusComm")
(use "RatLePlusR")
(simprat (pf "~ ~(as1 l)+0==as1 l"))
(use "RatLeTrans" (pt "as1 m+(1#2**PosS(PosS p))"))
(use "RatLePlusR")
(use "RatLeTrans" (pt "abs(as1 l+ ~(as1 m))"))
(simp "RatPlusComm")
(ng)
(use "Truth")
(use "CauchyElim" (pt "M1"))
(use "RealConstrToCauchy")
(use "Rz")
(use "NatLeTrans" (pt "m"))
(simp "m=")
(use "NatLeTrans" (pt "M1(PosS(PosS p))max M0(PosS(PosS p))"))
(use "NatMaxUB1")
(use "NatMaxUB1")
(use "m<=l")
(use "NatLeTrans" (pt "m"))
(simp "m=")
(use "NatLeTrans" (pt "M1(PosS(PosS p))max M0(PosS(PosS p))"))
(use "NatMaxUB1")
(use "NatMaxUB1")
(use "Truth")
(use "RatLeTrans" (pt "(as n+as0 n)*(1#2)+(as0 n+ ~(as n))*(1#2**2)"))
(use "RatLeMonPlus")
(use "hyp")
(simprat (pf "(1#2**PosS(PosS p))==(1#2**p)*(1#2**2)"))
(use "RatLeMonTimes")
(use "Truth")
(ng "y<x")
(simp "n=")
(use "y<x")
(assert "(1#2)**PosS(PosS p)==(1#2)**p*(1#2)**2")
(simprat "RatExpPosS")
(simprat "RatExpPosS")
(ng)
(use "Truth")
(assume "arithm")
(use "arithm")
(simprat (pf "(as n+as0 n)*(1#2)+(as0 n+ ~(as n))*(1#2**2)==
              as0 n+ ~(as0 n+ ~(as n))*(1#2**2)"))
(use "RatLeTrans" (pt "as0 n+ ~(1#2**PosS(PosS p))"))
(use "RatLeMonPlus")
(use "Truth")
(simprat (pf "(1#2**PosS(PosS p))==(1#2**p)*(1#2**2)"))
(simprat (pf "~((1#2**p)*(1#2**2))== ~(1#2**p)*(1#2**2)"))
(use "RatLeMonTimes")
(use "Truth")
(simp "RatLeUMinus")
(simp "n=")
(use "y<x")
(use "Truth")
(assert "(1#2)**PosS(PosS p)==(1#2)**p*(1#2)**2")
(simprat "RatExpPosS")
(simprat "RatExpPosS")
(ng)
(use "Truth")
(assume "arithm")
(use "arithm")
(simp "RatPlusComm")
(use "RatLePlusRInv")
(simp "RatPlusComm")
(use "RatLePlusR")
(use "RatLeTrans" (pt "abs(as0 n+ ~(as0 l))"))
(simp "RatPlusComm")
(use "Truth")
(use "CauchyElim" (pt "M0"))
(use "RealConstrToCauchy")
(use "Ry")
(simp "n=")
(use "NatMaxUB1")
(use "NatLeTrans" (pt "m"))
(simp "m=")
(use "NatLeTrans" (pt "M1(PosS(PosS p))max M0(PosS(PosS p))"))
(use "NatMaxUB2")
(use "NatMaxUB1")
(use "m<=l")
;; Rational arithmetic begins
(simprat (pf "~(as0 n+ ~(as n))*(1#2**2)==
               ~(as0 n+ ~(as n))*(1#2)+(as0 n+ ~(as n))*(1#2**2)"))
(simprat (pf "(as0 n+ ~(as n))*(1#2**2)== ~(as0 n+ ~(as n))* ~(1#2**2)"))
(simp "RatPlusAssoc")
(use "RatPlusCompat")
(simprat "RatTimesPlusDistrLeft")
(simprat (pf "~(as0 n+ ~(as n))== ~(as0 n)+as n"))
(simprat "RatTimesPlusDistrLeft")
(simp "RatPlusAssoc")
(simp "RatPlusComm")
(use "RatPlusCompat")
(simprat (pf "~(as0 n)*(1#2)==(as0 n)* ~(1#2)"))
(simprat "RatEqvSym")
(use "Truth")
(simprat (pf "as0 n==as0 n*1"))
(simp "<-" "RatTimesAssoc")
(simprat "<-" "RatTimesPlusDistr")
(use "Truth")
(use "Truth")
(assert "all c,c1 ~c*c1==c* ~c1")
(assume "c" "c1")
(ng)
(use "Truth")
(assume "arithm")
(simprat "arithm")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(assert "all c,c1 c*c1== ~c* ~c1")
(assume "c" "c1")
(use "Truth")
(assume "arithm")
(simprat "arithm")
(use "Truth")
(simprat (pf "(as0 n+ ~(as n))*(1#2**2)== ~(as0 n+ ~(as n))* ~(1#2**2)"))
(simprat "<-" "RatTimesPlusDistr")
(ng)
(use "Truth")
(assert "all c,c1 c*c1== ~c* ~c1")
(assume "c" "c1")
(use "Truth")
(assume "arithm")
(simprat "arithm")
(use "Truth")
(use "Truth")
(use "Truth")
;; done, now 2nd case
(assume "hyp")
(intro 1)
(use "RealLeIntro")
(use "Rx")
(use "Rz")
(use "RealNNegChar2RealConstrFree")
(realproof)
(assume "p0")
(intro 0 (pt "m"))
(assume "l" "m<=l")
(use "RatLeTrans" (pt "(0#1)"))
(use "Truth")
(ng)
(simp "RatPlusComm")
(use "RatLePlusR")
(ng)
(use "RatLeTrans" (pt "as n+(1#2**PosS(PosS p))"))
(use "RatLePlusR")
(simp "RatPlusComm")
(use "RatLeTrans" (pt "abs(as l+ ~(as n))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "NatLeTrans" (pt "m"))
(simp "m=")
(use "NatMaxUB2")
(use "m<=l")
(simp "n=")
(use "NatMaxUB2")
(use "RatLeTrans" (pt "as n+(as0 n+ ~(as n))*(1#2**2)"))
(use "RatLeMonPlus")
(use "Truth")
(simprat (pf "(1#2**PosS(PosS p))==(1#2**p)*(1#2**2)"))
(use "RatLeMonTimes")
(use "Truth")
(simp "n=")
(use "y<x")
(assert "(1#2)**PosS(PosS p)==(1#2)**p*(1#2)**2")
(simprat "RatExpPosS")
(simprat "RatExpPosS")
(ng)
(use "Truth")
(assume "arithm")
(use "arithm")
(simprat (pf "as n+ (as0 n+ ~(as n))*(1#2**2)==
              (as n+as0 n)*(1#2)+ ~(as0 n+ ~(as n))*(1#2**2)"))
(use "RatLeTrans" (pt "as1 m+ ~(1#2**PosS(PosS p))"))
(use "RatLeMonPlus")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "hyp")
(simprat (pf "(1#2**PosS(PosS p))==(1#2**p)*(1#2**2)"))
(simprat (pf "~((1#2**p)*(1#2**2))== ~(1#2**p)*(1#2**2)"))
(use "RatLeMonTimes")
(use "Truth")
(simp "RatLeUMinus")
(simp "n=")
(use "y<x")
(use "Truth")
(assert "(1#2)**PosS(PosS p)==(1#2)**p*(1#2)**2")
(simprat "RatExpPosS")
(simprat "RatExpPosS")
(ng)
(use "Truth")
(assume "arithm")
(use "arithm")
(simp "RatPlusComm")
(use "RatLePlusRInv")
(simp "RatPlusComm")
(use "RatLePlusR")
(use "RatLeTrans" (pt "abs(as1 m+ ~(as1 l))"))
(simp "RatPlusComm")
(use "Truth")
(use "CauchyElim" (pt "M1"))
(use "RealConstrToCauchy")
(use "Rz")
(simp "m=")
(use "NatLeTrans" (pt "M1(PosS(PosS p))max M0(PosS(PosS p))"))
(use "NatMaxUB1")
(use "NatMaxUB1")
(use "NatLeTrans" (pt "m"))
(simp "m=")
(use "NatLeTrans" (pt "M1(PosS(PosS p))max M0(PosS(PosS p))"))
(use "NatMaxUB1")
(use "NatMaxUB1")
(use "m<=l")
;; remaining: rational arithmetic
(simprat (pf "as n+(as0 n+ ~(as n))*(1#2**2)==
              4*as n*(1#2**2)+(as0 n+ ~(as n))*(1#2**2)"))
(simprat "<-" "RatTimesPlusDistrLeft")
(simprat (pf "(as n+ as0 n)*(1#2)==2*(as n+ as0 n)*(1#2**2)"))
(simprat "<-" "RatTimesPlusDistrLeft")
(use "RatTimesCompat")
(ng)
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(simprat (pf "~(as n)+4*as n==3*as n"))
(simprat (pf "2*(as n+as0 n)+ ~(as0 n)==2*as n+as0 n"))
(use "RatEqvSym")
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(simprat (pf "as n+ 2*as n==3*as n"))
(use "Truth")
(simprat (pf "as n+2*as n==1*as n+2*as n"))
(simprat "<-" "RatTimesPlusDistrLeft")
(use "Truth")
(use "Truth")
(simprat "RatTimesPlusDistr")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(simprat (pf "~(as0 n)== ~1*as0 n"))
(simprat "<-" "RatTimesPlusDistrLeft")
(use "Truth")
(use "RatEqvTrans" (pt "~(1*as0 n)"))
(use "Truth")
(assert "all c,c1(~(c*c1)== ~c*c1)")
(assume "c" "c1")
(use "Truth")
(assume "arithm")
(simprat "arithm")
(use "Truth")
(simprat (pf "~(as n)== ~1*as n"))
(simprat "<-" "RatTimesPlusDistrLeft")
(use "Truth")
(use "RatEqvTrans" (pt "~(1*as n)"))
(use "Truth")
(assert "all c,c1(~(c*c1)== ~c*c1)")
(assume "c" "c1")
(use "Truth")
(assume "arithm")
(simprat "arithm")
(use "Truth")
(use "Truth")
(use "RatEqvSym")
(simp "RatTimesComm")
(simp "RatTimesAssoc")
(simprat (pf "(1#2**2)*2==(1#2)"))
(simp "RatTimesComm")
(use "Truth")
(use "Truth")
(use "RatPlusCompat")
(simp "RatTimesComm")
(simp "RatTimesAssoc")
(simprat (pf "(1#2**2)*4==1"))
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "ApproxSplit")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [x,x0,x1,p]
;;  [case x
;;    (RealConstr as M -> 
;;    [case x0
;;      (RealConstr as0 M0 -> 
;;      [case x1
;;        (RealConstr as1 M1 -> 
;;        as1(M1(PosS(PosS p))max M0(PosS(PosS p))max M(PosS(PosS p)))<=
;;        (as(M0(PosS(PosS p))max M(PosS(PosS p)))+
;;         as0(M0(PosS(PosS p))max M(PosS(PosS p))))*
;;        (1#2))])])]

;; RealLeAbs
(set-goal "all x,y(x<<=y -> ~x<<=y -> abs x<<=y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x<=y" "~x<=y")
(use "RealLeIntro")
(realproof)
(realproof)
(inst-with-to "RealConstrLeElim2"
	      (pt "as") (pt "M") (pt "bs") (pt "N") "x<=y" "x<=yInst")
(inst-with-to "RealConstrLeElim2"
	      (pt "[n]~(as n)") (pt "M") (pt "bs") (pt "N") "~x<=y" "~x<=yInst")
(use "RealNNegIntro")
(realproof)
(assume "p")
(inst-with-to "RealConstrNNegElim1"
	      (pt "[n]bs n+ ~(as n)") (pt "[p]N(PosS p)max M(PosS p)")
	      "x<=yInst" (pt "p") "+Hyp")
(inst-with-to "RealConstrNNegElim1"
	      (pt "[n]bs n+ ~(([n0]~(as n0))n)")
	      (pt "[p]N(PosS p)max M(PosS p)")
	      "~x<=yInst" (pt "p") "-Hyp")
(drop "x<=yInst" "~x<=yInst")
(ng)
(use-with "RatAbsCases"
	  (make-cterm (pv "a")
		      (pf "0<=bs(N(PosS p)max M(PosS p))+ ~abs a+(1#2**p)"))
	  (pt "as(N(PosS p)max M(PosS p))") "?" "?")
(assume "+Eq")
(simp "+Eq")
(use "+Hyp")
(assume "-Eq")
(simp "-Eq")
(use "-Hyp")
;; Proof finished.
(save "RealLeAbs")

;; RealLeAbsInv
(set-goal "all x,y(Real x -> abs x<<=y -> ~y<<=x)")
(assume "x" "y" "Rx" "|x|<=y")
(inst-with-to "RealUMinusUMinus" (pt "x") "RealUMinusUMinusInst")
(simpreal "<-" "RealUMinusUMinusInst")
(drop "RealUMinusUMinusInst")
(use "RealLeUMinus")
(use "RealLeTrans" (pt "abs~ x"))
(use "RealLeAbsId")
(realproof)
(simpreal "RealAbsUMinus")
(use "|x|<=y")
(use "Rx")
(use "Rx")
;; Proof finished.
(save "RealLeAbsInv")

;; RealAbsTimes
(set-goal "all x,y(Real x -> Real y -> abs(x*y)===abs x*abs y)")
(assert "all x,y(Real x -> Real y -> abs(x*y)=+=abs x*abs y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "Rx" "Ry")
(use "RealEqSIntro")
(assume "n")
(ng)
(simp "RatAbsTimes")
(use "Truth")
;; Assertion proved.
(assume "RealAbsTimesEqS" "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealAbsTimesEqS")
(use "Rx")
(use "Ry")
;; Proof finished.
(save "RealAbsTimes")

;; RealAbsZero
(set-goal "allnc x(Real x -> abs x===0 -> x===0)")
(assume "x" "Rx" "Abs0")
(use "RealLeAntiSym")
;; 3,4
;; x<<=0
(use "RealLeTrans" (pt "abs x"))
(use "RealLeAbsId")
(use "Rx")
(simpreal "Abs0")
(use "RatLeToRealLe")
(use "Truth")
;; ?^4:0<<=x
(use "RealLeUMinusInv")
(ng #t)
(use "RealLeTrans" (pt "abs ~x"))
(use "RealLeAbsId")
(realproof)
(simpreal "RealAbsUMinus")
(simpreal "Abs0")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealAbsZero")

;; RealAllncTotalIntro
(set-goal "allnc as,M (Pvar rea)(RealConstr as M) -> allnc x (Pvar rea)x")
(assume "asMHyp")
(use "AllncTotalIntro")
(assume "x^" "Tx")
(simp "TotalReaToEqD")
(assert "allnc as^(TotalNc as^ -> allnc M (Pvar rea)(RealConstr as^ M))")
(use-with "AllncTotalElim" (py "nat=>rat")
 (make-cterm (pv "as^") (pf "allnc M (Pvar rea)(RealConstr as^ M)")) "?")
(use "asMHyp")
(assume "Assertion")
(inst-with-to "Assertion" (pt "x^ seq") "AssInst")
(drop "Assertion")
(assert "allnc M^(TotalNc M^ -> (Pvar rea)(RealConstr x^ seq M^))")
(use-with "AllncTotalElim" (py "pos=>nat")
 (make-cterm (pv "M^") (pf "(Pvar rea)(RealConstr x^ seq M^)")) "?")
(use "AssInst")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM" "n^" "Tn")
(use "Tas")
(use "Tn")
;; Assertion proved
(assume "Assertion2")
(use "Assertion2")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM" "p^" "Tp")
(use "TM")
(use "Tp")
(use "Tx")
;; Proof finished.
(save "RealAllncTotalIntro")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [alpha3697]alpha3697

;; RealAllncTotalElim
(set-goal "allnc x (Pvar rea)x -> allnc as,M (Pvar rea)(RealConstr as M)")
(assume "xHyp")
(assert "allnc x^(TotalReaNc x^ -> (Pvar rea)x^)")
 (use-with "AllncTotalElim" (py "rea")
  (make-cterm (pv "x^") (pf "(Pvar rea)x^")) "xHyp")
(assume "Assertion")
(use "AllncTotalIntro")
(assume "as^" "Tas")
(use "AllncTotalIntro")
(assume "M^" "TM")
(use "Assertion")
(use "TotalReaRealConstr")
(use "Tas")
(use "TM")
;; Proof finished.
(save "RealAllncTotalElim")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [alpha3697]alpha3697

;; RealLePlusCancelL
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x+y<<=x+z -> y<<=z)")
(assume "x" "y" "z" "Rx" "Ry" "Rz" "x+y<<=x+z")
(use "RealLeIntro")
 (autoreal)
(inst-with-to "RealLeElim2" (pt "x+y") (pt "x+z") "x+y<<=x+z" "NNegHyp")
(assert "x+z+ ~(x+y)===z+ ~y")
 (simpreal "RealUMinusPlus")
 (simpreal (pf "x+z===z+x"))
 (simpreal "<-" "RealPlusAssoc")
 (use "RealPlusCompat")
 (use "RealEqRefl")
 (autoreal)
 (simpreal "RealPlusComm")
 (simpreal (pf "~x+ ~y=== ~y+ ~x"))
 (simpreal "RealEqPlusMinus")
 (use "RealEqRefl")
 (autoreal)
 (use "RealPlusComm")
 (autoreal)
 (use "RealPlusComm")
 (autoreal)
(assume "Assertion")
(simpreal "<-" "Assertion")
(use "NNegHyp")
;; Proof finished.
(save "RealLePlusCancelL")

;; RealLePlusCancelR
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x+y<<=z+y -> x<<=z)")
(assume "x" "y" "z" "Rx" "Ry" "Rz" "x+y<<=z+y")
(use "RealLePlusCancelL" (pt "y"))
(autoreal)
(simpreal (pf "y+x===x+y"))
(simpreal (pf "y+z===z+y"))
(use "x+y<<=z+y")
(use "RealPlusComm")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
(save "RealLePlusCancelR")

;; RealEqPlusCancelL
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x+y===x+z -> y===z)")
(assume "x" "y" "z" "Rx" "Ry" "Rz" "x+y===x+z")
(use "RealLeAntiSym")
(use "RealLePlusCancelL" (pt "x"))
(autoreal)
(simpreal "x+y===x+z")
(use "RealLeRefl")
(autoreal)
(use "RealLePlusCancelL" (pt "x"))
(autoreal)
(simpreal "x+y===x+z")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
(save "RealEqPlusCancelL")

;; RealEqPlusCancelR
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x+z===y+z -> x===y)")
(assume "x" "y" "z" "Rx" "Ry" "Rz" "x+z===y+z")
(use "RealEqPlusCancelL" (pt "z"))
(autoreal)
(simpreal (pf "z+x===x+z"))
(simpreal (pf "z+y===y+z"))
(use "x+z===y+z")
(use "RealPlusComm")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
(save "RealEqPlusCancelR")

;; RealLeTimesCancelL
(set-goal "all x,y,z,p(Real x -> Real y -> Real z -> RealPos x p ->
 x*y<<=x*z -> y<<=z)")
(assume "x" "y" "z" "p" "Rx" "Ry" "Rz" "PosHyp" "x*y<<=x*z")
(use "RealLeIntro")
 (autoreal)
(inst-with-to "RealLeElim2" (pt "x*y") (pt "x*z") "x*y<<=x*z" "NNegHyp")
(drop "PosHyp"  "x*y<<=x*z")
(inst-with-to "RealPosToNNegUDiv" (pt "x") (pt "p") "Rx" "PosHyp" "UDivHyp")
(assert "z+ ~y===RealUDiv x p*(x*z+ x* ~y)")
 (simpreal "<-" "RealTimesPlusDistr")
 (simpreal "RealTimesAssoc")
 (simpreal (pf "RealUDiv x p*x===x*RealUDiv x p"))
 (simpreal "RealTimesUDiv")
 (simpreal "RealOneTimes")
 (use "RealEqRefl")
 (autoreal)
 (use "PosHyp")
 (autoreal)
 (use "RealTimesComm") 
 (autoreal)
(assume "EqHyp")
(simpreal "EqHyp")
(use "RealNNegTimesNNeg")
(use "UDivHyp")
(simpreal "RealTimesIdUMinus")
(use "NNegHyp")
(autoreal)
;; Proof finished.
(save "RealLeTimesCancelL")

;; RealLeTimesCancelR
(set-goal "all x,y,z,p(Real x -> Real y -> Real z -> RealPos y p ->
 x*y<<=z*y -> x<<=z)")
(assume "x" "y" "z" "p" "Rx" "Ry" "Rz" "PosHyp" "x*y<<=z*y")
(use "RealLeTimesCancelL" (pt "y") (pt "p"))
(autoreal)
(use "PosHyp")
(simpreal (pf "y*x===x*y"))
(simpreal (pf "y*z===z*y"))
(use  "x*y<<=z*y")
(use "RealTimesComm")
(autoreal)
(use "RealTimesComm")
(autoreal)
;; Proof finished.
(save "RealLeTimesCancelR")

;; RealEqTimesCancelL
(set-goal
 "all x,y,z,p(Real x -> Real y -> Real z -> RealPos x p -> x*y===x*z -> y===z)")
(assume "x" "y" "z" "p" "Rx" "Ry" "Rz" "PosHyp" "x*y===x*z")
(use "RealLeAntiSym")
(use "RealLeTimesCancelL" (pt "x") (pt "p"))
(autoreal)
(use "PosHyp")
(simpreal "x*y===x*z")
(use "RealLeRefl")
(autoreal)
(use "RealLeTimesCancelL" (pt "x") (pt "p"))
(autoreal)
(use "PosHyp")
(simpreal "x*y===x*z")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
(save "RealEqTimesCancelL")

;; RealEqTimesCancelR
(set-goal
 "all x,y,z,p(Real x -> Real y -> Real z -> RealPos z p -> x*z===y*z -> x===y)")
(assume "x" "y" "z" "p" "Rx" "Ry" "Rz" "PosHyp" "x*z===y*z")
(use "RealEqTimesCancelL" (pt "z") (pt "p"))
(autoreal)
(use "PosHyp")
(simpreal (pf "z*x===x*z"))
(simpreal (pf "z*y===y*z"))
(use "x*z===y*z")
(use "RealTimesComm")
(autoreal)
(use "RealTimesComm")
(autoreal)
;; Proof finished.
(save "RealEqTimesCancelR")

;; Extend lib files using archive/koepp/lub_lemma.scm and lub_sqrt.scm

;; RealLePlusL
(set-goal "all x,y,z(Real x -> Real y -> Real z -> y<<= ~x+z -> x+y<<=z)")
(assume "x" "y" "z" "Rx" "Ry" "Rz" "y<<= ~x+z")
(use "RealLeTrans" (pt "x+(~x+z)"))
(use "RealLeMonPlus")
(use "RealLeRefl")
(autoreal)
(use "y<<= ~x+z")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusComm")
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
(save "RealLePlusL")

;; RealLePlusLInv
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x+y<<=z -> y<<= ~x+z)")
(assume "x" "y" "z" "Rx" "Ry" "Rz" "x+y<<=z")
(intro 0)
(autoreal)
(simpreal (pf "~x+z+ ~y===z+ ~(x+y)"))
(use "RealLeElim2")
(use "x+y<<=z")
(simpreal (pf "~x+z===z+ ~x"))
(simpreal "RealUMinusPlus")
(simpreal "RealPlusAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
(save "RealLePlusLInv")

;; RealLePlusR
(set-goal "all x,y,z(Real x -> Real y -> Real z -> ~y+x<<=z -> x<<=y+z)")
(assume "x" "y" "z" "Rx" "Ry" "Rz" "~y+x<<=z")
(intro 0)
(autoreal)
(simpreal (pf "y+z+ ~x===z+ ~(~y+x)"))
(use "RealLeElim2")
(use "~y+x<<=z")
(simpreal-with "RealPlusComm" (pt "y") (pt "z") "Ry" "Rz")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealUMinusPlus")
(simpreal "RealUMinusUMinus")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
(save "RealLePlusR")

;; RealLePlusRInv
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x<<=y+z -> ~y+x<<=z )")
(assume "x" "y" "z" "Rx" "Ry" "Rz" "x<<=y+z")
(intro 0)
(autoreal)
(simpreal "<-" (pf "y+z+ ~x===z+ ~(~y+x)"))
(use "RealLeElim2")
(use "x<<=y+z")
(simpreal-with "RealPlusComm" (pt "y") (pt "z") "Ry" "Rz")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealUMinusPlus")
(simpreal "RealUMinusUMinus")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
(save "RealLePlusRInv")

;; RealLePlusUMinus
(set-goal "allnc x,y,z(Real x -> Real y -> Real z -> x+ ~y<<=z -> x+ ~z<<=y)")
(assume "x" "y" "z" "Rx" "Ry" "Rz" "x-y<=z")
(assert "~y+x<<=z")
(simpreal "RealPlusComm")
(use "x-y<=z")
(autoreal)
(assume "-y+x<=z")
(simpreal "RealPlusComm")
(use "RealLePlusRInv")
(autoreal)
(simpreal "RealPlusComm")
(use "RealLePlusR")
(autoreal)
(use "-y+x<=z")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLePlusUMinus")

;; RealLtIntro
(set-goal "all x,y,p(RealPos(y+ ~x)p -> RealLt x y p)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "p" "Hyp")
(simp "RealLt0CompRule")
(use "Hyp")
;; Proof finished.
(save "RealLtIntro")

;;RealLtElim
(set-goal "all x,y,p(RealLt x y p -> RealPos(y+ ~x)p)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "p" "Hyp")
(ng)
(use "Hyp")
;; Proof finished.
(save "RealLtElim")

;; RatEqvToRealEq
(set-goal "all a,b(a==b -> a===b)")
(assume "a" "b" "a==b")
(use "RealLeAntiSym")
(use "RatLeToRealLe")
(use "RatLeRefl")
(use "a==b")
(use "RatLeToRealLe")
(use "RatLeRefl")
(use "RatEqvSym")
(use "a==b")
;; Proof finished.
(save "RatEqvToRealEq")

;; RealEqToRatEqv
(set-goal "all a,b(a===b -> a==b)")
(assume "a" "b" "a===b")
(use "RatLeAntiSym")
(use "RealLeToRatLe")
(simpreal "a===b")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeToRatLe")
(simpreal "a===b")
(use "RatLeToRealLe")
(use "Truth")
;; Proof finished.
(save "RealEqToRatEqv")

;; RealTimesPlusIntNOneDistrLeft
(set-goal "all k,x(Real x -> (x+IntN 1)* ~k===(x* ~k+k))")
(assert "all k,x (x+IntN 1)* ~k=+=(x* ~k+k)")
(assume "k")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(simprat "RatTimesPlusDistrLeft")
(ng)
(simp "IntTimesIntNL")
(use "Truth")
;; Assertion proved.
(assume "RealTimesPlusIntNOneDistrLeftEqS" "k" "x" "Rx")
(use "RealEqSToEq")
(autoreal)
(use "RealTimesPlusIntNOneDistrLeftEqS")
;; Proof finished.
(save "RealTimesPlusIntNOneDistrLeft")

;; RealTimesPlusOneDistrLeft
(set-goal "all k,x(Real x -> (x+1)*k===x*k+k)")
(assert "all k,x (x+1)*k=+=x*k+k")
(assume "k")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(simprat "RatTimesPlusDistrLeft")
(use "RatPlusCompat")
(use "Truth")
(ng)
(use "Truth")
;; Assertion proved.
(assume  "RealTimesPlusOneDistrLeftEqS" "k" "x" "Rx")
(use "RealEqSToEq")
(autoreal)
(use "RealTimesPlusOneDistrLeftEqS")
;; Proof finished.
(save "RealTimesPlusOneDistrLeft")

;; RealNNegAllPlusToNNeg
(set-goal "all x(Real x -> all p RealNNeg(x+(1#2**p)) -> RealNNeg x)")
(assert "all x(Real x -> all p RealNNeg(x+(1#2**p)) -> RealNNeg(x+0))")
(cases)
(assume "as" "M" "Rx" "AllNNeg")
(intro 0)
(realproof)
(assume "p")
(ng)
(use "RatLeAllPlusToLe")
(assume "q")
(inst-with-to "AllNNeg" (pt "q") "AllNNegInst")
(inst-with-to "RealNNegElim1" (pt "RealConstr as M +(1#2**q)") "RealNNegInst")
(ng)
(simp "<-" "RatPlusAssoc")
(simp (pf "(1#2**p)+(1#2**q) = (1#2**q)+(1#2**p)"))
(simp "RatPlusAssoc")
(use "RealNNegInst")
(use "AllNNeg")
(use "RatPlusComm")
;; Assertion proved
(assume "RealNNegAllPlusToNNegAux")
(strip)
(simpreal "<-" "RealPlusZero")
(use "RealNNegAllPlusToNNegAux")
(auto)
;; Proof finished.
;; (cdp)
(save "RealNNegAllPlusToNNeg")

;; RealLeAllPlusToLe
(set-goal "all x,y(Real x -> Real y -> all p x<<=y+(1#2**p) -> x<<=y)")
(assume "x" "y" "Rx" "Ry" "LeAllPlus")
(intro 0)
(autoreal)
(use "RealNNegAllPlusToNNeg")
(realproof)
(assume "p")
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "~x+(1#2**p)===(1#2**p)+ ~x"))
(simpreal "RealPlusAssoc")
(use "RealLeElim2")
(use "LeAllPlus")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeAllPlusToLe")

;; RatUMinusRealUMinus
(set-goal "all a ~a===RealUMinus a")
(assume "a")
(intro 0)
(autoreal)
(assume "p")
(ng)
(assert "~a+a<=(1#2**p)")
(use "RatLePlusRInv")
(use "RatLeTrans" (pt "a+0"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(assume "InEq")
(use "RatLeAbs")
;; 16,17
(use "InEq")
;; 17
(ng)
(simp "RatPlusComm")
(use "InEq")
;; Proof finished.
(save "RatUMinusRealUMinus")

;; RatPlusRealPlus
(set-goal "all a,b a+b===RealPlus a b")
(assume "a" "b")
(intro 0)
(autoreal)
(assume "p")
(ng)
(use "RatLeAbs")
;; 8,9
(simp "RatPlusComm")
(use "RatLePlusRInv")
(simp "RatPlusComm")
(use "RatLePlusRInv")
(ng)
(use "RatLeTrans" (pt "a+b+0"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
;; 9
(ng)
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatLePlusRInv")
(use "RatLePlusRInv")
(ng)
(use "RatLeTrans" (pt "a+b+0"))
(use "Truth")
(use "RatLeMonPlus")
(simp "RatPlusComm")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RatPlusRealPlus")

;; RealPlusHalfExpPosS
(set-goal "allnc p RealPlus(1#2**PosS p)(1#2**PosS p)===(1#2**p)")
(assume "p")
(simpreal "<-" "RatPlusRealPlus")
(use "RatEqvToRealEq")
(use "RatPlusHalfExpPosS")
;; Proof finished.
;; (cdp)
(save "RealPlusHalfExpPosS")

;; RatAbsRealAbs
(set-goal "all a abs a===RealAbs a")
(assume "a")
(intro 0)
(autoreal)
(assume "p")
(ng)
(use "RatLeTrans" (pt "abs(a+ ~a)"))
(use "RatLeAbsMinusAbs")
(assert "~a+a<=(1#2**p)")
(use "RatLePlusRInv")
(use "RatLeTrans" (pt "a+0"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(assume "InEq")
(use "RatLeAbs")
;; 18,19
(simp "RatPlusComm")
(use "InEq")
;; 19
(ng)
(use "InEq")
;; Proof finished.
(save "RatAbsRealAbs")

;; RealLeZeroAbs
(set-goal "all x(Real x -> 0<<=abs x)")
(cases)
(assume "as" "M" "Rx")
(use "RealSeqLeToLe" (pt "Zero"))
(autoreal)
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
(save "RealLeZeroAbs")

;; RealPosPlus
(set-goal "all x,y,p(Real x -> Real y -> 0<<=x -> RealLt 0 y p -> 
 RealLt 0(x+y)(p+3))")
(assume "x" "y" "p" "Rx" "Ry" "Le" "Lt")
(inst-with-to "RealLeCharOneRealConstrFree"
	      (car (predicate-form-to-args (pf "Real 0"))) (pt "x")
	      "Le" "xProp")
(drop "Le")
(inst-with-to "xProp" (pt "p+2") "xpProp")
(drop "xProp")
(by-assume "xpProp" "n" "xpnProp")
(inst-with-to "RealLtElim" (car (predicate-form-to-args (pf "Real 0")))
	      (pt "y") (pt "p") "Lt" "RealPos y+0")
(drop "Lt")
(ng "RealPos y+0")
(assert "Real(y+0)")
(autoreal)
(assume "Ry+0")
(inst-with-to "RealPosChar1RealConstrFree" (pt "y+0") (pt "p")
	      "Ry+0" "RealPos y+0" "ypProp")
(use "RealLtIntro")
(cases (pt "x"))
(assume "as" "M" "xDef")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(assert "RealPos(RealConstr as M+RealConstr bs N+0)(PosS(p+2))")
(assert "RealConstr as M+RealConstr bs N+0 eqd
         RealConstr([n]as n+bs n)([p]M(PosS(PosS p))max N(PosS(PosS p)))")
(intro 0)
(assume "x+y+0Def")
(simp "x+y+0Def")
(use "RealPosChar2" (pt "N(PosS(PosS p))max n"))
(assert "Real(x+y+0)")
(autoreal)
(simp "xDef")
(simp "yDef")
(auto)
(assume "n0" "Hn0")
(ng #t)
(assert "n<=n0")
(use "NatLeTrans" (pt "N(PosS(PosS p))max n"))
(use "NatMaxUB2")
(use "Hn0")
(assume "n<=n0")
(assert "0<=x seq n0+(1#2**(p+2))")
(use-with "xpnProp" (pt "n0") "n<=n0")
(assume "xn0pProp")
(assert "(1#2**(p+2))<=y seq n0-(1#2**(p+2))")
(simphyp-with-to "ypProp" "yDef" "ypn0Prop")
(simp "yDef")
(ng #t)
(simp "RatPlusComm")
(use "RatLePlusR")
(simp (pf "~(IntN 1#2**(p+2))=(1#2**(p+2))"))
(simp (pf "p+2=PosS(p+1)"))
(simprat "RatPlusHalfExpPosS")
(use "ypn0Prop")
(use "NatLeTrans" (pt "N(PosS(PosS p))max n"))
(use "NatMaxUB1")
(use "Hn0")
(cases (pt "p"))
(prop)
(assume "p0" "Hp0")
(prop)
(assume "p0" "Hp0")
(prop)
(use "Truth")
(assume "yn0pProp")
(simprat (pf "(1#2**(p+2))==0+(1#2**(p+2))"))
(simprat (pf "as n0+bs n0==x seq n0+(1#2**(p+2))+(y seq n0-(1#2**(p+2)))"))
(use-with "RatLeMonPlus" (pt "0#1") (pt "x seq n0+(1#2**(p+2))")
	  (pt "(1#2**(p+2))") (pt "y seq n0-(1#2**(p+2))")
	  "xn0pProp" "yn0pProp")
(simp "<-" "RatPlusAssoc")
(simprat (pf "(1#2**(p+2))+(y seq n0-(1#2**(p+2)))==y seq n0"))
(simp "xDef")
(simp "yDef")
(use "Truth")
(simp "RatPlusComm")
(ng #t)
(simp "<-" "RatPlusAssoc")
(use "RatPlusZero")
(simp "RatPlusComm")
(simprat "RatPlusZero")
(use "Truth")
(assume "RealPosx+y+0")
(simp (pf "p+3=(PosS(p+2))"))
(use "RealPosx+y+0")
(cases (pt "p"))
(prop)
(assume "p0" "Hp0")
(prop)
(assume "p0" "Hp0")
(prop)
;; Proof finished.
;; (cdp)
(save "RealPosPlus")

;; Added 2020-08-28

;; A variant (due to Nils Koepp) with
;; RealPlus x p       for RealLt 0 x p
;; RealNNeg x         for 0<<=x
;; PosS(PosS(PosS p)) for p+3

;; RealPosPlus1
(set-goal "all x,y,p(Real x -> Real y ->
 RealNNeg x -> RealPos y p -> RealPos(x+y)(PosS(PosS(PosS p))))")
(cases)
(assume "as" "M")
(cases)
(assume "as0" "M0")
(assume "p" "Rx" "Ry" "0<=x" "0<y")
(use "RealPosChar2RealConstrFree"
     (pt "cRealNNegCharOne M(PosS(PosS p))max(M(PosS(PosS(PosS p)))max
          M0(PosS(PosS(PosS p))))"))
(realproof)
(assume "n" "n0<=n")
(assert "all p,n(cRealNNegCharOne M p<=n -> ~(1#2**p)<=as n)")
 (use "RealNNegCharOneExFree")
 (use "0<=x")
(assume "all_x ineq")
(assert "~(1#2**(PosS(PosS p)))<=as n")
 (inst-with-to "all_x ineq" (pt "PosS(PosS p)") (pt "n") "hyp")
 (drop "all_x ineq")
 (use "hyp")
 (drop "hyp")
(use "NatLeTrans"
     (pt "cRealNNegCharOne M(PosS(PosS p))max (M(PosS(PosS(PosS p)))max
          M0(PosS(PosS(PosS p))))"))
 (use "NatMaxUB1")
 (use "n0<=n")
(assume "x ineq")
(ng #t)
(assert "all n(M0(PosS p) <=n -> (1#2**(PosS p))<=as0 n)")
 (use "RealPosChar1")
 (use "Ry")
 (use "0<y")
(assume "all_y ineq")
(assert "(1#2**(PosS p))<=as0 n")
 (use "all_y ineq")
 (use "NatLeTrans" (pt "M0(PosS(PosS(PosS p)))"))
 (use "MonElim")
 (use "RealConstrToMon" (pt "as0"))
 (use "Ry")
 (use "PosLeTrans" (pt "PosS(PosS p)"))
 (use "Truth")
 (use "Truth")
 (use "NatLeTrans" (pt "M(PosS(PosS(PosS p)))max M0(PosS(PosS(PosS p)))"))
 (use "NatMaxUB2")
(use "NatLeTrans"
     (pt "cRealNNegCharOne M(PosS(PosS p))max (M(PosS(PosS(PosS p)))max
          M0(PosS(PosS(PosS p))))"))
 (use "NatMaxUB2")
 (use "n0<=n")
(assume "y ineq")
(drop "all_y ineq")
(use "RatLeTrans" (pt "(IntN 1#2**PosS(PosS p))+(1#2**PosS p)"))
(simprat (pf "(IntN 1#2**PosS(PosS p))+(1#2**PosS p)==(1#2**(PosS(PosS p)))"))
(use "Truth")
(simprat "<-" "RatPlusHalfExpPosS")
(simp "RatPlusAssoc")
(simprat (pf "(IntN 1#2**PosS(PosS p))+(1#2**PosS(PosS p))==0"))
(ng)
(use "Truth")
(ng)
(use "Truth")
(use "RatLeMonPlus")
(use "x ineq")
(use "y ineq")
;; Proof finished.
;; (cdp)
(save "RealPosPlus1")

;; Added 2020-07-19

;; RealLeAbsMinus
(set-goal "all x,y,z (Real x -> Real y -> Real z ->
 abs(x+ ~y) <<= abs(x+ ~z) + abs(z+ ~y))")
(assume "x" "y" "z" "x_r" "y_r" "z_r")
(simpreal (pf "x+ ~y ===(x+ ~z) + (z+ ~y)"))
(use "RealLeAbsPlus")
(autoreal)
(simpreal "RealPlusAssoc")
(simpreal (pf "x+ ~z +z===x+ (~z +z)"))
(simpreal (pf "~z +z===z + ~z"))
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
(use "RealEqSym")
(use "RealPlusAssoc")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeAbsMinus")

;; RealAbsPlusUMinus
(set-goal "allnc x,y(Real x -> Real y -> abs(x+ ~y)===abs(y+ ~x))")
(assume "x" "y" "Rx" "Ry")
(simpreal "<-" "RealAbsUMinus")
(simpreal "RealUMinusPlus")
(simpreal "RealUMinusUMinus")
(simpreal "RealPlusComm")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealAbsPlusUMinus")

;; Added 2020-08-28

;; RealLtIrrefl
(set-goal "all x,p(Real x -> RealLt x x p -> F)")
(assume "x" "p" "Rx" "x<x")
(use-with
 "RealPosCompatRealConstrFree"
 (pt "x+ ~x")
 (pt "RealConstr([n](IntZero#1))([p]Zero)")
 "?" (pt "p") "?")
(use "RealPlusMinusZero")
(use "Rx")
(use "RealLtElim")
(use "x<x")
;; Proof finished.
;; (cdp)
(save "RealLtIrrefl")

;; RealLtLeTrans
(set-goal "all x,y,z,p(Real x -> Real y -> Real z ->
 RealLt x y p -> y<<=z -> RealLt x z(PosS(PosS(PosS(PosS(PosS p))))))")
(assume "x" "y" "z" "p" "Rx" "Ry" "Rz" "x<y" "y<=z")
(use "RealLtIntro")
(use "RealPosCompatRealConstrFree" (pt "z+ ~y+(y+ ~x)"))
;; ?^4:z+ ~y+(y+ ~x)===z+ ~x
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(use "Rz")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusComm")
(simpreal "RealPlusAssoc")
(simpreal "RealEqPlusMinus")
(use "RealEqRefl")
(autoreal)
;; ?^5:RealPos(z+ ~y+(y+ ~x))(PosS(PosS(PosS p)))
(use "RealPosPlus1")
(autoreal)
(use "RealLeElim2")
(use "y<=z")
(use "RealLtElim")
(use "x<y")
;; Proof finished.
(save "RealLtLeTrans")

;; RealLeLtTrans
(set-goal "all x,y,z,p(Real x -> Real y -> Real z ->
 x<<=y -> RealLt y z p -> RealLt x z(PosS(PosS(PosS(PosS(PosS p))))))")
(assume "x" "y" "z" "p" "Rx" "Ry" "Rz" "x<=y" "y<z")
(use "RealLtIntro")
(use "RealPosCompatRealConstrFree" (pt "y+ ~x+(z+ ~y)"))
;; ?^4:y+ ~x+(z+ ~y)===z+ ~x
(simpreal "RealPlusComm")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(use "Rz")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusComm")
(simpreal "RealPlusAssoc")
(simpreal "RealEqPlusMinus")
(use "RealEqRefl")
(autoreal)
;; ?^5:RealPos(y+ ~x+(z+ ~y))(PosS(PosS(PosS p)))
(use "RealPosPlus1")
(autoreal)
(use "RealLeElim2")
(use "x<=y")
(use "RealLtElim")
(use "y<z")
;; Proof finished.
(save "RealLeLtTrans")

;; RatLtToRealLt
(set-goal "all a,b(a<b -> exl p RealLt a b p)")
(assume "a" "b" "a<b")
(ng)
(assert "a+ ~a<b+ ~a")
(ng)
(use "a<b")
(assume "a+ ~a<b+ ~a")
(use "RatLeLowerBound")
(simprat (pf "0==a+ ~a"))
(ng)
(use "a<b")
(use "RatEqvSym")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RatLtToRealLt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [a,a0]cRatLeLowerBound(a0+ ~a)

;; RealLeTransRat
(set-goal "all a,x,b(a<<=x -> x<<=b -> a<=b)")
(assume "a" "x" "b" "a<=x" "x<=b")
(use "RatNotLtToLe")
(assume "b<a")
(inst-with-to "RatLtToRealLt" (pt "b") (pt "a") "b<a" "pEx")
(by-assume "pEx" "p" "pProp")
(use-with "RealLtIrrefl"
	  (pt "x")
	  (pt "PosS(PosS(PosS(PosS(PosS(PosS(PosS(PosS(PosS(PosS p)))))))))")
	  "?" "?")
(realproof)
(use "RealLeLtTrans" (pt "RealConstr([n]b)([p]Zero)"))
(autoreal)
(use "x<=b")
;; ?^16:RealLt b x(PosS(PosS(PosS(PosS(PosS p)))))
(use "RealLtLeTrans" (pt "RealConstr([n]a)([p]Zero)"))
(autoreal)
(use "pProp")
(use "a<=x")
;; Proof finished.
;; (cdp)
(save "RealLeTransRat")

;; RealLeBound
(set-goal "all x(Real x -> x<<=2**(RealBd(x seq)(x mod)))")
(cases)
(assume "as" "M" "Rx")
(simp "RealSeq0CompRule")
(simp "RealMod0CompRule")
;; ?^5:RealConstr as M<<=2**RealBd as M
(use "RealLeSToLe")
(use "Rx")
(use "RealRat")
(use "RealLeSChar1")
(simp "RealSeq0CompRule")
(assume "n")
(use "RatLeTrans" (pt "abs(as n)"))
(use "Truth")
(use "RealBdProp")
(use "RealConstrToCauchy")
(use "Rx")
;; Proof finished.
(save "RealLeBound")

;; From semws18/completeness.scm (by Max Zeuner):
;; RatCauchyConvMod
(set-goal "all as,M,p,n(Real(RealConstr as M) -> M p<=n ->
                        abs(as n+ ~(RealConstr as M))<<=(1#2**p))")
(assume "as" "M" "p" "n" "Rx" "nBd")
(use "RealLeChar2RealConstrFree")
;; 3-5
(realproof)
;; 4
(use "RealRat")
;; 5
(ng)
(assume "p0")
(simp (pf "(2**p0+2**p#2**p*2**p0)=((1#2**p)+(1#2**p0))"))
(intro 0 (pt "M p"))
(assume "n0" "n0Bd")
(use "RatLeTrans" (pt "(1#2**p)+0"))
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "nBd")
(use "n0Bd")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RatCauchyConvMod")

;; RealEqIntro1
(set-goal "all x,y(Real x -> Real y -> all p abs(x+ ~y)<<=(1#2**p) -> x===y)")
(assume "x" "y" "x_r" "y_r" "assumption")
(assert "all x,p,n(Real x -> x mod p<=n -> abs(x seq n+ ~x)<<=(1#2**p))")
(cases)
(use "RatCauchyConvMod")
(assume "RealCauchyConv1")
(use "RealEqChar2RealConstrFree")
(autoreal)
(assume "p")
(intro 0 (pt "x mod (p+2) max y mod (p+2)"))
(assume "n")
(assume "nDef")
(use "RealLeToRatLe")
(use "RealLeTrans" (pt "abs(x seq n + ~x) + abs(x + ~(y seq n))"))
(simpreal "RatAbsRealAbs")
(simpreal "RatPlusRealPlus")
(simpreal "RatUMinusRealUMinus")
(use "RealLeAbsMinus")
(autoreal)
(simpreal (pf "(1#2**p)===RealPlus(1#2**(p+1))(1#2**(p+1))"))
;; 1#2**p ===RealConstr([n](1#2**(p+1)))([p] Zero) + RealConstr([n](1#2**(p+1)))([p] Zero)"))
(use "RealLeMonPlus")
(use "RealLeTrans" (pt "RealConstr([n]1#2**(p+2))([p] Zero)"))
(use "RealCauchyConv1")
(autoreal)
(use "NatLeTrans" (pt "x mod(p+2)max y mod(p+2)"))
(use "NatMaxUB1")
(use "nDef")
(use "RatLeToRealLe")
(ng #t)
(use "NatLeMonTwoExp")
(simp "PosToNatLe")
(use "PosLeTrans" (pt "p+1"))
(search)
(simp (pf "p+2=PosS (PosS p)"))
(ng #t)
(use "Truth")
(simp "<-" "PosPlus0CompRule")
(simp "<-" "PosPlus0CompRule")
(simp "<-" "PosPlusAssoc")
(simp (pf "1+1=2"))
(ng #t)
(use "Truth")
(search)
(use "RealLeTrans" (pt "abs(x+ ~y) + abs(y + ~(y seq n))"))
(simpreal "RatUMinusRealUMinus")
(use "RealLeAbsMinus")
(autoreal)
(simpreal (pf "(1#2**(p+1))===RealPlus(1#2**(p+2))(1#2**(p+2))"))
(use "RealLeMonPlus")
(use "assumption")
(simpreal "<-" "RealAbsUMinus")
(simpreal "RealUMinusPlus")
(simpreal "RealPlusComm")
(simpreal "RatUMinusRealUMinus")
(simpreal "RealUMinusUMinus")
(use "RealCauchyConv1")
(autoreal)
(use "NatLeTrans" (pt "x mod(p+2)max y mod(p+2)"))
(use "NatMaxUB2")
(use "nDef")
(autoreal)
(simpreal "<-" "RatPlusRealPlus")
(use "RatEqvToRealEq")
(use "RatEqvSym")
(simp (pf "p+2=PosS (p+1)"))
(use "RatPlusHalfExpPosS")
(simp (pf "2=1+1"))
(simp "PosPlusAssoc")
(ng #t)
(use "Truth")
(search)
(simpreal "<-" "RatPlusRealPlus")
(use "RatEqvToRealEq")
(use "RatEqvSym")
(use "RatPlusHalfExpPosS")
;; Proof finished.
;; (cdp)
(save "RealEqIntro1")

(add-var-name "xs" (py "nat=>rea"))

;; Condition Mon M added by Wolfgang Boehnisch
(add-ids
 (list (list "RealConv"
	     (make-arity (py "nat=>rea") (py "rea") (py "pos=>nat"))))
 '("allnc xs,x,M(allnc n Real(xs n) -> Real x -> Mon M ->
               allnc p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) ->
               RealConv xs x M)" "RealConvIntro"))

;; RealConvElim1
(set-goal "allnc xs,x,M(RealConv xs x M -> allnc n Real(xs n))")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
(save "RealConvElim1")

;; RealConvElim2
(set-goal "allnc xs,x,M(RealConv xs x M -> Real x)")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
(save "RealConvElim2")

;; RealConvElim3
(set-goal "allnc xs,x,M(RealConv xs x M -> Mon M)")
(assume "xs" "x" "M")
(elim)
(search)
(save "RealConvElim3")

;; RealConvElim4
(set-goal
 "allnc xs,x,M(RealConv xs x M -> allnc p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)))")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
(save "RealConvElim4")

;; 2020-11-19.  The essential content of RealConvEq is in RealLimCompat,
;; which does not involve RealConv.

;; RealConvEq
(set-goal "allnc x,x0,xs,xs0,M,M0(
     allnc n xs n===xs0 n -> RealConv xs x M -> RealConv xs0 x0 M0 -> x===x0)")
(assume "x" "x0" "xs" "xs0" "M" "M0" "eq" "xsConv" "xs0Conv")
(assert "Real x")
(use "RealConvElim2" (pt "xs") (pt "M"))
(use "xsConv")
(assume "x_r")
(assert "Real x0")
(use "RealConvElim2" (pt "xs0") (pt "M0"))
(use "xs0Conv")
(assume "x0_r")
(use "RealEqIntro1")
(autoreal)
(assume "p")
(assert "Real (xs(M(p+1) max M0(p+1)))")
(use "RealConvElim1" (pt "x") (pt "M"))
(use "xsConv")
(assume "xs_r")
(assert "Real (xs0(M(p+1) max M0(p+1)))")
(use "RealConvElim1" (pt "x0") (pt "M0"))
(use "xs0Conv")
(assume "xs0_r")
(use "RealLeTrans"
     (pt "abs(x+ ~(xs(M(p+1)max M0(p+1))))+abs(xs(M(p+1)max M0(p+1))+ ~x0)"))
(use "RealLeAbsMinus")
(autoreal)
(simpreal (pf "(1#2**p)===RealPlus(1#2**(p+1))(1#2**(p+1))"))
(use "RealLeMonPlus")
(simpreal "<-" "RealAbsUMinus")
(simpreal "RealUMinusPlus")
(simpreal "RealPlusComm")
(simpreal "RealUMinusUMinus")
(use "RealConvElim4" (pt "M"))
(use "xsConv")
(use "NatMaxUB1")
(autoreal)
(simpreal "eq")
(use "RealConvElim4" (pt "M0"))
(use "xs0Conv")
(use "NatMaxUB2")
(simpreal "<-" "RatPlusRealPlus")
(use "RatEqvToRealEq")
(use "RatEqvSym")
(use "RatPlusHalfExpPosS")
;; Proof finished.
;; (cdp)
(save "RealConvEq")

;; 9. Completeness of the real numbers
;; ===================================

;; Based on semws18/completeness.scm (by Max Zeuner) and
;; semws19/completeness.scm (by Wolfgang Boehnisch)

;; Unfolding NatToPos n is complex: because of the binary structure of
;; pos GRec is used.  Use cNatPos instead (with NatPos deanimated) and
;; NatPosExFree : all n cNatPos n=NatToPos n

(add-var-name "ass" (py "nat=>nat=>rat"))
(add-var-name "Ns" (py "nat=>pos=>nat"))

;; RealSeqApprox
(set-goal "allnc ass,Ns,xs,bs(
 allnc n xs n eqd RealConstr(ass n)(Ns n) ->
 allnc n Real(xs n) ->
 allnc n bs n=ass n(Ns n(cNatPos n)) ->
 allnc n abs(bs n+ ~(xs n))<<=(1#2**n))")
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
(set-goal "allnc ass,Ns,xs,M,bs,L(
 allnc n Real(xs n) ->
 allnc p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) ->
 allnc n xs n eqd RealConstr(ass n)(Ns n) ->
 allnc n bs n=ass n(Ns n(cNatPos n)) ->
 allnc p L p=M(PosS p)max PosS(PosS p) ->
 allnc p,n,m(L p<=n -> L p<=m -> abs(bs n+ ~(bs m))<<=(1#2**p)))")
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
(use "RealLeMonPlus")
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
(use "RealLeMonPlus")
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
(set-goal "allnc xs,M(
     allnc n Real(xs n) -> 
     allnc p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
     allnc p,q(p<=q -> M p<=M q) ->
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
(assert "exl ass allnc n ass n eqd(xs n)seq")
(intro 0 (pt "[n](xs n)seq"))
(assume "n1")
(use "InitEqD")
(assume "assEx")
(by-assume "assEx" "ass" "assDef")
;; Introduce NsDef
(assert "exl Ns allnc n Ns n eqd(xs n)mod")
(intro 0 (pt "[n](xs n)mod"))
(assume "n1")
(use "InitEqD")
(assume "NsEx")
(by-assume "NsEx" "Ns" "NsDef")
;; Introduce xsChar
(assert "allnc n xs n eqd RealConstr(ass n)(Ns n)")
(assume "n1")
(simp "assDef")
(simp "NsDef")
(cases (pt "xs n1"))
(ng #t)
(assume "as" "M1" "Useless")
(use "InitEqD")
(assume "xsChar")
;; Introduce bsDef
(assert "exl bs allnc n bs n =ass n(Ns n(cNatPos n))")
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

;; RealLimConst
(set-goal "allnc x,M(Real x -> Mon M -> RealLim([n]x)M===x)")
(assume "x" "M" "Rx" "MonM")
(intro 0)
(use "RealLimReal")
;; 6-8
(assume "n")
(use "Rx")
;; 7
(ng #t)
(assume "p" "n" "m" "Useless1" "Useless2")
(simpreal "RealPlusMinusZero")
(use "RatLeToRealLe")
(use "Truth")
(use "Rx")
;; 8
(use "MonElim")
(use "MonM")
;; 4
(use "Rx")
;; 5
(ng #t)
(assert "Cauchy(x seq)(x mod)")
(use "RealToCauchy")
(use "Rx")
(assume "CHyp")
(assert "Mon(x mod)")
(use "RealToMon")
(use "Rx")
(assume "MonHyp")
(assume "p")
(inst-with-to "CauchyElim" (pt "x seq") (pt "x mod") "CHyp" (pt "p") "Inst")
(use "Inst")
(drop "Inst")
(use "MonElim")
(use "MonHyp")
;; ?^32:p<=cNatPos(M(PosS(PosS p))max PosS(PosS(PosS p)))
(simp "NatPosExFree")
(simp "<-" "PosToNatLe")
(simp "PosToNatToPosId")
;; 35,36
;; ?^35:p<=M(PosS(PosS p))max PosS(PosS(PosS p))
(use "NatLeTrans" (pt "PosToNat(PosS(PosS(PosS p)))"))
(simp "PosToNatLe")
(use "PosLeTrans" (pt "PosS(PosS p)"))
(use "PosLeTrans" (pt "PosS p"))
(use "Truth")
(use "Truth")
(use "Truth")
(use "NatLeTrans" (pt "PosToNat(PosS(PosS(PosS p)))"))
(use "Truth")
(use "NatMaxUB2")
;; ?^36:Zero<M(PosS(PosS p))max PosS(PosS(PosS p))
(use "NatLtLeTrans" (pt "Succ Zero"))
(use "Truth")
(use "NatLeTrans" (pt "PosToNat(PosS(PosS(PosS p)))"))
(use "NatLeTrans" (pt "PosToNat(PosS(PosS p))"))
(use "NatLeTrans" (pt "PosToNat(PosS p)"))
(simp (pf "Succ Zero=PosToNat(NatToPos(Succ Zero))"))
(simp "PosToNatLe")
(use "Truth")
(simp "PosToNatToPosId")
(use "Truth")
(use "Truth")
(simp "PosToNatLe")
(use "Truth")
(simp "PosToNatLe")
(use "Truth")
;; ?^49:PosS(PosS(PosS p))<=M(PosS(PosS p))max PosS(PosS(PosS p))
(use "NatLeTrans" (pt "PosToNat(PosS(PosS(PosS p)))"))
(simp "PosToNatLe")
(use "Truth")
(use "NatMaxUB2")
;; ?^29:x mod p<=x mod(PosS p)
(use "MonElim")
(use "MonHyp")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealLimConst")

;; RealCauchyConvMod
(set-goal "allnc ass,Ns,xs,M,bs,L,x(
 allnc n xs n eqd RealConstr(ass n)(Ns n) ->
 allnc n Real(xs n) ->
 allnc p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) ->
 allnc p,q(p<=q -> M p<=M q) ->
 allnc n bs n=ass n(Ns n(cNatPos n)) ->
 allnc q L q=M(PosS q)max PosS(PosS q) ->
 x===RealConstr bs L ->
 allnc p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)))")
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
(use "RealLeMonPlus")
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
(use "RealLeMonPlus")
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
(set-goal "allnc xs,M(
     allnc n Real(xs n) -> 
     allnc p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
     allnc p,q(p<=q -> M p<=M q) ->
     allnc p,n(M p<=n -> abs(xs n+ ~(RealLim xs M))<<=(1#2**p)))")
(assume "xs" "M" "Rxs" "xsCs" "MMon")

;; Introduce assDef
(assert "exl ass allnc n ass n eqd(xs n)seq")
(intro 0 (pt "[n](xs n)seq"))
(assume "n1")
(use "InitEqD")
(assume "assEx")
(by-assume "assEx" "ass" "assDef")

;; Introduce NsDef
(assert "exl Ns allnc n Ns n eqd(xs n)mod")
(intro 0 (pt "[n](xs n)mod"))
(assume "n1")
(use "InitEqD")
(assume "NsEx")
(by-assume "NsEx" "Ns" "NsDef")

;; Introduce xsChar
(assert "allnc n xs n eqd RealConstr(ass n)(Ns n)")
(assume "n1")
(simp "assDef")
(simp "NsDef")
(cases (pt "xs n1"))
(ng #t)
(assume "as" "M1" "Useless")
(use "InitEqD")
(assume "xsChar")

;; Introduce bsDef
(assert "exl bs allnc n bs n =ass n(Ns n(cNatPos n))")
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

;; ?^43:allnc p,n(M p<=n -> abs(xs n+ ~(RealLim xs M))<<=(1#2**p))
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

;; RealLeMonLim
(set-goal "allnc xs1,M1,xs2,M2(
 allnc p,n,m(M1 p<=n -> M1 p<=m -> abs(xs1 n+ ~(xs1 m))<<=(1#2**p)) -> 
 allnc p,q(p<=q -> M1 p<=M1 q) -> 
 allnc p,n,m(M2 p<=n -> M2 p<=m -> abs(xs2 n+ ~(xs2 m))<<=(1#2**p)) -> 
 allnc p,q(p<=q -> M2 p<=M2 q) -> 
 allnc n xs1 n<<=xs2 n ->
 RealLim xs1 M1<<=RealLim xs2 M2)")
(assume "xs1" "M1" "xs2" "M2" "Cxs1M1" "MonM1" "Cxs2M2" "MonM2" "LeHyp")
(defnc "x1" "RealLim xs1 M1")
(defnc "x2" "RealLim xs2 M2")
(simp "<-" "x1Def")
(simp "<-" "x2Def")

(assert "Real x1")
(simp "x1Def")
(use "RealLimReal")
(assume "n")
(autoreal)
(use "Cxs1M1")
(use "MonM1")
(assume "Rx1")

(assert "Real x2")
(simp "x2Def")
(use "RealLimReal")
(assume "n")
(autoreal)
(use "Cxs2M2")
(use "MonM2")
(assume "Rx2")

(use "RealLeAllPlusToLe")
(autoreal)
(assume "p")
;; ?^48:x1<<=x2+(1#2**p)
(use "RealLePlusR")
(autoreal)
;; ?^42:~x2+x1<<=(1#2**p)

;; Pick a large enough n
(defnc "n" "M1(PosS p)max M2(PosS p)")

(assert "~(xs2 n)+(xs1 n)<<=0")
(use "RealLePlusRInv")
(autoreal)
(simpreal "RealPlusZero")
(use "LeHyp")
(autoreal)
(assume "MidLeZero")

(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeTrans" (pt "(~x2+(xs2 n))+(~(xs1 n)+x1)"))
;; 60,61
;; ?^60:~x2+x1<<= ~x2+xs2 n+(~(xs1 n)+x1)
(simpreal "<-" "RealPlusAssoc")
(use "RealLeMonPlus")
(use "RealLeRefl")
(autoreal)
(simpreal "RealPlusAssoc")
(use "RealLeTrans" (pt "0+x1"))
(simpreal "RealZeroPlus")
(use "RealLeRefl")
(autoreal)
(use "RealLeMonPlus")
;; ?^78:0<<=xs2 n+ ~(xs1 n)
(simpreal "RealPlusComm")
(use "RealLePlusLInv")
(autoreal)
(simpreal "RealPlusZero")
(use "LeHyp")
(autoreal)
(use "RealLeRefl")
(autoreal)
;; ?^61:~x2+xs2 n+(~(xs1 n)+x1)<<=RealPlus(1#2**PosS p)(1#2**PosS p)
(use "RealLeMonPlus")
;; 90,91
;; ?^90:~x2+xs2 n<<=(1#2**PosS p)
(simpreal "RealPlusComm")
(use "RealLeTrans" (pt "abs(xs2 n+ ~x2)"))
(use "RealLeAbsId")
(autoreal)
(simp "x2Def")
(use "RealComplete")
(assume "n1")
(autoreal)
(use "Cxs2M2")
(use "MonM2")
(simp "nDef")
(use "NatMaxUB2")
(autoreal)
;; ?^91:~(xs1 n)+x1<<=(1#2**PosS p)
(simpreal "RealPlusComm")
(use "RealLeTrans" (pt "abs(x1+ ~(xs1 n))"))
(use "RealLeAbsId")
(autoreal)
(simpreal "RealAbsPlusUMinus")
(simp "x1Def")
(use "RealComplete")
(assume "n1")
(autoreal)
(use "Cxs1M1")
(use "MonM1")
(simp "nDef")
(use "NatMaxUB1")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeMonLim")

;; As a corollary we obtain RealLimCompat.  We use RealLeAntiSym and
;; that <<= follows from ===, RealLeRefl

;; RealLimCompat
(set-goal "allnc xs1,M1,xs2,M2(
 allnc p,n,m(M1 p<=n -> M1 p<=m -> abs(xs1 n+ ~(xs1 m))<<=(1#2**p)) -> 
 allnc p,q(p<=q -> M1 p<=M1 q) -> 
 allnc p,n,m(M2 p<=n -> M2 p<=m -> abs(xs2 n+ ~(xs2 m))<<=(1#2**p)) -> 
 allnc p,q(p<=q -> M2 p<=M2 q) -> 
 allnc n xs1 n===xs2 n ->
 RealLim xs1 M1===RealLim xs2 M2)")
(assume "xs1" "M1" "xs2" "M2" "Cxs1M1" "MonM1" "Cxs2M2" "MonM2" "EqHyp")
(use "RealLeAntiSym")
;; 3,4
(use "RealLeMonLim")
(use "Cxs1M1")
(use "MonM1")
(use "Cxs2M2")
(use "MonM2")
;; ?^9:allnc n xs1 n<<=xs2 n
(assume "n")
(inst-with-to "EqHyp" (pt "n") "nEqHyp")
(simpreal "nEqHyp")
(use "RealLeRefl")
(autoreal)
;; ?^4:RealLim xs2 M2<<=RealLim xs1 M1
(use "RealLeMonLim")
(use "Cxs2M2")
(use "MonM2")
(use "Cxs1M1")
(use "MonM1")
;; ?^19:allnc n xs2 n<<=xs1 n
(assume "n")
(inst-with-to "EqHyp" (pt "n") "nEqHyp")
(simpreal "nEqHyp")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLimCompat")

;; CauchyExt
(set-goal "allnc as1,M1(
 Cauchy as1 M1 ->
 allnc as2,M2(allnc n as1 n eqd as2 n -> allnc p M1 p=M2 p -> Cauchy as2 M2))")
(assume "as1" "M1" "Cas1M1")
(elim "Cas1M1")
(assume "as2" "M2" "as2M2Prop" "as3" "M3" "as2=as3" "M2=M3")
(intro 0)
(assume "p" "n" "m")
(simp "<-" "M2=M3")
(simp "<-" "as2=as3")
(simp "<-" "as2=as3")
(use "as2M2Prop")
;; Proof finished.
;; (cdp)
(save "CauchyExt")

;; MonExt
(set-goal "allnc M1(Mon M1 -> allnc M2(allnc p M1 p=M2 p -> Mon M2))")
(assume "M1" "MonM1")
(elim "MonM1")
(assume "M2" "MonM2" "M3" "M2=M3")
(intro 0)
(assume "p" "q")
(simp "<-" "M2=M3")
(simp "<-" "M2=M3")
(use "MonM2")
;; Proof finished.
;; (cdp)
(save "MonExt")

;; RealExt
(set-goal "allnc x1(Real x1 -> 
 allnc x2(allnc n x1 seq n eqd x2 seq n -> 
          allnc p x1 mod p=x2 mod p -> Real x2))")
(assume "x1" "Rx1")
(elim "Rx1")
(assume "x2" "Cx2" "Mx2" "x3" "as2=as3" "M2=M3")
(intro 0)
;; 5,6
(use "CauchyExt" (pt "x2 seq") (pt "x2 mod"))
(use "Cx2")
(use "as2=as3")
(use "M2=M3")
;; 6
(use "MonExt" (pt "x2 mod"))
(use "Mx2")
(use "M2=M3")
;; Proof finished.
;; (cdp)
(save "RealExt")

;; RealConstrExt
(set-goal "allnc as1,M1,as2,M2(
 allnc n as1 n eqd as2 n -> allnc p M1 p eqd M2 p ->
 EqPReaNc(RealConstr as1 M1)(RealConstr as2 M2))")
(assume "as1" "M1" "as2" "M2" "as1=as2" "M1=M2")
(intro 0)
;; 3,4
;;   {as1}  {M1}  {as2}  {M2}  as1=as2:
;;     allnc n as1 n eqd as2 n
;;   M1=M2:allnc p M1 p eqd M2 p
;; ----------------------------------------------------------------------------
;; ?^3:allnc n^,n^0(EqPNatNc n^ n^0 -> EqPRatNc(as1 n^)(as2 n^0))
(assume "n^1" "n^2" "n1=n2")
(simp "<-" (pf "n^1 eqd n^2"))
(assert "allnc n^(TotalNatNc n^ -> as1 n^ eqd as2 n^)")
(fold-alltotal)
(use "as1=as2")
;; Assertion proved.
(assume "Assertion")
(simp "<-" "Assertion")
;; ?^12:EqPRatNc(as1 n^1)(as1 n^1)
(use "EqPRatRefl")
;; ?^14:TotalRat(as1 n^1)
(assert "allnc n^(TotalNat n^ -> TotalRat(as1 n^))")
(fold-alltotal)
(assume "n")
(use "RatTotalVar")
;; Assertion proved.
(assume "Assertion2")
(use "Assertion2")
(use "EqPNatToTotalLeft" (pt "n^2"))
(use "n1=n2")
(use "EqPNatToTotalLeft" (pt "n^2"))
(use "n1=n2")
(use "EqPNatNcToEqD")
(use "n1=n2")
;; ?^4:allnc p^,p^0(EqPPosNc p^ p^0 -> EqPNatNc(M1 p^)(M2 p^0))
(assume "p^1" "p^2" "p1=p2")
(simp "<-" (pf "p^1 eqd p^2"))
(assert "allnc p^(TotalPosNc p^ -> M1 p^ eqd M2 p^)")
(fold-alltotal)
(use "M1=M2")
;; Assertion proved.
(assume "Assertion")
(simp "<-" "Assertion")
;; ?^31:EqPNatNc(M1 p^1)(M1 p^1)
(use "EqPNatRefl")
;; ?^33:TotalNat(M1 p^1)
(assert "allnc p^(TotalPos p^ -> TotalNat(M1 p^))")
(fold-alltotal)
(assume "p")
(use "NatTotalVar")
;; Assertion proved.
(assume "Assertion2")
(use "Assertion2")
(use "EqPPosToTotalLeft" (pt "p^2"))
(use "p1=p2")
(use "EqPPosToTotalLeft" (pt "p^2"))
(use "p1=p2")
(use "EqPPosToEqD")
(use "p1=p2")
;; Proof finished.
;; (cdp)
(save "RealConstrExt")

;; RealLimExt
(set-goal (rename-variables (term-to-pure-extnc-formula (pt "RealLim"))))

;; ?^1:allnc xs^,xs^0(
;;      allnc n^,n^0(EqPNatNc n^ n^0 -> EqPReaNc(xs^ n^)(xs^0 n^0)) -> 
;;      allnc M^,M^0(
;;       allnc p^,p^0(EqPPosNc p^ p^0 -> EqPNatNc(M^ p^)(M^0 p^0)) -> 
;;       EqPReaNc(RealLim xs^ M^)(RealLim xs^0 M^0)))

(assume "xs^1" "xs^2" "xs1=xs2" "M^1" "M^2" "M1=M2")
(intro 0)
;; 3,4
;; ?^3:allnc n^,n^0(
;;      EqPNatNc n^ n^0 -> 
;;      EqPRatNc(([n](xs^1 n)seq((xs^1 n)mod(cNatPos n)))n^)
;;      (([n](xs^2 n)seq((xs^2 n)mod(cNatPos n)))n^0))
(ng #t)
;; ?^5:allnc n^,n^0(
;;      EqPNatNc n^ n^0 -> 
;;      EqPRatNc((xs^1 n^)seq((xs^1 n^)mod(cNatPos n^)))
;;      ((xs^2 n^0)seq((xs^2 n^0)mod(cNatPos n^0))))
(assume "n^1" "n^2" "n1=n2")
(inst-with-to "xs1=xs2" (pt "n^1") (pt "n^2") "n1=n2" "xs1n1=xs2n2")
(elim "xs1n1=xs2n2")
(ng #t)
;; ?^10:allnc as^,as^0(
;;       allnc n^,n^0(EqPNatNc n^ n^0 -> EqPRatNc(as^ n^)(as^0 n^0)) -> 
;;       allnc M^,M^0(
;;        allnc p^,p^0(EqPPosNc p^ p^0 -> EqPNatNc(M^ p^)(M^0 p^0)) -> 
;;        EqPRatNc(as^(M^(cNatPos n^1)))(as^0(M^0(cNatPos n^2)))))
(assume "as^1" "as^2" "as1=as2" "M^3" "M^4" "M3=M4")
(use "as1=as2")
(use "M3=M4")
(inst-with-to "EqPNatNcToEqD" (pt "n^1") (pt "n^2") "n1=n2" "Inst")
(simp "<-" "Inst")
(use "EqPPosRefl")
(use "cNatPosTotal")
(use "EqPNatToTotalLeft" (pt "n^2"))
(use "n1=n2")
;; ?^4:allnc p^,p^0(
;;      EqPPosNc p^ p^0 -> 
;;      EqPNatNc(([p]M^1(PosS p)max PosS(PosS p))p^)
;;      (([p]M^2(PosS p)max PosS(PosS p))p^0))
(ng #t)
(assume "p^1" "p^2" "p1=p2")
(assert "EqPPosNc(PosS p^1)(PosS p^2)")
(use "PosSEqP")
(use "p1=p2")
;; Assertion proved.
(assume "Sp1=Sp2")
(assert "EqPPosNc(PosS(PosS p^1))(PosS(PosS p^2))")
(use "PosSEqP")
(use "Sp1=Sp2")
;; Assertion proved.
(assume "SSp1=SSp2")
(inst-with-to "M1=M2" (pt "PosS p^1") (pt "PosS p^2") "Sp1=Sp2" "M1Sp1=M2Sp2")
(inst-with-to "EqPNatNcToEqD" (pt "M^1(PosS p^1)") (pt "M^2(PosS p^2)")
	      "M1Sp1=M2Sp2" "Inst")
(simp "<-" "Inst")
(simp "<-" (pf "p^1 eqd p^2"))
(use "EqPNatRefl")
(use "NatMaxTotal")
(use "EqPNatToTotalLeft" (pt "M^2(PosS p^2)"))
(use "M1Sp1=M2Sp2")
(use "PosToNatTotal")
(use "EqPPosToTotalLeft" (pt "PosS(PosS p^2)"))
(use "SSp1=SSp2")
(use "EqPPosToEqD")
(use "p1=p2")
;; Proof finished.
;; (cdp)
(save "RealLimExt")

;; RealConstrPureExt
(set-goal (rename-variables (term-to-pure-extnc-formula (pt "RealConstr"))))

;; ?^1:allnc as^,as^0(
;;      allnc n^,n^0(EqPNatNc n^ n^0 -> EqPRatNc(as^ n^)(as^0 n^0)) -> 
;;      allnc M^,M^0(
;;       allnc p^,p^0(EqPPosNc p^ p^0 -> EqPNatNc(M^ p^)(M^0 p^0)) -> 
;;       EqPReaNc(RealConstr as^ M^)(RealConstr as^0 M^0)))

(assume "as^1" "as^2" "as1=as2" "M^1" "M^2" "M1=M2")
(intro 0)
(use "as1=as2")
(use "M1=M2")
;; Proof finished.
;; (cdp)
(save "RealConstrPureExt")

;; RealSeqSubToEq
(set-goal "allnc as1,M1,as2,M2,nat=>nat(
     Real(RealConstr as1 M1) -> 
     Real(RealConstr as2 M2) -> 
     allnc n n<=nat=>nat n -> 
     allnc n as2 n==as1(nat=>nat n) -> RealConstr as1 M1===RealConstr as2 M2)")
(assume "as1" "M1" "as2" "M2" "nat=>nat" "Rx1" "Rx2" "id<=f" "SeqSubHyp")
(use "RealEqChar2")
(use "Rx1")
(use "Rx2")
(inst-with-to "RealConstrToCauchy" (pt "as1") (pt "M1") "Rx1" "Cx1")
(inst-with-to "CauchyElim" (pt "as1") (pt "M1") "Cx1" "x1Hyp")
(assume "p")
(intro 0 (pt "M1 p"))
(assume "n" "nBd")
(simprat "SeqSubHyp")
(use "x1Hyp")
(use "nBd")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "id<=f")
;; Proof finished
;; (cdp)
(save "RealSeqSubToEq")

;; RealSeqSubToEqRealConstrFree
(set-goal "allnc x1,x2,nat=>nat(
     Real x1 -> 
     Real x2 -> 
     allnc n n<=nat=>nat n -> 
     allnc n x2 seq n==x1 seq(nat=>nat n) -> x1===x2)")
(assume "x1" "x2" "nat=>nat" "Rx1" "Rx2" "id<=f" "SeqSubHyp")
(use "RealEqChar2RealConstrFree")
(use "Rx1")
(use "Rx2")
(inst-with-to "RealToCauchy" (pt "x1") "Rx1" "Cx1seq")
(inst-with-to "CauchyElim" (pt "x1 seq") (pt "x1 mod") "Cx1seq" "x1Hyp")
(assume "p")
(intro 0 (pt "x1 mod p"))
(assume "n" "nBd")
(simprat "SeqSubHyp")
(use "x1Hyp")
(use "nBd")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "id<=f")
;; Proof finished
;; (cdp)
(save "RealSeqSubToEqRealConstrFree")

;; RatCauchyConvModRealConstrFree
(set-goal
 "allnc x,p,n(Real x -> x mod p<=n -> abs(x seq n+ ~x)<<=(1#2**p))")
(cases)
(assume "as" "M" "p" "n" "Rx" "nBd")
(use "RatCauchyConvMod")
(use "Rx")
(use "nBd")
;; Proof finished.
(save "RatCauchyConvModRealConstrFree")

;; 2020-11-23.  We study the completion of real numbers.

(add-var-name "v" (py "(nat=>rea)yprod(pos=>nat)"))

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

(add-ids
 (list (list "RCplPt" (make-arity (py "(nat=>rea)yprod(pos=>nat)"))))
 '("allnc v(
   allnc n Real(lft v n) ->  RCauchy(lft v)(rht v) -> Mon(rht v) -> RCplPt v)"
   "RCplPtIntro"))

;; RCplPtToR
(set-goal "allnc v(RCplPt v -> allnc n Real(lft v n))")
(assume "v" "Pv")
(elim "Pv")
(search)
;; Proof finished.
;; (cdp)
(save "RCplPtToR")

;; RCplPtToRCauchy
(set-goal "allnc v(RCplPt v -> RCauchy(lft v)(rht v))")
(assume "v" "Pv")
(elim "Pv")
(search)
;; Proof finished.
;; (cdp)
(save "RCplPtToRCauchy")

;; RCplPtToMon
(set-goal "allnc v(RCplPt v -> Mon(rht v))")
(assume "v" "Pv")
(elim "Pv")
(search)
;; Proof finished.
;; (cdp)
(save "RCplPtToMon")

;; The following variants will be useful, because their heads will be
;; more often of the form of a given goal.

;; RCplPtPairToR
(set-goal "allnc xs,M(RCplPt(xs pair M) -> allnc n Real(xs n))")
(assume "xs" "M" "Pv")
(use-with "RCplPtToR" (pt "xs pair M") "Pv")
;; Proof finished.
;; (cdp)
(save "RCplPtPairToR")

;; RCplPtPairToRCauchy
(set-goal "allnc xs,M(RCplPt(xs pair M) -> RCauchy xs M)")
(assume "xs" "M" "Pv")
(use-with "RCplPtToRCauchy" (pt "xs pair M") "Pv")
;; Proof finished.
;; (cdp)
(save "RCplPtPairToRCauchy")

;; RCplPtPairToMon
(set-goal "allnc xs,M(RCplPt(xs pair M) -> Mon M)")
(assume "xs" "M" "Pv")
(use-with "RCplPtToMon" (pt "xs pair M") "Pv")
;; Proof finished.
;; (cdp)
(save "RCplPtPairToMon")

;; RCplPlusRCpl
(set-goal "allnc v1,v2(RCplPt v1 -> RCplPt v2 ->
 RCplPt(([n]lft v1 n+lft v2 n)pair([p]rht v1(PosS p)max rht v2(PosS p))))")
(cases)
(assume "xs1" "M1")
(cases)
(assume "xs2" "M2")
(ng #t)
;; ?^6:RCplPt(xs1 pair M1) -> 
;;     RCplPt(xs2 pair M2) -> 
;;     RCplPt(([n]xs1 n+xs2 n)pair([p]M1(PosS p)max M2(PosS p)))
(assume "Pv1" "Pv2")

(inst-with-to "RCplPtPairToR" (pt "xs1") (pt "M1") "Pv1" "Rxs1")
(inst-with-to "RCplPtPairToRCauchy" (pt "xs1") (pt "M1") "Pv1" "RCxs1M1")
(inst-with-to "RCplPtPairToMon" (pt "xs1") (pt "M1") "Pv1" "MonM1")
(inst-with-to "RCplPtPairToR" (pt "xs2") (pt "M2") "Pv2" "Rxs2")
(inst-with-to "RCplPtPairToRCauchy" (pt "xs2") (pt "M2") "Pv2" "RCxs2M2")
(inst-with-to "RCplPtPairToMon" (pt "xs2") (pt "M2") "Pv2" "MonM2")

(intro 0)
;; 20-22
(ng #t)
;; ?^23:allnc n Real(xs1 n+xs2 n)
(assume "n")
(autoreal)
;; 21
(ng #t)
;; ?^25:RCauchy([n]xs1 n+xs2 n)([p]M1(PosS p)max M2(PosS p))
(intro 0)
(ng #t)
;; ?^27:allnc p,n,m(
;;       M1(PosS p)max M2(PosS p)<=n -> 
;;       M1(PosS p)max M2(PosS p)<=m -> 
;;       abs(xs1 n+xs2 n+ ~(xs1 m+xs2 m))<<=(1#2**p))
(assume "p" "n" "m" "nBd" "mBd")

(simpreal (pf "abs(xs1 n+xs2 n+ ~(xs1 m+xs2 m))===
               abs(xs1 n+ ~(xs1 m)+(xs2 n+ ~(xs2 m)))"))
;; 29,30
(use "RealLeTrans" (pt "abs(xs1 n+ ~(xs1 m))+abs(xs2 n+ ~(xs2 m))"))
(use "RealLeAbsPlus")
(autoreal)
(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlus")
;; 36,37
;; ?^36:abs(xs1 n+ ~(xs1 m))<<=(1#2**PosS p)
(use "RCauchyElim" (pt "M1"))
(use "RCxs1M1")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB1")
(use "mBd")
;; ?^37:abs(xs2 n+ ~(xs2 m))<<=(1#2**PosS p)
(use "RCauchyElim" (pt "M2"))
(use "RCxs2M2")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB2")
(use "nBd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB2")
(use "mBd")

;; 30:abs(xs1 n+xs2 n+ ~(xs1 m+xs2 m))===abs(xs1 n+ ~(xs1 m)+(xs2 n+ ~(xs2 m)))
(use "RealAbsCompat")
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

;; ?^22:Mon(rht(([n]xs1 n+xs2 n)pair([p]M1(PosS p)max M2(PosS p))))
(ng #t)
;; ?^80:Mon([p]M1(PosS p)max M2(PosS p))
(intro 0)
(ng #t)
(assume "p" "q" "p<=q")
(use "NatLeMonMax")
(use "MonElim")
(use "MonM1")
(use "p<=q")
(use "MonElim")
(use "MonM2")
(use "p<=q")
;; Proof finished.
;; (cdp)
(save "RCplPlusRCpl")

;; 2020-11-26.  For x1+x2===x use
;; (pp "RealEqIntro1")
;; all x,y(Real x -> Real y -> all p abs(x+ ~y)<<=(1#2**p) -> x===y)

;; Insert approximations (xs1 n) (xs2 n) (xs1 n+xs2 n) of x1,x2,x via
;; (pp "RealLeAbsMinus")
;; all x,y,z(Real x -> Real y -> Real z -> abs(x+ ~y)<<=abs(x+ ~z)+abs(z+ ~y))

; RealLimPlusRealLim
(set-goal "allnc xs1,M1,xs2,M2(
 RCplPt(xs1 pair M1) ->
 RCplPt(xs2 pair M2) ->
 RealLim xs1 M1+RealLim xs2 M2===
 RealLim([n]xs1 n+xs2 n)([p]M1(PosS p)max M2(PosS p)))")
(assume "xs1" "M1" "xs2" "M2" "Pv1" "Pv2")

(inst-with-to "RCplPtPairToR" (pt "xs1") (pt "M1") "Pv1" "Rxs1")
(inst-with-to "RCplPtPairToRCauchy" (pt "xs1") (pt "M1") "Pv1" "Cxs1M1")
(inst-with-to "RCplPtPairToMon" (pt "xs1") (pt "M1") "Pv1" "MonM1")
(inst-with-to "RCplPtPairToR" (pt "xs2") (pt "M2") "Pv2" "Rxs2")
(inst-with-to "RCplPtPairToRCauchy" (pt "xs2") (pt "M2") "Pv2" "Cxs2M2")
(inst-with-to "RCplPtPairToMon" (pt "xs2") (pt "M2") "Pv2" "MonM2")

(inst-with-to "RCplPlusRCpl" (pt "(xs1 pair M1)") (pt "(xs2 pair M2)")
	      "Pv1" "Pv2" "Pv")

(defnc "x1" "RealLim xs1 M1")
(defnc "x2" "RealLim xs2 M2")
(defnc "x" "RealLim([n]xs1 n+xs2 n)([p]M1(PosS p)max M2(PosS p))")

(simp "<-" "x1Def")
(simp "<-" "x2Def")
(simp "<-" "xDef")

(assert "Real x1")
(simp "x1Def")
(use "RealLimReal")
(use "Rxs1")
(use "RCauchyElim")
(use "Cxs1M1")
(use "MonElim")
(use "MonM1")
(assume "Rx1")

(assert "Real x2")
(simp "x2Def")
(use "RealLimReal")
(use "Rxs2")
(use "RCauchyElim")
(use "Cxs2M2")
(use "MonElim")
(use "MonM2")
(assume "Rx2")

(assert "Real x")
(simp "xDef")
(use "RealLimReal")
;; 62-64
(assume "n")
(ng #t)
(autoreal)
;; 63
(ng #t)
(assume "p" "n" "m" "nBd" "mBd")
;; ?^68:abs(xs1 n+xs2 n+ ~(xs1 m+xs2 m))<<=(1#2**p)

(simpreal (pf "abs(xs1 n+xs2 n+ ~(xs1 m+xs2 m))===
               abs(xs1 n+ ~(xs1 m)+(xs2 n+ ~(xs2 m)))"))
;; 69,70
(use "RealLeTrans" (pt "abs(xs1 n+ ~(xs1 m))+abs(xs2 n+ ~(xs2 m))"))
(use "RealLeAbsPlus")
(autoreal)
(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlus")
;; 76,77
;; ?^76:abs(xs1 n+ ~(xs1 m))<<=(1#2**PosS p)
(use "RCauchyElim" (pt "M1"))
(use "Cxs1M1")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB1")
(use "mBd")
;; ?^77:abs(xs2 n+ ~(xs2 m))<<=(1#2**PosS p)
(use "RCauchyElim" (pt "M2"))
(use "Cxs2M2")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB2")
(use "nBd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB2")
(use "mBd")

;; 70:abs(xs1 n+xs2 n+ ~(xs1 m+xs2 m))===abs(xs1 n+ ~(xs1 m)+(xs2 n+ ~(xs2 m)))
(use "RealAbsCompat")
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

;; 64
(ng #t)
(assume "p" "q" "p<=q")
(use "NatLeMonMax")
(use "MonElim")
(use "MonM1")
(use "p<=q")
(use "MonElim")
(use "MonM2")
(use "p<=q")
;; Assertion proved.
(assume "Rx")

;; ?^128:x1+x2===x
(use "RealEqIntro1")
(autoreal)
;; ?^131:all p abs(x1+x2+ ~x)<<=(1#2**p)

;; We need approximations (xs1 n) (xs2 n) (xs1 n+xs2 n) of x1,x2,x
;; to apply RealLeAbsMinus .
(assume "p")
(defnc "n" "M1(PosS(PosS p))max M2(PosS(PosS p))")

(assert "abs(xs1 n+ ~x1)<<=(1#2**PosS(PosS p))")
(simp "x1Def")
(use "RealComplete")
(use "Rxs1")
(use "RCauchyElim")
(use "Cxs1M1")
(use "MonElim")
(use "MonM1")
(simp "nDef")
(use "NatMaxUB1")
;; Assertion proved.
(assume "LimApprox1")

(assert "abs(xs2 n+ ~x2)<<=(1#2**PosS(PosS p))")
(simp "x2Def")
(use "RealComplete")
(use "Rxs2")
(use "RCauchyElim")
(use "Cxs2M2")
(use "MonElim")
(use "MonM2")
(simp "nDef")
(use "NatMaxUB2")
;; Assertion proved.
(assume "LimApprox2")

(assert "abs(([n]xs1 n+xs2 n)n+ ~x)<<=(1#2**PosS p)")
(simp "xDef")
(use "RealComplete")
;; 165-167
(ng #t)
(assume "n1")
(autoreal)
;; 166
(use "RCauchyElim")
(use "RCplPtPairToRCauchy")
(use "Pv")
;; 167
(use "MonElim")
;; ?^173:Mon([p]M1(PosS p)max M2(PosS p))
(intro 0)
(assume "p1" "q1" "p1<=q1")
(ng #t)
(use "NatLeMonMax")
(use "MonElim")
(use "MonM1")
(use "p1<=q1")
(use "MonElim")
(use "MonM2")
(use "p1<=q1")
;; 168
(simp "nDef")
(use "Truth")
(ng #t)
;; Assertion proved.
(assume "LimApprox")

;; ?^185:abs(x1+x2+ ~x)<<=(1#2**p)
(use "RealLeTrans" (pt "abs(x1+x2+ ~(xs1 n+xs2 n))+abs(xs1 n+xs2 n+ ~x)"))
(use "RealLeAbsMinus")
(autoreal)
(use "RealLeTrans" (pt "RealPlus(1#2**PosS p)(1#2**PosS p)"))
(use "RealLeMonPlus")
;; 193,194
;; ?^193:abs(x1+x2+ ~(xs1 n+xs2 n))<<=(1#2**PosS p)
(simpreal (pf "x1+x2+ ~(xs1 n+xs2 n)===x1+ ~(xs1 n)+(x2+ ~(xs2 n))"))
;; 195,196
;; ?^195:abs(x1+ ~(xs1 n)+(x2+ ~(xs2 n)))<<=(1#2**PosS p)
(use "RealLeTrans" (pt "abs(x1+ ~(xs1 n))+abs(x2+ ~(xs2 n))"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeTrans" (pt "RealPlus(1#2**PosS(PosS p))(1#2**PosS(PosS p))"))
(use "RealLeMonPlus")
;; 203,204
;; ?^203:abs(x1+ ~(xs1 n))<<=(1#2**PosS(PosS p))
(simpreal "RealAbsPlusUMinus")
(use "LimApprox1")
(autoreal)
;; ?^204:abs(x2+ ~(xs2 n))<<=(1#2**PosS(PosS p))
(simpreal "RealAbsPlusUMinus")
(use "LimApprox2")
(autoreal)
;; ?^202:RealPlus(1#2**PosS(PosS p))(1#2**PosS(PosS p))<<=(1#2**PosS p)
(simpreal "RealPlusHalfExpPosS")
(use "RatLeToRealLe")
(use "Truth")

;; ?^196:x1+x2+ ~(xs1 n+xs2 n)===x1+ ~(xs1 n)+(x2+ ~(xs2 n))
(simpreal "RealUMinusPlus")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)

;; ?^225:x2+(~(xs1 n)+ ~(xs2 n))=== ~(xs1 n)+(x2+ ~(xs2 n))
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")

;; ?^235:x2+ ~(xs1 n)=== ~(xs1 n)+x2
(use "RealPlusComm")
(autoreal)
(use "RealEqRefl")
(autoreal)

;; ?^194:abs(xs1 n+xs2 n+ ~x)<<=(1#2**PosS p)
(use "LimApprox")

;; ?^192:RealPlus(1#2**PosS p)(1#2**PosS p)<<=(1#2**p)
(simpreal "RealPlusHalfExpPosS")
(use "RatLeToRealLe")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealLimPlusRealLim")

(remove-var-name "ns" "ass" "Ns" "v")
