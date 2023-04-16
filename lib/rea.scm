;; 2023-04-16.  rea.scm

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
(add-var-name "M" "N" "K" (py "pos=>nat"))

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
(fold-alltotal)
(cases)
(assume "as" "M")
(fold-alltotal)
(assume "n")
(use "RatTotalVar")
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
(fold-alltotal)
(cases)
(assume "as" "M")
(fold-alltotal)
(assume "p")
(use "NatTotalVar")
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
(add-program-constant "RealExp" (py "rea=>nat=>rea"))
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

(add-computation-rules "RealPos(RealConstr as M)p" "(1#2**p)<=as(M(PosS p))")

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
(fold-alltotal)
(cases)
(assume "as" "M")
(fold-alltotal)
(assume "p")
(use "BooleTotalVar")
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
 "RealPos(RealConstr bs N+ ~(RealConstr as M))p")

;; Rules for RealUMinus

(add-computation-rules
 "~(RealConstr as M)" "RealConstr([n]~(as n))M")

;; RealUMinusTotal
(set-totality-goal "RealUMinus")
(fold-alltotal)
(cases)
(assume "as" "M")
(use "ReaTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for RealPlus

(add-computation-rules
 "RealConstr as M+RealConstr bs N"
 "RealConstr([n]as n+bs n)([p]M(PosS p)max N(PosS p))")

;; RealPlusTotal
(set-totality-goal "RealPlus")
(fold-alltotal)
(cases)
(assume "as" "M")
(fold-alltotal)
(cases)
(assume "bs" "N")
(use "ReaTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; RealLtTotal

(set-totality-goal "RealLt")
(fold-alltotal)
(cases)
(assume "as" "M")
(fold-alltotal)
(cases)
(assume "bs" "N")
(fold-alltotal)
(assume "p")
(ng #t)
(use "BooleTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for RealMinus

(add-computation-rules
 "x-y" "x+ ~y")

(set-totality-goal "RealMinus")
(fold-alltotal)
(cases)
(assume "as" "M")
(fold-alltotal)
(cases)
(assume "bs" "N")
(use "ReaTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for RealUDiv
(add-computation-rules
 "RealUDiv(RealConstr as M)q" "RealConstr([n]RatUDiv(as n))([p]M(2*PosS q+p))")

;; RealUDivTotal
(set-totality-goal "RealUDiv")
(fold-alltotal)
(cases)
(assume "as" "M")
(fold-alltotal)
(assume "p")
(use "ReaTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for RealAbs

(add-computation-rules
 "abs(RealConstr as M)" "RealConstr([n]abs(as n))M")

;; RealAbsTotal
(set-totality-goal "RealAbs")
(fold-alltotal)
(cases)
(assume "as" "M")
(use "ReaTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for RealTimes are postponed.
;; They require the Archimedian property, in the form of a pconst
;; RealBd.  We will define an auxiliary function ListNatMax, then
;; RealBd and finally the computation rule for RealTimes.  Its
;; properties require the predicate Cauchy.

;; Rules for RealMax : rea=>rea=>rea

(add-computation-rules
 "RealConstr as M max RealConstr bs N"
 "RealConstr([n]as n max bs n)([p]M p max N p)")

;; RealMaxTotal
(set-totality-goal "RealMax")
(fold-alltotal)
(cases)
(assume "as1" "M1")
(fold-alltotal)
(cases)
(assume "as2" "M2")
(use "ReaTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for RealMin : rea=>rea=>rea

(add-computation-rules
 "RealConstr as M min RealConstr bs N"
 "RealConstr([n]as n min bs n)([p]M p max N p)")

;; RealMinTotal
(set-totality-goal "RealMin")
(fold-alltotal)
(cases)
(assume "as1" "M1")
(fold-alltotal)
(cases)
(assume "as2" "M2")
(use "ReaTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

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

;; CauchyChar1
(set-goal "all as,M(Cauchy as M ->
 all p,n,m(M p<=n -> M p<=m -> as n<=as m+(1#2**p)))")
(assume "as" "M" "CasM" "p" "n" "m" "nBd" "mBd")
(use "RatLePlusR")
(simp "RatPlusComm")
(use "RatLeTrans" (pt "abs(as n+ ~(as m))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "nBd")
(use "mBd")
;; Proof finished.
;; (cdp)
(save "CauchyChar1")

;; CauchyChar2
(set-goal "all as,M(all p,n,m(M p<=n -> M p<=m -> as n<=as m+(1#2**p)) ->
 Cauchy as M)")
(assume "as" "M" "AllHyp")
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(use "RatLeAbs")
;; 5,6
(simp "RatPlusComm")
(use "RatLePlusRInv")
(use "AllHyp")
(use "nBd")
(use "mBd")
;; 6
(ng #t)
(use "RatLePlusRInv")
(use "AllHyp")
(use "mBd")
(use "nBd")
;; Proof finished.
;; (cdp)
(save "CauchyChar2")

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

;; Computation rules for RealTimes.  

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
(fold-alltotal)
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
(fold-alltotal)
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
(fold-alltotal)
(assume "p")
(fold-alltotal)
(assume "q")
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save "cRatLeBoundTotal")

;; Every real has an upper bound, that is the reals are Archimedian ordered.

;; 2021-10-15.  NatPos NatPosExfree cNatPosTotal moved to lib/pos.scm
;; ;; Use cNatPos instead of the pconst NatToPos to block unwanted unfoldings

;; ;; NatPos
;; (set-goal "all n exl p p=NatToPos n")
;; (assume "n")
;; (intro 0 (pt "NatToPos n"))
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "NatPos")

;; (animate "NatPos")

;; ;; NatPosExFree
;; (set-goal "all n cNatPos n=NatToPos n")
;; (assume "n")
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "NatPosExFree")

;; (deanimate "NatPos")

;; (set-totality-goal "cNatPos")
;; (fold-alltotal)
;; (assume "n")
;; (use "PosTotalVar")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "cNatPosTotal")

;; 2021-02-05.  
;; Use cRBd instead of the pconst RealBd to block unwanted unfoldings

(add-program-constant "RealBd" (py "(nat=>rat)=>(pos=>nat)=>nat") t-deg-zero)

;; It might be more uniform to take rea=>nat as type.  Postponed, but
;; some preliminary code is in temp/librseq8.scm, for RealBound

(add-computation-rules
 "RealBd as M"
 "Succ(ListNatMax(cRatLeAbsBound map as fbar Succ(M 1)))")

(set-totality-goal "RealBd")
(fold-alltotal)
(assume "as")
(fold-alltotal)
(assume "M")
(ng #t)
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; RBd
(set-goal "all as,M(Cauchy as M -> exl n n=RealBd as M)")
(assume "as" "M" "CasM")
(intro 0 (pt "RealBd as M"))
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RBd")

(animate "RBd")

;; RBdExFree
(set-goal "all as,M(Cauchy as M -> cRBd as M=RealBd as M)")
(assume "as" "M" "CasM")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RBdExFree")

(deanimate "RBd")

(set-totality-goal "cRBd")
(fold-alltotal)
(assume "as")
(fold-alltotal)
(assume "M")
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Now we can use cRBd where we had used RealBd before.

;; (add-program-constant "RealTimes" (py "rea=>rea=>rea"))

(add-computation-rules
 "(RealConstr as M)*(RealConstr bs N)"
 "RealConstr([n]as n*bs n)
            ([p]M(PosS(p+cNatPos(cRBd bs N)))max
                N(PosS(p+cNatPos(cRBd as M))))")

(animate "RBd")

;; RealBdProp
(set-goal "all as,M(Cauchy as M -> all n abs(as n)<=2**cRBd as M)")
(assume "as" "M" "CasM" "n")
(ng #t)
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
(set-goal "all as,M Zero<cRBd as M")
(assume "as" "M")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealBdPos")

(deanimate "RBd")

;; Totality proofs for RealTimes and RealExp

;; RealTimesTotal
(set-totality-goal "RealTimes")
(fold-alltotal)
(cases)
(assume "as" "M")
(fold-alltotal)
(cases)
(assume "bs" "N")
(use "ReaTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for RealExp : rea=>nat=>rea

(add-computation-rules
 "x**Zero" "RealConstr([n](RatConstr(IntPos One)One))([p]Zero)"
 "x**Succ n" "x**n*x")

;; RealExpTotal
(set-totality-goal "RealExp")
(fold-alltotal)
(assume "x")
(fold-alltotal)
(ind)
;; Base
(ng #t)
(use "ReaTotalVar")
;; Step
(assume "n" "IH")
(ng #t)
(use "RealTimesTotal")
(use "IH")
(use "ReaTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; 5.  Comparisen and equality
;; ===========================

;; We introduce an inductively defined predicate RealLe x y

(add-ids
 (list (list "RealLe" (make-arity (py "rea") (py "rea"))))
 '("all x,y(Real x -> Real y ->
    all p x seq(x mod(PosS p))<=y seq(y mod(PosS p))+(1#2**p) ->
    RealLe x y)" "RealLeIntro"))

;; Notice that we cannot take <= and use overloading, because the token
;; <= has token type rel-op and hence produces a term, not a predicate.

(add-token
 "<<="
 'pred-infix
 (lambda (x y)
   (make-predicate-formula (make-idpredconst "RealLe" '() '()) x y)))

(add-idpredconst-display "RealLe" 'pred-infix "<<=")

;; We introduce an inductively defined predicate RealLeS x y
;; expressing pointwise <= for the Cauchy sequences.

(add-ids
 (list (list "RealLeS" (make-arity (py "rea") (py "rea"))))
 '("all x,y(all n x seq n<=y seq n -> RealLeS x y)" "RealLeSIntro"))

;; predicate creator

(define (make-predicate-creator token min-type-string)
  (lambda (x y)
    (let* ((type1 (term-to-type x))
	   (type2 (term-to-type y))
	   (min-type (py min-type-string))
	   (type (types-lub type1 type2 min-type))
	   (internal-name (token-and-types-to-name token (list type))))
      (make-predicate-formula (make-idpredconst internal-name '() '()) x y))))

(add-token "<+=" 'pred-infix (make-predicate-creator "<+=" "rea"))

(add-token-and-type-to-name "<+=" (py "rea") "RealLeS")

(add-idpredconst-display "RealLeS" 'pred-infix "<+=")

;; We introduce an inductively defined predicate RealEq x y

(add-ids
 (list (list "RealEq" (make-arity (py "rea") (py "rea"))))
 '("all x,y(x<<=y -> y<<=x -> RealEq x y)" "RealEqIntro"))

;; Notice that we cannot take = and use overloading, because the token
;; = has token type rel-op and hence produces a term, not a predicate.

(add-token "===" 'pred-infix (make-predicate-creator "===" "rea"))

(add-token-and-type-to-name "===" (py "rea") "RealEq")

(add-idpredconst-display "RealEq" 'pred-infix "===")

;; RealLeAntiSym ;same as RealEqIntro
(set-goal "all x,y(x<<=y -> y<<=x -> RealEq x y)")
(use "RealEqIntro")
;; Proof finished.
;; (cdp)
(save "RealLeAntiSym")

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

;; Properties of RealLe RealLeS RealEq RealEqS RealNNeg RealNNegS

;; RealLeElim0
(set-goal "all x,y(x<<=y -> Real x)")
(assume "x" "y" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
;; (cdp)
(save "RealLeElim0")

;; RealLeElim1
(set-goal "all x,y(x<<=y -> Real y)")
(assume "x" "y" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
;; (cdp)
(save "RealLeElim1")

;; RealLeElim2
(set-goal "all x,y(x<<=y ->
  all p x seq(x mod(PosS p))<=y seq(y mod(PosS p))+(1#2**p))")
(assume "x" "y" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
;; (cdp)
(save "RealLeElim2")

;; RealConstrLeElim2
(set-goal
 "all as,M,bs,N(RealConstr as M<<=RealConstr bs N ->
                all p as(M(PosS p))<=bs(N(PosS p))+(1#2**p))")
(assume "as" "M" "bs" "N" "LeHyp" "p")
(use-with "RealLeElim2"
	  (pt "RealConstr as M") (pt "RealConstr bs N") "LeHyp" (pt "p"))
;; Proof finished.
;; (cdp)
(save "RealConstrLeElim2")

;; RealEqElim0
(set-goal "all x,y(x===y -> x<<=y)")
(assume "x" "y" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqElim0")

;; RealEqElim1
(set-goal "all x,y(x===y -> y<<=x)")
(assume "x" "y" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqElim1")

;; RealEqToReal0
(set-goal "all x,y(x===y -> Real x)")
(assume "x" "y" "x=y")
(use "RealLeElim0" (pt "y"))
(use "RealEqElim0")
(use "x=y")
;; Proof finished.
;; (cdp)
(save "RealEqToReal0")

;; RealEqToReal1
(set-goal "all x,y(x===y -> Real y)")
(assume "x" "y" "x=y")
(use "RealLeElim1" (pt "x"))
(use "RealEqElim0")
(use "x=y")
;; Proof finished.
;; (cdp)
(save "RealEqToReal1")

;; RealEqSElim
(set-goal "all x,y(x=+=y -> all n x seq n==y seq n)")
(assume "x" "y" "x=y")
(elim "x=y")
(search)
;; Proof finished.
;; (cdp)
(save "RealEqSElim")

;; RealConstrEqSElim
(set-goal
 "all as,M,bs,N(RealConstr as M=+=RealConstr bs N -> all n as n==bs n)")
(assume "as" "M" "bs" "N" "EqSHyp" "n")
(use-with "RealEqSElim"
	  (pt "RealConstr as M") (pt "RealConstr bs N") "EqSHyp" (pt "n"))
;; Proof finished.
;; (cdp)
(save "RealConstrEqSElim")

;; TotalReaToEqD
(set-goal "allnc x^(TotalReaNc x^ -> x^ eqd RealConstr x^ seq x^ mod)")
(assume "x^")
(elim)
(ng)
(strip)
(use "InitEqD")
;; Proof finished.
;; (cdp)
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

;; We now prove further properties of RealLe RealNNeg

;; EfRealLe
(set-goal "F -> all x,y x<<=y")
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
(save "EfRealLe")

;; RealLeRefl
(set-goal "all x(Real x -> x<<=x)")
(cases)
(assume "as" "M" "Rx")
(use "RealLeIntro")
;; 4-6
(use "Rx")
(use "Rx")
(assume "p")
(use "Truth")
;; Proof finished.
(save "RealLeRefl")

;; EfRealEq
(set-goal "F -> all x,y x===y")
(assume "Absurd" "x" "y")
(intro 0)
(use "EfRealLe")
(use "Absurd")
(use "EfRealLe")
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

;; To prove transitivity of RealLe we need a characterization

;; RealLeChar1
(set-goal "allnc as,M,bs,N(RealConstr as M<<=RealConstr bs N -> 
      allnc p exnc n1 allnc n(n1<=n -> as n<=bs n+(1#2**p)))")
(assume "as" "M" "bs" "N" "x<=y" "p")
(intro 0 (pt "M(PosS(PosS p))max N(PosS(PosS p))"))
(assume "n" "BdHyp")
(use "RatLePlusR")
(simp "RatPlusComm")
;; ?^6:as n+ ~(bs n)<=(1#2**p)
(use "RatLeTrans"
     (pt "(1#2**(PosS(PosS p)))+(1#2**(PosS p))+(1#2**(PosS(PosS p)))"))
;; 7,8
(use "RatLeTrans" (pt "(as n+ ~(as(M(PosS(PosS p)))))+
                       (as(M(PosS(PosS p)))+ ~(bs(N(PosS(PosS p)))))+
                       (bs(N(PosS(PosS p)))+ ~(bs n))"))
;; 9,10
(ng #t)
(simprat "RatEqvPlusMinus")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; 10
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
;; 22-24
(use "RatLeTrans" (pt "abs(as n+ ~(as(M(PosS(PosS p)))))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(autoreal)
(use "NatLeTrans" (pt "(M(PosS(PosS p)))max(N(PosS(PosS p)))"))
(use "NatMaxUB1")
(use "BdHyp")
(use "Truth")
;; 23
(simp "RatPlusComm")
(use "RatLePlusRInv")
(use "RealConstrLeElim2")
(use "x<=y")
;; 24
(use "RatLeTrans" (pt "abs(bs(N(PosS(PosS p)))+ ~(bs n))"))
(use "Truth")
(use "CauchyElim" (pt "N"))
(use "RealConstrToCauchy")
(autoreal)
(use "Truth")
(use "NatLeTrans" (pt "(M(PosS(PosS p)))max(N(PosS(PosS p)))"))
(use "NatMaxUB2")
(use "BdHyp")
;; ?^8:(1#2**PosS(PosS p))+(1#2**PosS p)+(1#2**PosS(PosS p))<=(1#2**p)
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
;; (cdp)
(save "RealLeChar1")

;; RealLeChar1RealConstrFree
(set-goal "all x,y(x<<=y ->
 all p exnc n0 all n(n0<=n -> x seq n<=y seq n+(1#2**p)))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealLeChar1")
;; Proof finished.
;; (cdp)
(save "RealLeChar1RealConstrFree")

;; RealLeChar2
(set-goal "all as,M,bs,N(Real(RealConstr as M) -> Real(RealConstr bs N) ->
           all p exnc n0 all n(n0<=n -> as n<=bs n+(1#2**p)) ->
           RealConstr as M<<=RealConstr bs N)")
(assume "as" "M" "bs" "N" "Rx" "Ry" "Est")
(intro 0)
(autoreal)
(assume "p")
(ng #t)
;; ?^7:as(M(PosS p))<=bs(N(PosS p))+(1#2**p)
(use "RatLePlusR")
(simp "RatPlusComm")
;; ?^9:as(M(PosS p))+ ~(bs(N(PosS p)))<=(1#2**p)
(use "RatLeAllPlusToLe")
(assume "q")
;; ?^11:as(M(PosS p))+ ~(bs(N(PosS p)))<=(1#2**p)+(1#2**q)
(inst-with-to "Est" (pt "q") "InstEst")
(drop "Est")
(by-assume "InstEst" "n0" "n0Prop")
;; We now want to use n as an abbreviation for the complex term
;; ((M(PosS p))max(N(PosS p)))max n0.
(defnc "n" "((M(PosS p))max(N(PosS p)))max n0")
(use "RatLeTrans"
     (pt "(as(M(PosS p))+ ~(as n))+
          (as n+ ~(bs n))+
          (bs n+ ~(bs(N(PosS p))))"))
;; 25,26
(ng #t)
(simprat "RatEqvPlusMinus")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; ?^26:as(M(PosS p))+ ~(as n)+(as n+ ~(bs n))+(bs n+ ~(bs(N(PosS p))))<=
;;      (1#2**p)+(1#2**q)
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
;; 40-42
(drop "RatLeMonPlus3")
(use "RatLeTrans" (pt "abs(as(M(PosS p))+ ~(as n))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "Truth")
(simp "nDef")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS p)"))
(use "NatMaxUB1")
(use "NatMaxUB1")
;; 41
(drop "RatLeMonPlus3")
(simp "RatPlusComm")
(use "RatLePlusRInv")
(use "n0Prop")
(simp "nDef")
(use "NatMaxUB2")
;; 42
(drop "RatLeMonPlus3")
(use "RatLeTrans" (pt "abs(bs n+ ~(bs(N(PosS p))))"))
(use "Truth")
(use "CauchyElim" (pt "N"))
(use "RealConstrToCauchy")
(use "Ry")
(simp "nDef")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS p)"))
(use "NatMaxUB2")
(use "NatMaxUB1")
(use "Truth")
;; ?^31:(1#2**PosS p)+(1#2**q)+(1#2**PosS p)<=(1#2**p)+(1#2**q)
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealLeChar2")

;; RealLeChar2RealConstrFree
(set-goal "all x,y(Real x -> Real y -> 
 all p exnc n0 all n(n0<=n -> x seq n<=y seq n+(1#2**p)) -> x<<=y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealLeChar2")
;; Proof finished.
;; (cdp)
(save "RealLeChar2RealConstrFree")

;; It will be helpful to have direct characterizations of RealEq

;; RealEqChar1
(set-goal "all x,y(x===y ->
  all p exnc n1 all n(n1<=n -> abs(x seq n+ ~(y seq n))<=(1#2**p)))")
(assume "x" "y" "x=y" "p")

(inst-with-to "RealEqElim0" (pt "x") (pt "y") "x=y" "x<=y")
(inst-with-to "RealLeChar1RealConstrFree"
	      (pt "x") (pt "y") "x<=y" (pt "p") "n1Ex")
(by-assume "n1Ex" "n1" "n1Prop")

(inst-with-to "RealEqElim1" (pt "x") (pt "y") "x=y" "y<=x")
(inst-with-to "RealLeChar1RealConstrFree"
	      (pt "y") (pt "x") "y<=x" (pt "p") "n2Ex")
(by-assume "n2Ex" "n2" "n2Prop")

(intro 0 (pt "n1 max n2"))
(assume "n" "nBd")
(use "RatLeAbs")
;; 19,20
(simp "RatPlusComm")
(use "RatLePlusRInv")
(use "n1Prop")
(use "NatLeTrans" (pt "n1 max n2"))
(use "NatMaxUB1")
(use "nBd")
;; 20
(ng #t)
(use "RatLePlusRInv")
(use "n2Prop")
(use "NatLeTrans" (pt "n1 max n2"))
(use "NatMaxUB2")
(use "nBd")
;; Proof finished.
;; (cdp)
(save "RealEqChar1")

;; RealEqChar2
(set-goal "all x,y(Real x -> Real y -> 
 all p exnc n0 all n(n0<=n -> abs(x seq n+ ~(y seq n))<=(1#2**p)) -> x===y)")
(assume "x" "y" "Rx" "Ry" "AllExHyp")
(use "RealEqIntro")
;; 3,4
(use "RealLeChar2RealConstrFree")
(autoreal)
(assume "p")
(inst-with-to "AllExHyp" (pt "p") "nEx")
(drop "AllExHyp")
(by-assume "nEx" "n" "nProp")
(intro 0 (pt "n"))
(assume "m" "n<=m")
(inst-with-to "nProp" (pt "m") "n<=m" "AbsIneq")
(assert "x seq m+ ~(y seq m)<=(1#2**p)")
(use "RatLeTrans" (pt "abs(x seq m+ ~(y seq m))"))
(use "Truth")
(use "AbsIneq")
;; Assertion proved.
(assume "Ineq")
(use "RatLePlusR")
(simp "RatPlusComm")
(use "Ineq")
;; 4
(use "RealLeChar2RealConstrFree")
(autoreal)
(assume "p")
(inst-with-to "AllExHyp" (pt "p") "nEx")
(drop "AllExHyp")
(by-assume "nEx" "n" "nProp")
(intro 0 (pt "n"))
(assume "m" "n<=m")
(inst-with-to "nProp" (pt "m") "n<=m" "AbsIneq")
(use "RatLePlusR")
(simp (pf "y seq m= ~ ~(y seq m)"))
(simp "<-" "RatUMinus2RewRule")
(use "RatLeTrans" (pt "abs(~(x seq m+ ~(y seq m)))"))
(use "Truth")
(simp "RatAbs0RewRule")
(use "AbsIneq")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealEqChar2")

;; RealEqChar2 is useful to relate operations like Plus on lower types
;; like nat to the corresponding operations on the reals.  An example is
;; NatToRealPlus : all n,m RealPlus n m===n+m proved later.

;; RealLeTrans
(set-goal "all x,y,z(x<<=y -> y<<=z -> x<<=z)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "K" "x<=y" "y<=z")
;; ?^7:RealConstr as M<<=RealConstr cs K
(use "RealLeChar2")
(autoreal)
;; ?^10:all p exnc n all n0(n<=n0 -> as n0<=cs n0+(1#2**p))
(assume "p")
;; Use RealLeChar1 for x<=y
(assert "exnc n all n0(n<=n0 -> as n0<=bs n0+(1#2**(PosS p)))")
(use "RealLeChar1" (pt "M") (pt "N"))
(use "x<=y")
(assume "xyExHyp")
(by-assume "xyExHyp" "m" "mProp")
;; Use RealLeChar1 for y<=z
(assert "exnc n all n0(n<=n0 -> bs n0<=cs n0+(1#2**(PosS p)))")
(use "RealLeChar1" (pt "N") (pt "K"))
(use "y<=z")
(assume "yzExHyp")
(by-assume "yzExHyp" "l" "lProp")
;; Take m max l for n
(intro 0 (pt "m max l"))
(assume "n" "BdHyp")
(simprat "<-" "RatPlusHalfExpPosS")
(use "RatLeTrans" (pt "bs n+(1#2**PosS p)"))
;; 29,30
(use "mProp")
(use "NatLeTrans" (pt "m max l"))
(use "NatMaxUB1")
(use "BdHyp")
;; ?^30:bs n+(1#2**PosS p)<=cs n+((1#2**PosS p)+(1#2**PosS p))
(simp "RatPlusAssoc")
(ng #t)
(use "lProp")
(use "NatLeTrans" (pt "m max l"))
(use "NatMaxUB2")
(use "BdHyp")
;; Proof finished.
;; (cdp)
(save "RealLeTrans")

;; RealEqRefl
(set-goal "all x(Real x -> x===x)")
(assume "x" "Rx")
(intro 0)
(use "RealLeRefl")
(use "Rx")
(use "RealLeRefl")
(use "Rx")
;; Proof finished.
;; (cdp)
(save "RealEqRefl")

;; RealEqSym
(set-goal "all x,y(x===y -> y===x)")
(assume "x" "y" "x=y")
(elim "x=y")
(assume "x1" "y1" "x1<=y1" "y1<=x1")
(intro 0)
(use "y1<=x1")
(use "x1<=y1")
;; Proof finished.
;; (cdp)
(save "RealEqSym")

;; RealEqTrans
(set-goal "all x,y,z(x===y -> y===z -> x===z)")
(assume "x" "y" "z" "x=y" "y=z")
(intro 0)
;; 3,4
(use "RealLeTrans" (pt "y"))
(use "RealEqElim0")
(use "x=y")
(use "RealEqElim0")
(use "y=z")
;; 4
(use "RealLeTrans" (pt "y"))
(use "RealEqElim1")
(use "y=z")
(use "RealEqElim1")
(use "x=y")
;; Proof finished.
;; (cdp)
(save "RealEqTrans")

;; An immediate consequence of RealLeChar2 is that any two reals with
;; pointwise increasing Cauchy sequence (but possibly different
;; moduli) are increasing

;; RealSeqLeToLe
(set-goal "all x,y,n1(Real x -> Real y ->
 all n(n1<=n -> x seq n<=y seq n) -> x<<=y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "n1" "Rx" "Ry" "Incr")
(ng "Incr")
(use "RealLeChar2")
(autoreal)
(assume "p")
(intro 0 (pt "n1"))
(assume "n" "n1<=n")
(use "RatLeTrans" (pt "bs n"))
(use "Incr")
(use "n1<=n")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealSeqLeToLe")

;; RealSeqEqToEq
(set-goal "all x,y,n1(Real x -> Real y ->
 all n(n1<=n -> x seq n==y seq n) -> x===y)")
(assume "x" "y" "n1" "Rx" "Ry" "EqHyp")
(intro 0)
;; 3,4
(use "RealSeqLeToLe" (pt "n1"))
(autoreal)
(assume "n" "n1<=n")
(simprat "EqHyp")
(use "Truth")
(use "n1<=n")
;; 4
(use "RealSeqLeToLe" (pt "n1"))
(autoreal)
(assume "n" "n1<=n")
(simprat "EqHyp")
(use "Truth")
(use "n1<=n")
;; Proof finished.
;; (cdp)
(save "RealSeqEqToEq")

;; RatLeToRealLe
(set-goal "all a,b(a<=b -> a<<=b)")
(assume "a" "b" "a<=b")
(use "RealLeIntro")
(autoreal)
(assume "p")
(ng #t)
(use "RatLeTrans" (pt "b"))
(use "a<=b")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RatLeToRealLe")

;; RealLeToRatLe
(set-goal "all a,b(a<<=b -> a<=b)")
(assume "a" "b" "a<<=b")
(inst-with-to "RealLeElim2"
	      (pt "RealConstr([n]a)([p]Zero)")
	      (pt "RealConstr([n]b)([p]Zero)")
	      "a<<=b" "RealLeElim2Inst")
(ng "RealLeElim2Inst")
(use "RatLeAllPlusToLe")
(use "RealLeElim2Inst")
;; Proof finished.
;; (cdp)
(save "RealLeToRatLe")

;; IntLeToRealLe
(set-goal "all k,j(k<=j -> k<<=j)")
(assume "k" "j" "k<=j")
(use "RatLeToRealLe")
(use "k<=j")
;; Proof finished.
;; (cdp)
(save "IntLeToRealLe")

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
;; (cdp)
(save "RealLeToIntLe")

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

;; RealLeSElim
(set-goal "all x,y(x<+=y -> all n x seq n<=y seq n)")
(assume "x" "y" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
;; (cdp)
(save "RealLeSElim")

;; RealConstrLeSElim
(set-goal
 "all as,M,bs,N(RealConstr as M<+=RealConstr bs N -> all n as n<=bs n)")
(assume "as" "M" "bs" "N" "LeSHyp" "n")
(use-with "RealLeSElim"
	  (pt "RealConstr as M") (pt "RealConstr bs N") "LeSHyp" (pt "n"))
;; Proof finished.
;; (cdp)
(save "RealConstrLeSElim")

;; RealLeSToLe
(set-goal "all x,y(Real x -> Real y -> x<+=y -> x<<=y)")
(assume "x" "y" "Rx" "Ry" "LeSxy")
(cases (pt "x"))
(assume "as" "M" "xDef")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(use "RealLeChar2")
(simp "<-" "xDef")
(use "Rx")
(simp "<-" "yDef")
(use "Ry")
(assume "p")
(intro 0 (pt "Zero"))
(assume "n" "Useless")
(use "RatLeTrans" (pt "bs n"))
(use "RealConstrLeSElim" (pt "M") (pt "N"))
(simp "<-" "xDef")
(simp "<-" "yDef")
(use "LeSxy")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealLeSToLe")

;; RealNNegChar1
(set-goal "all as,M(RealNNeg(RealConstr as M) -> 
      all p exnc n1 all n(n1<=n -> ~(1#2**p)<=as n))")
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
;; The following argument is repeated in the proof of RealPosChar1 below
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
;; (cdp)
(save "RealNNegChar1")

;; RealNNegChar1RealConstrFree
(set-goal
 "all x(RealNNeg x -> all p exnc n all n0(n<=n0 -> ~(1#2**p)<=x seq n0))")
(cases)
(assume "as" "M" "NNegx")
(ng)
(assume "p")
(simp (pf "(IntN 1#2**p)= ~(1#2**p)"))
(use "RealNNegChar1" (pt "M"))
(use "NNegx")
(ng)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealNNegChar1RealConstrFree")

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
;; (cdp)
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
;; (cdp)
(save "RealNNegChar2RealConstrFree")

;; RealNNegSElim
(set-goal "all x(RealNNegS x -> all n 0<=x seq n)")
(assume "x" "NNegSx")
(elim "NNegSx")
(search)
;; Proof finished.
;; (cdp)
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
;; (cdp)
(save "RealNNegSToNNeg")

;; RealNNegToZeroLe
(set-goal "all x(RealNNeg x -> 0<<=x)")
(assume "x" "NNx")
(use "RealLeChar2RealConstrFree")
(autoreal)
(assume "p")
(inst-with-to "RealNNegChar1RealConstrFree" (pt "x") "NNx" (pt "p") "Inst")
(by-assume "Inst" "n1" "n1Prop")
(intro 0 (pt "n1"))
(assume "n" "nBd")
(ng #t)
(simp "RatPlusComm")
(use "RatLePlusR")
(use "n1Prop")
(use "nBd")
;; Proof finished.
;; (cdp)
(save "RealNNegToZeroLe")

;; RealZeroLeToNNeg
(set-goal "all x(0<<=x -> RealNNeg x)")
(assume "x" "0<=x")
(use "RealNNegChar2RealConstrFree")
(autoreal)
(assume "p")
(inst-with-to "RealLeChar1RealConstrFree"
	      (pt "RealConstr([n](0#1))([p]Zero)") (pt "x") "0<=x" (pt "p")
	      "Inst")
(by-assume "Inst" "n1" "n1Prop")
(intro 0 (pt "n1"))
(assume "n" "nBd")
(ng "n1Prop")
(assert "~(1#2**p)+0<=x seq n")
(use "RatLePlusRInv")
(simp "RatPlusComm")
(use "n1Prop")
(use "nBd")
(ng #t)
(assume "Hyp")
(use "Hyp")
;; Proof finished.
;; (cdp)
(save "RealZeroLeToNNeg")

;; Properties of RealPos

;; RealPos
;;   comprules
;; 0	RealPos(RealConstr as M)p	(1#2**p)<=as(M(Pos p))

;; RealPosChar1
(set-goal "all as,M,p(
 Real(RealConstr as M) -> RealPos(RealConstr as M)p ->
 all n(M(PosS p)<=n -> (1#2**PosS p)<=as n))")
(assume "as" "M" "p" "Rx" "xPos" "n" "BdHyp")
(use "RatLeTrans" (pt "~(1#2**(PosS p))+(as(M(PosS p))+ ~(as n))+as n"))
;; 3,4
(use "RatLePlusR")
(ng #t)
(simp "RatPlusComm")
(simp "<-" "RatPlusAssoc")
(simp "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(use "RatLeTrans" (pt "as(M(PosS p))+(~(as(M(PosS p)))+as n)"))
(use "RatLeMonPlus")
(use "xPos")
(use "Truth")
(ng #t)
(simp "RatPlusComm")
(ng #t)
(simprat "RatEqvPlusMinusRev")
(use "Truth")
;; ?^4:~(1#2**PosS p)+(as(M(PosS p))+ ~(as n))+as n<=as n
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
;; (cdp)
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
(set-goal "all x,n,p(Real x -> all n0(n<=n0 -> (1#2**p)<=x seq n0) ->
                     RealPos x(PosS p))")
(cases)
(assume "as" "M" "n" "p" "Rx" "Est")
(ng #t)
(use "RatLeTrans" (pt "~(1#2**(PosS(PosS p)))+(1#2**p)"))
;; 5,6
(use "RatLeTrans" (pt "~(1#2**(PosS p))+(1#2**p)"))
;; 7,8
(simprat (pf "(1#2**p)==(1#2**PosS p)+(1#2**PosS p)"))
(simp "RatPlusComm")
(simprat "RatEqvPlusMinusRev")
(use "Truth")
(use "RatEqvSym")
(use "RatPlusHalfExpPosS")
(use "RatLeMonPlus")
(simp "RatLeUMinus")
(ng #t)
(assert "all p 2**p<=2**PosS p")
 (assume "p1")
 (simp "PosSSucc")
 (ng #t)
 (use "Truth")
(assume "Assertion")
(use "Assertion")
(use "Truth")
;; 6
(defnc "m" "n max M(PosS(PosS p))")
(use "RatLeTrans" (pt "~(1#2**PosS(PosS p))+as m"))
;; 31,32
(use "RatLeMonPlus")
(use "Truth")
(use "Est")
(simp "mDef")
(use "NatMaxUB1")
;; 32
(use "RatLeTrans" (pt "as(M(PosS(PosS p)))+ ~(as m) +as m"))
(use "RatLeMonPlus")
(simp "<-" "RatLeUMinus")
(ng #t)
(simp "RatPlusComm")
(use "RatLeTrans" (pt "abs(as m+ ~(as(M(PosS(PosS p)))))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(simp "mDef")
(use "NatMaxUB2")
(use "Truth")
(use "Truth")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealPosChar2")

;; Added 2021-01-11 (from Jan Belle's exp.scm)
;; RealPosIntro and RealPosElim can be helpful since they express the
;; definition in implicational form.

;; RealPosIntro
(set-goal "all x,p((1#2**p)<=x seq(x mod(PosS p)) -> RealPos x p)")
(cases)
(assume "as" "M" "p" "x>0")
(use "x>0")
;; Proof finished.
;; (cdp)
(save "RealPosIntro")

;; RealPosElim
(set-goal "all x,p(RealPos x p -> (1#2**p)<=x seq(x mod(PosS p)))")
(cases)
(assume "as" "M" "p" "x>0")
(use "x>0")
;; Proof finished.
;; (cdp)
(save "RealPosElim")

;; RealPosPosS
(set-goal "all x,p(Real x -> RealPos x p -> RealPos x(PosS p))")
(cases)
(assume "as" "M" "p" "Rx" "Pxp")
(ng)
(use "StabAtom")
(assume "FHyp")
(assert "as(M(PosS p))<as(M(PosS p))")
(use "RatLtLeTrans" (pt "(1#2**p)"))
;; ?^9:as(M(PosS p))<(1#2**p)
(simprat "<-" "RatPlusHalfExpPosS")
;; ?^11:as(M(PosS p))<(1#2**PosS p)+(1#2**PosS p)
(use "RatLeLtTrans" (pt "as(M(PosS(PosS p)))+(1#2**PosS p)"))
(use "CauchyChar1" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "Truth")
;; ?^16:M(PosS p)<=M(PosS(PosS p))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "Truth")
;; ?^13:as(M(PosS(PosS p)))+(1#2**PosS p)<(1#2**PosS p)+(1#2**PosS p)
(simp "RatLt5RewRule")
(use "RatNotLeToLt")
(use "FHyp")
(use "Pxp")
;; ?^7:as(M(PosS p))<as(M(PosS p)) -> F
(ng #t)
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "RealPosPosS")

;; RealPosLe
(set-goal "all x,y,p(x<<=y -> RealPos x p -> RealPos y(PosS(PosS p)))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "p" "x<=y")
(ng #t)
(assume "0<x")
(use "RatLeTrans" (pt "(1#2**PosS p)+ ~(1#2**PosS(PosS p))"))
;; 8,9
(inst-with-to "RatPlusHalfExpPosS" (pt "PosS p") "RatPlusHalfExpPosSInst")
(simprat "<-" "RatPlusHalfExpPosSInst")
(simp "<-" "RatPlusAssoc")
(use "Truth")
;; ?^9:(1#2**PosS p)+ ~(1#2**PosS(PosS p))<=bs(N(PosS(PosS(PosS p))))
(inst-with-to "RatEqvPlusMinus"
	      (pt "bs(N(PosS(PosS(PosS p))))")
	      (pt "as(M(PosS(PosS(PosS p))))")
	      "RatEqvPlusMinusInst")
(simphyp-to "RatEqvPlusMinusInst" "RatPlusComm" "RatEqvPlusMinusInstSimp")
(drop "RatEqvPlusMinusInst")
(simprat "<-" "RatEqvPlusMinusInstSimp")
(drop "RatEqvPlusMinusInstSimp")
(use "RatLeMonPlus")
;; 21,22
;; ?^21:(1#2**PosS p)<=as(M(PosS(PosS(PosS p))))
(use "RealPosChar1" (pt "M"))
(autoreal)
(ng #t)
(use "0<x")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(autoreal)
(use "PosLeTrans" (pt "PosS(PosS p)"))
(use "Truth")
(use "Truth")
;; ?^22:~(1#2**PosS(PosS p))<=
;;      bs(N(PosS(PosS(PosS p))))+ ~(as(M(PosS(PosS(PosS p)))))
(use "RatLeTrans"
     (pt "~(as(M(PosS(PosS(PosS p))))+ ~(bs(N(PosS(PosS(PosS p))))))"))
(simp "RatLeUMinus")
(simp "RatPlusComm")
(use "RatLePlusRInv")
(use "RealConstrLeElim2")
(use "x<=y")
;; 33
(ng #t)
(simp "RatPlusComm")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealPosLe")

;; An easy consequence is

;; RealPosSemiCompat
(set-goal "all x,y,p(x===y -> RealPos x p -> RealPos y(PosS(PosS p)))")
(assume "x" "y" "p" "x=y")
(use "RealPosLe")
(use "RealEqElim0")
(use "x=y")
;; Proof finished.
;; (cdp)
(save "RealPosSemiCompat")

;; RealPosToPosAbs
(set-goal "all p,x(RealPos x p -> RealPos(abs x)p)")
(assume "p")
(cases)
(assume "as" "M" "PosHyp")
(ng #t)
(use "RatLeTrans" (pt "as(M(PosS p))"))
(use "PosHyp")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealPosToPosAbs")

;; RealPosAbsToPos
(set-goal "all x,p(0<<=x -> RealPos abs x p -> RealPos x p)")
(cases)
(ng #t)
(assume "as" "M" "p" "0<=x")
(defnc "a" "as(M(PosS p))")
(simp "<-" "aDef")
(assume "LeAbs")
(use "RatNotLtToLe")
(assume "LtHyp")
(use "RatAbsCases" (pt "a"))
;; 16,17
(assume "|a|=a")
(assert "a<a")
(use "RatLtLeTrans" (pt "(1#2**p)"))
(use "LtHyp")
(simp "<-" "|a|=a")
(use "LeAbs")
(assume "Absurd")
(use "Absurd")
;; ?^17:abs a= ~a -> F
(assume "|a|= ~a")
(assert "a<a")
(use "RatLeLtTrans" (pt "~(1#2**p)"))
(simp (pf "a= ~ ~a"))
(simp "RatLe7RewRule")
(simp "<-" "|a|= ~a")
(use "LeAbs")
(use "Truth")
;; ?^29:~(1#2**p)<a
(use "RatLtLeTrans" (pt "~(1#2**PosS p)"))
(ng #t)
(use "PosLtMonPosExpTwoPos")
(use "Truth")
;; ?^35:~(1#2**PosS p)<=a
(simp "aDef")
(simp (pf "~(1#2**PosS p)= ~(1#2**PosS p)+0"))
(use "RatLePlusRInv")
(simp "RatPlusComm")
(use "RealConstrNNegElim1") ;unary NNeg needed, binary Le would not work
(use "RealZeroLeToNNeg")
(use "0<=x")
(use "Truth")
;; ?^26:a<a -> F
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "RealPosAbsToPos")

;; RealLeToPos
(set-goal "all x,p((1#2**p)<<=x -> RealPos x(PosS p))")
(cases)
(assume "as" "M" "p" "LeHyp")
(ng #t)
;; (elim "LeHyp")
(inst-with-to
 "RealLeElim2"
 (pt "RealConstr([n](1#2**p))([p]Zero)")
 (pt "RealConstr as M")
 "LeHyp"
 (pt "PosS p")
 "Inst")
(ng "Inst")
(use "RatLePlusCancelR" (pt "(1#2**PosS p)"))
(simprat "RatPlusHalfExpPosS")
(use "Inst")
;; Proof finished.
;; (cdp)
(save "RealLeToPos")

;; RealPosToLe
(set-goal "all x,p(Real x -> RealPos x p -> (1#2**PosS p)<<=x)")
(cases)
(assume "as" "M" "p" "Rx" "0<x")
(use "RealLeChar2")
(autoreal)
(assume "q")
(ng #t)
(intro 0 (pt "M(PosS p)"))
(assume "n" "Mp+1<=n")
(use "RatLeTrans" (pt "as n"))
(use "RealPosChar1" (pt "M"))
(use "Rx")
(use "0<x")
(use "Mp+1<=n")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealPosToLe")

;; RealPosToZeroLe
(set-goal "all x,p(Real x -> RealPos x p -> 0<<=x)")
(assume "x" "p" "Rx" "0<x")
(use "RealLeTrans" (pt "RealConstr([n](1#2**PosS p))([p]Zero)"))
;; 3,4
(use "RatLeToRealLe")
(use "Truth")
;; 4
(use "RealPosToLe")
(use "Rx")
(use "0<x")
;; Proof finished.
;; (cdp)
(save "RealPosToZeroLe")

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

;; NatToRealPlus
(set-goal "all n,m RealPlus n m===n+m")
(assume "n" "m")
(use "RealEqChar2")
(autoreal)
(assume "p")
(intro 0 (pt "Zero"))
(assume "n0" "Useless")
(ng #t)
(simp "NatToIntPlus")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatToRealPlus")

;; RealPosMonPlus
(set-goal "all x,y,p,q(Real x -> Real y -> RealPos x p -> RealPos y q ->
                       RealPos(x+y)(PosS(PosS(p min q))))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "p" "q" "Rx" "Ry" "x ppos" "y qpos")
(use "RealPosChar2" (pt "M(PosS p)max N(PosS q)"))
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
;; (cdp)
(save "RealPosMonPlus")

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
(set-goal "all x,p(Real x -> RealPos abs x p -> Real(RealUDiv x p))")
(cases)
(assume "as" "M" "p" "Rx" "Pxp")
(assert "RealPos(RealConstr([n]abs(as n))M)p")
(use "Pxp")
;; Assertion proved.
(assume "PxpAbs")
(assert "Real(RealConstr([n]abs(as n))M)")
(intro 0)
(ng #t)
(intro 0)
(ng #t)
(assume "q" "n" "m" "nBd" "mBd")
(use "RatLeTrans" (pt "abs(as n+ ~(as m))"))
(use "RatLeAbsMinusAbs")
;; ?^16:abs(as n+ ~(as m))<=(1#2**q)
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "nBd")
(use "mBd")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
;; Assertion proved.
(assume "RAbs")
(inst-with-to
"RealPosChar1"
(pt "[n]abs(as n)") (pt "M") (pt "p") "RAbs" "PxpAbs" "asProp")
(ng "asProp")

(intro 0)
;; 26,27
(ng #t)
;; ?^28:Cauchy([n]RatUDiv(as n))([p0]M(SZero(PosS p)+p0))
(intro 0)
(ng #t)
(assume "q" "n" "m" "nBd" "mBd")
(simprat (pf "RatUDiv(as n)==(as m)*RatUDiv((as n)*(as m))"))
;; 32,33
(simprat (pf "RatUDiv(as m)==(as n)*RatUDiv((as n)*(as m))"))
;; 34,35
(simprat "RatUDivTimes")
(simp "<-" "RatTimes4RewRule")
(simprat "<-" "RatTimesPlusDistrLeft")
(simp "RatAbsTimes")
(simp "RatAbsTimes")
(simp "RatTimesAssoc")
;; ?^41:abs(as m+ ~(as n))*abs(RatUDiv(as n))*abs(RatUDiv(as m))<=(1#2**q)
(simprat (pf "(1#2**q)==(1#2**(SZero(PosS p)+q))*2**PosS p*2**PosS p"))
(use "RatLeMonTimesTwo")
(simp "<-" "RatAbsTimes")
(use "Truth")
(simp "RatLe9RewRule")
(use "Truth")
(use "RatLeMonTimesTwo")
(use "Truth")
(simp "RatLe9RewRule")
(use "Truth")
;; ?^30:abs(as m+ ~(as n))<=(1#2**(SZero(PosS p)+q))
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "mBd")
(use "nBd")
;; ?^53:abs(RatUDiv(as n))<=2**PosS p
(ng #t)
(simprat (pf "2**PosS p==RatUDiv(RatUDiv(2**PosS p))"))
(use "RatLeUDivUDiv")
(ng #t)
(use "Truth")
(ng #t)
(use "asProp")
(use "NatLeTrans" (pt "M(SZero(PosS p)+q)"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "SZero(PosS p)"))
(use "Truth")
(use "Truth")
(use "nBd")
(simp "RatEqvSym")
(use "Truth")
(use "RatUDivUDiv")
;; ?^47:abs(RatUDiv(as m))<=2**PosS p
(ng #t)
(simprat (pf "2**PosS p==RatUDiv(RatUDiv(2**PosS p))"))
(use "RatLeUDivUDiv")
(use "Truth")
(ng #t)
(use "asProp")
(use "NatLeTrans" (pt "M(SZero(PosS p)+q)"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "SZero(PosS p)"))
(use "Truth")
(use "Truth")
(use "mBd")
(simp "RatEqvSym")
(use "Truth")
(use "RatUDivUDiv")
;; ?^43:(1#2**q)==(1#2**(SZero(PosS p)+q))*2**PosS p*2**PosS p
(ng #t)
(simp "<-" "PosExpTwoPosPlus")
;; ?^93:2**SZero(PosS p)*2**q=2**PosS p*2**PosS p*2**q
(assert "all r(SZero r=r+r andnc SOne r=PosS(r+r))")
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
(simp (pf "SZero(PosS p)=PosS p+PosS p"))
(simp "<-" "PosExpTwoPosPlus")
(use "Truth")
(use "Assertion")
;; RatUDiv(as m)==as n*RatUDiv(as n*as m)
(use "RatUDivExpandL")
;; ?^111:0<abs(as n)
(use "RatLtLeTrans" (pt "(1#2**PosS p)"))
(use "Truth")
(use "asProp")
(use "NatLeTrans" (pt "M(SZero(PosS p)+q)"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "SZero(PosS p)"))
(use "Truth")
(use "Truth")
(use "nBd")
;; ?^33:RatUDiv(as n)==as m*RatUDiv(as n*as m)
(use "RatUDivExpandR")
;; ?^122:0<abs(as m)
(use "RatLtLeTrans" (pt "(1#2**PosS p)"))
(use "Truth")
(use "asProp")
(use "NatLeTrans" (pt "M(SZero(PosS p)+q)"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "SZero(PosS p)"))
(use "Truth")
(use "Truth")
(use "mBd")
;; ?^27:Mon((RealUDiv(RealConstr as M)p)mod)
(ng #t)
(intro 0)
(assume "p1" "q1" "p1<=q1")
(ng #t)
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(ng #t)
(use "p1<=q1")
;; Proof finished.
;; (cdp)
(save "RealUDivReal")

;; RealUDivReal can be strengthened by weakening its RealPos premise.

;; RealUDivRealPosFree
(set-goal  "all x,p(Real x ->
  all n(x mod(PosS p)<=n -> (1#2**PosS p)<=(abs x)seq n) ->
  Real(RealUDiv x p))")
(cases)
(assume "as" "M" "q" "Rx")
(ng #t)
(assume "asMProp")
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
;; ?^20:abs(as m+ ~(as n))*abs(RatUDiv(as n))*abs(RatUDiv(as m))<=(1#2**p)
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
;; ?^31:abs(as m+ ~(as n))<=(1#2**(SZero(PosS q)+p))
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "mBd")
(use "nBd")
;; ?^32:abs(RatUDiv(as n))<=2**PosS q
(ng)
(simprat (pf "2**PosS q==RatUDiv(RatUDiv(2**PosS q))"))
(use "RatLeUDivUDiv")
(ng)
(use "Truth")
(ng)
(use "asMProp")
(use "NatLeTrans" (pt "M(SZero(PosS q)+p)"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "SZero(PosS q)"))
(use "Truth")
(use "Truth")
(use "nBd")
(simp "RatEqvSym")
(use "Truth")
(use "RatUDivUDiv")
;; ?^26:abs(RatUDiv(as m))<=2**PosS q
(ng)
(simprat (pf "2**PosS q==RatUDiv(RatUDiv(2**PosS q))"))
(use "RatLeUDivUDiv")
(ng)
(use "Truth")
(ng)
(use "asMProp")
(use "NatLeTrans" (pt "M(SZero(PosS q)+p)"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "SZero(PosS q)"))
(use "Truth")
(use "Truth")
(use "mBd")
(simp "RatEqvSym")
(use "Truth")
(use "RatUDivUDiv")
;; ?^22:(1#2**p)==(1#2**(SZero(PosS q)+p))*2**PosS q*2**PosS q
(ng)
(simp "<-" "PosExpTwoPosPlus")
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
;; ?^14:RatUDiv(as m)==as n*RatUDiv(as n*as m)
(use "RatUDivExpandL")
;; ?^91:0<abs(as n)
(use "RatLtLeTrans" (pt "(1#2**PosS q)"))
(use "Truth")
(use "asMProp")
(use "NatLeTrans" (pt "M(SZero(PosS q)+p)"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "SZero(PosS q)"))
(use "Truth")
(use "Truth")
(use "nBd")
;; ?^12:RatUDiv(as n)==as m*RatUDiv(as n*as m)
(use "RatUDivExpandR")
;; ?_102:0<abs(as m)
(use "RatLtLeTrans" (pt "(1#2**PosS q)"))
(use "Truth")
(use "asMProp")
(use "NatLeTrans" (pt "M(SZero(PosS q)+p)"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "SZero(PosS q)"))
(use "Truth")
(use "Truth")
(use "mBd")
;; ?^7:Mon((RealConstr([n]RatUDiv(as n))([p]M(SZero(PosS q)+p)))mod)
(use "MonIntro")
(ng)
(assume "p1" "p2" "p1<=p2")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(ng)
(use "p1<=p2")
;; Proof finished.
;; (cdp)
(save "RealUDivRealPosFree")

;; RealPosToZeroLeUDiv
(set-goal "all x,p(Real x -> RealPos x p -> 0<<=(RealUDiv x p))") 
(cases)
(assume "as" "M" "p" "Rx" "0<x")
(use "RealLeChar2")
(use "RealRat")
;; ?^5:Real(RealConstr([n]RatUDiv(as n))([p0]M(SZero(PosS p)+p0)))
(simp (pf "SZero(PosS p)=2*PosS p"))
(simp "<-" "RealUDiv0CompRule")
(use "RealUDivReal")
(use "Rx")
;; ?^11:RealPos abs(RealConstr as M)p
(use "RealPosToPosAbs")
(use "0<x")
(use "Truth")
;; ?^6:all p exnc n all n0(n<=n0 -> ([n1]0)n0<=([n1]RatUDiv(as n1))n0+(1#2**p))
(ng #t)
;; ?^13:all p exnc n all n0(n<=n0 -> 0<=RatUDiv(as n0)+(1#2**p))
(assume "q")
(intro 0 (pt "M(PosS p)"))
(assume "n" "nBd")
;; ?^16:0<=RatUDiv(as n)+(1#2**q)
(assert "(1#2**PosS p)<=as n")
(use "RealPosChar1" (pt "M"))
(use "Rx")
(use "0<x")
(use "nBd")
;; Assertion proved.
(assume "asnBd")

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

(use "RatLeTrans" (pt "RatUDiv(as n)"))
;; 35,36
(use "RatLtToLe")
(use "RatPosUDiv")
(use "RatLtLeTrans" (pt "(1#2**PosS p)"))
(use "Truth")
(use "asnBd")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealPosToZeroLeUDiv")

;; RealUDivPosS
(set-goal "all x,p(Real x -> RealPos(1+ ~x)p ->
 Real(RealUDiv(1+ ~x)(PosS p)))")
(assume "x" "p" "Rx" "x<1")
(use "RealUDivReal")
(realproof)
(use "RealPosToPosAbs")
(use "RealPosPosS")
(realproof)
(use "x<1")
;; Proof finished.
;; (cp)
(save "RealUDivPosS")

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
(ng #t)
(use "CauchyIntro")
(ng #t)
(assume "p" "n" "m" "nBd" "mBd")
(use-with "CauchyElim"
	  (pt "[n]as n*bs n")
	  (pt "[p]M(PosS(p+cNatPos(cRBd bs N)))max
                  N(PosS(p+cNatPos(cRBd as M)))")
	  "?" (pt "p") (pt "n") (pt "m") "?" "?")
(use "CauchyTimes")
(use "CasM")
(use "CbsN")
(use "MonM")
(use "MonN")
;; ?^23:all n abs(as n)<=2**cNatPos(cRBd as M)
(assert "Zero<cRBd as M")
(simp "RBdExFree")
(use "Truth")
(use "CasM")
;; Assertion proved.
(assume "xBdPos")

(assert "PosToNat(cNatPos(cRBd as M))=cRBd as M")
(simp "NatPosExFree")
(use "PosToNatToPosId")
(use "xBdPos")
;; Assertion proved.
(assume "EqHyp")
(simp "EqHyp")
(use "RealBdProp")
(use "CasM")
;; ?^24:all n abs(bs n)<=2**cNatPos(cRBd bs N)
(assert "Zero<cRBd bs N")
(simp "RBdExFree")
(use "Truth")
(use "CbsN")
;; Assertion proved.
(assume "yBdPos")

(assert "PosToNat(cNatPos(cRBd bs N))=cRBd bs N")
(simp "NatPosExFree")
(use "PosToNatToPosId")
(use "yBdPos")
;; Assertion proved.
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
(ng #t)
(assume "p" "q" "p<=q")
(use "NatMaxLUB")
;; 53,54
(use "NatLeTrans" (pt "M(PosS(q+cNatPos(cRBd bs N)))"))
(use "MonElim")
(use "MonM")
(ng #t)
(use "p<=q")
(use "NatMaxUB1")
;; 54
(use "NatLeTrans" (pt "N(PosS(q+cNatPos(cRBd as M)))"))
(use "MonElim")
(use "MonN")
(ng #t)
(use "p<=q")
(use "NatMaxUB2")
;; Proof finished.
;; (cdp)
(save "RealTimesReal")

;; RealExpReal
(set-goal "all x,n(Real x -> Real(x**n))")
(assume "x" "n" "Rx")
(ind (pt "n"))
;; Base
(ng #t)
(use "RealRat")
;; Step
(assume "n1" "IH")
(ng #t)
(use "RealTimesReal")
(use "IH")
(use "Rx")
;; Proof finished.
;; (cdp)
(save "RealExpReal")

;; We now aim at RealMaxReal.  To reduce the number of necessary case
;; distinctions we prove RealMaxRealAux , which will be used twice.

;; RealMaxRealAux
(set-goal "all as,bs,n,m,p(
 abs(as m+ ~(as n))<=(1#2**p) ->
 abs(bs n+ ~(bs m))<=(1#2**p) ->
 as n<=bs n -> abs(as n max bs n+ ~(as m max bs m))<=(1#2**p))")
(assume "as" "bs" "n" "m" "p" "asEst" "bsEst" "asn<=bsn")
(cases (pt "as m<=bs m"))
;; 3,4
(assume "asm<=bsm")
(simprat (pf "as n max bs n==bs n"))
(simprat (pf "as m max bs m==bs m"))
(use "bsEst")
(simp "RatMaxEq2")
(use "Truth")
(use "asm<=bsm")
(simp "RatMaxEq2")
(use "Truth")
(use "asn<=bsn")
;; ?^4:(as m<=bs m -> F) -> abs(as n max bs n+ ~(as m max bs m))<=(1#2**p)
(assume "Notasm<=bsm")
(assert "bs m<=as m")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "Notasm<=bsm")
(assume "bsm<=asm")
(drop "Notasm<=bsm")
;; ?^20:abs(as n max bs n+ ~(as m max bs m))<=(1#2**p)
(simprat (pf "as n max bs n==bs n"))
(simprat (pf "as m max bs m==as m"))
(cases (pt "as m<=bs n"))
;; 25,26
(assume "asm<=bsn")
(use "RatLeTrans" (pt "bs n+ ~(bs m)"))
(simp "RatAbsId")
(use "RatLeMonPlus")
(use "Truth")
(use "bsm<=asm")
(use "RatLePlusR")
(use "asm<=bsn")
(use "RatLeTrans" (pt "abs(bs n+ ~(bs m))"))
(use "Truth")
(use "bsEst")
;; ?^26:(as m<=bs n -> F) -> abs(bs n+ ~(as m))<=(1#2**p)
(assume "Notasm<=bsn")
(assert "bs n<=as m")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "Notasm<=bsn")
(assume "bsn<=asm")
(drop "Notasm<=bsn")
;; ?^43:abs(bs n+ ~(as m))<=(1#2**p)
(simp "RatEqAbsMinusCor")
;; 44,45
;; ?^44:as m+ ~(bs n)<=(1#2**p)
(use "RatLeTrans" (pt "as m+ ~(as n)"))
;; 46,47
(use "RatLeMonPlus")
(use "Truth")
(use "asn<=bsn")
;; 47
(use "RatLeTrans" (pt "abs(as m+ ~(as n))"))
(use "Truth")
(use "asEst")
;; 45
(use "bsn<=asm")
;; 24
(simp "RatMaxEq1")
(use "Truth")
(use "bsm<=asm")
;; 22
(simp "RatMaxEq2")
(use "Truth")
(use "asn<=bsn")
;; Proof finished.
;; (cdp)
(save "RealMaxRealAux")

;; RealMaxReal
(set-goal "all x1,x2(Real x1 -> Real x2 -> Real(x1 max x2))")
(assume "x1" "x2" "Rx1" "Rx2")
(elim "Rx1")
(cases)
(assume "as1" "M1" "Cas1M1" "MonM1")
(elim "Rx2")
(cases)
(assume "as2" "M2" "Cas2M2" "MonM2")
(use "RealIntro")
;; 9,10
(ng #t)
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
;; ?^14:abs(as1 n max as2 n+ ~(as1 m max as2 m))<=(1#2**p)
(cases (pt "as1 n<=as2 n"))
;; 15,16
(assume "as1n<=as2n")
(use "RealMaxRealAux")
;; 18-20
(use "CauchyElim" (pt "M1"))
(use "Cas1M1")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB1")
(use "mBd")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB1")
(use "nBd")
;; 19
(use "CauchyElim" (pt "M2"))
(use "Cas2M2")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB2")
(use "nBd")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB2")
(use "mBd")
;; 20
(use "as1n<=as2n")
;; 16
(assume "Notas1n<=as2n")
(assert "as2 n<=as1 n")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "Notas1n<=as2n")
(drop "Notas1n<=as2n")
(assume "as2n<=as1n")
;; ?^41:abs(as1 n max as2 n+ ~(as1 m max as2 m))<=(1#2**p)
(simprat "RatMaxComm")
(simprat (pf "as1 m max as2 m==as2 m max as1 m"))
(use "RealMaxRealAux")
;; 45-47
(use "CauchyElim" (pt "M2"))
(use "Cas2M2")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB2")
(use "mBd")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB2")
(use "nBd")
;; 46
(use "CauchyElim" (pt "M1"))
(use "Cas1M1")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB1")
(use "mBd")
;; 47
(use "as2n<=as1n")
;; 44
(use "RatMaxComm")
;; ?^10:Mon((RealConstr as1 M1 max RealConstr as2 M2)mod)
(ng #t)
(intro 0)
(assume "p" "q" "p<=q")
(ng #t)
(use "NatLeMonMax")
(use "MonElim")
(use "MonM1")
(use "p<=q")
(use "MonElim")
(use "MonM2")
(use "p<=q")
;; Proof finished.
;; (cdp)
(save "RealMaxReal")

;; We now aim at RealMinReal.  To reduce the number of necessary case
;; distinctions we prove RealMinRealAux , which will be used twice.

;; RealMinRealAux
(set-goal "all as,bs,n,m,p(
 abs(as n+ ~(as m))<=(1#2**p) ->
 abs(bs n+ ~(bs m))<=(1#2**p) ->
 as n<=bs n -> abs(as n min bs n+ ~(as m min bs m))<=(1#2**p))")
(assume "as" "bs" "n" "m" "p" "asEst" "bsEst" "asn<=bsn")
(cases (pt "as m<=bs m"))
;; 3,4
(assume "asm<=bsm")
(simprat (pf "as n min bs n==as n"))
(simprat (pf "as m min bs m==as m"))
(use "asEst")
(simp "RatMinEq1")
(use "Truth")
(use "asm<=bsm")
(simp "RatMinEq1")
(use "Truth")
(use "asn<=bsn")
;; ?^4:(as m<=bs m -> F) -> abs(as n min bs n+ ~(as m min bs m))<=(1#2**p)
(assume "Notasm<=bsm")
(assert "bs m<=as m")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "Notasm<=bsm")
(assume "bsm<=asm")
(drop "Notasm<=bsm")
;; ?^20:abs(as n min bs n+ ~(as m min bs m))<=(1#2**p)
(simprat (pf "as n min bs n==as n"))
(simprat (pf "as m min bs m==bs m"))
(cases (pt "bs m<=as n"))
;; 25,26
(assume "bsm<=asn")
(use "RatLeTrans" (pt "bs n+ ~(bs m)"))
(simp "RatAbsId")
(use "RatLeMonPlus")
(use "asn<=bsn")
(use "Truth")
(use "RatLePlusR")
(use "bsm<=asn")
(use "RatLeTrans" (pt "abs(bs n+ ~(bs m))"))
(use "Truth")
(use "bsEst")
;; ?^26:(bs m<=as n -> F) -> abs(as n+ ~(bs m))<=(1#2**p)
(assume "Notbsm<=asn")
(assert "as n<=bs m")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "Notbsm<=asn")
(assume "asn<=bsm")
(drop "Notbsm<=asn")
;; ?^43:abs(as n+ ~(bs m))<=(1#2**p)
(simp "RatEqAbsMinusCor")
;; 44,45
;; ?^44:bs m+ ~(as n)<=(1#2**p)
(use "RatLeTrans" (pt "as m+ ~(as n)"))
(use "RatLeMonPlus")
(use "bsm<=asm")
(use "Truth")
;; ?^47:as m+ ~(as n)<=(1#2**p)
(use "RatLeTrans" (pt "abs(as m+ ~(as n))"))
(use "Truth")
;; ?^51:abs(as m+ ~(as n))<=(1#2**p) ;from abs(as n+ ~(as m))<=(1#2**p)
(simp "RatPlusComm")
(simp (pf "abs(~(as n)+as m)=abs(~(~(as n)+as m))"))
(ng #t)
(use "asEst")
(simp "RatAbs0RewRule")
(use "Truth")
(use "asn<=bsm")
;; ?^24:as m min bs m==bs m
(simp "RatMinEq2")
(use "Truth")
(use "bsm<=asm")
;; ?^22:as n min bs n==as n
(simp "RatMinEq1")
(use "Truth")
(use "asn<=bsn")
;; Proof finished.
;; (cdp)
(save "RealMinRealAux")

;; RealMinReal
(set-goal "all x1,x2(Real x1 -> Real x2 -> Real(x1 min x2))")
(assume "x1" "x2" "Rx1" "Rx2")
(elim "Rx1")
(cases)
(assume "as1" "M1" "Cas1M1" "MonM1")
(elim "Rx2")
(cases)
(assume "as2" "M2" "Cas2M2" "MonM2")
(use "RealIntro")
;; 9,10
(ng #t)
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
;; ?^14:abs(as1 n min as2 n+ ~(as1 m min as2 m))<=(1#2**p)
(cases (pt "as1 n<=as2 n"))
;; 15,16
(assume "as1n<=as2n")
(use "RealMinRealAux")
;; 18-20
(use "CauchyElim" (pt "M1"))
(use "Cas1M1")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB1")
(use "mBd")
;; 19
(use "CauchyElim" (pt "M2"))
(use "Cas2M2")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB2")
(use "nBd")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB2")
(use "mBd")
;; 20
(use "as1n<=as2n")
;; 16
(assume "Notas1n<=as2n")
(assert "as2 n<=as1 n")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "Notas1n<=as2n")
(drop "Notas1n<=as2n")
(assume "as2n<=as1n")
;; ?^41:abs(as1 n min as2 n+ ~(as1 m min as2 m))<=(1#2**p)
(simprat "RatMinComm")
(simprat (pf "as1 m min as2 m==as2 m min as1 m"))
(use "RealMinRealAux")
;; 45-47
(use "CauchyElim" (pt "M2"))
(use "Cas2M2")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB2")
(use "nBd")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB2")
(use "mBd")
;; 46
(use "CauchyElim" (pt "M1"))
(use "Cas1M1")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "M1 p max M2 p"))
(use "NatMaxUB1")
(use "mBd")
;; 47
(use "as2n<=as1n")
;; 44
(use "RatMinComm")
;; ?^10:Mon((RealConstr as1 M1 min RealConstr as2 M2)mod)
(ng #t)
(intro 0)
(assume "p" "q" "p<=q")
(ng #t)
(use "NatLeMonMax")
(use "MonElim")
(use "MonM1")
(use "p<=q")
(use "MonElim")
(use "MonM2")
(use "p<=q")
;; Proof finished.
;; (cdp)
(save "RealMinReal")

;; 7.  Inclusion properties
;; ========================

;; RatPlusRealPlus
(set-goal "all a,b a+b===RealPlus a b")
(assume "a" "b")
(use "RealSeqEqToEq" (pt "Zero"))
(autoreal)
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
(save "RatPlusRealPlus")

;; RatUMinusRealUMinus
(set-goal "all a ~a===RealUMinus a")
(assume "a")
(use "RealSeqEqToEq" (pt "Zero"))
(autoreal)
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RatUMinusRealUMinus")

;; RatTimesRealTimes
(set-goal "all a,b a*b===RealTimes a b")
(assume "a" "b")
(use "RealSeqEqToEq" (pt "Zero"))
(autoreal)
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RatTimesRealTimes")

;; RatUDivRealUDiv
(set-goal "all a,p((1#2**PosS p)<=abs a ->  RatUDiv a===RealUDiv a p)")
(assume "a" "p" "PosHyp")
(assert "Real(RealUDiv a p)")
(use "RealUDivRealPosFree")
(autoreal)
(assume "n" "Useless")
(use "PosHyp")
;; Assertion proved.
(assume "R1/a")
(use "RealSeqEqToEq" (pt "Zero"))
(autoreal)
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RatUDivRealUDiv")

;; RatAbsRealAbs
(set-goal "all a abs a===RealAbs a")
(assume "a")
(use "RealSeqEqToEq" (pt "Zero"))
(autoreal)
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RatAbsRealAbs")

;; RatExpRealExp
(set-goal "all a,n a**n===RealExp a n")
(assume "a")
(assert "all n,m a**n==(RealExp a n)seq m")
;; 3,4
(ind)
(assume "m")
(use "Truth")
(assume "n" "IH" "m")
;; ?^8:a**Succ n==(RealExp a(Succ n))seq m
(simp "RatExpSucc")
(ng #t)
;; ?^10:a*a**n==(RealExp a n*a)seq m

(assert "all x,y(Real x -> Real y -> allnc n (x*y)seq n==x seq n*y seq n)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "Rx" "Ry" "n3")
(use "Truth")
;; Assertion proved.
(assume "seq*")

(simprat "seq*")
(simprat "<-" "IH")
(ng #t)
(simp "RatTimesComm")
(use "Truth")
(autoreal)
;; Assertion proved
(assume "RatExpRealExpNat" "n")
(use "RealSeqEqToEq" (pt "Zero"))
;; 25-27
(autoreal)
(assume "m" "Useless")
(use "RatExpRealExpNat")
;; Proof finished.
;; (cdp)
(save "RatExpRealExp")

;; RatMaxRealMax
(set-goal "all a,b a max b===RealMax a b")
(assume "a" "b")
(use "RealSeqEqToEq" (pt "Zero"))
(autoreal)
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RatMaxRealMax")

;; RatMinRealMin
(set-goal "all a,b a min b===RealMin a b")
(assume "a" "b")
(use "RealSeqEqToEq" (pt "Zero"))
(autoreal)
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RatMinRealMin")

;; 8.  Equality properties for real functions
;; ==========================================

;; For monotonicity properties of RealTimes and compatibilites we need
;; simple equality properties provable without simpreal (and hence
;; compatibilies) and without using RealLe properties.  The main tool
;; is pointwise equality (via RealEqSIntro).

;; RealPlusComm
(set-goal "all x,y(Real x -> Real y -> x+y===y+x)")
(assert "all x,y x+y=+=y+x")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(simp "RatPlusComm")
(use "Truth")
;; Assertion proved.
(assume "RealPlusCommEqS")
(assume "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(autoreal)
(use "RealPlusCommEqS")
;; Proof finished.
;; (cdp)
(save "RealPlusComm")

;; RealPlusAssoc
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x+(y+z)===x+y+z)")
(assert "all x,y,z x+(y+z)=+=x+y+z")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "K")
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
;; (cdp)
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
;; (cdp)
(save "RealZeroPlus")

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

;; RealTimesAssoc
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x*(y*z)===x*y*z)")
(assert "all x,y,z x*(y*z)=+=x*y*z")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "K")
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
(assume "cs" "K")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "RatTimesPlusDistr")
;; Assertion proved.
(assume "RealTimesPlusDistrEqS" "x" "y" "z" "Rx" "Ry" "Rz")
(use "RealEqSToEq")
(autoreal)
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
(assume "cs" "K")
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
;; (cdp)
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

;; RealTimesUDivR ;was RealTimesUDiv
(set-goal "all x,p(Real x -> RealPos x p -> x*RealUDiv x p===1)")
(assume "x" "p" "Rx" "0<x")
(use "RealEqChar2")
(autoreal)
(assume "q")
(inst-with-to "RealPosChar1RealConstrFree"
	      (pt "x")  (pt "p") "Rx" "0<x" "RealPosChar1RealConstrFreeInst")
(intro 0 (pt "x mod(PosS p)"))
(assume "n")
(cases (pt "x"))
(assume "as" "M" "xDef")
(ng #t)
;; ?^13:M(PosS p)<=n -> abs(as n*RatUDiv(as n)+IntN 1)<=(1#2**q)
(assume "nBd")
(simprat "RatTimesUDivR")
(use "Truth")
;; ?^16:0<abs(as n)
(use "RatLtLeTrans" (pt "(1#2**PosS p)"))
(use "Truth")
;; ?^18:(1#2**PosS p)<=abs(as n)
(use "RatLeTrans" (pt "as n"))
(use "RealPosChar1" (pt "M"))
(simp "<-" "xDef")
(use "Rx")
(simp "<-" "xDef")
(use "0<x")
(use "nBd")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealTimesUDivR")

;; RealTimesUDivRPosFree
(set-goal "all x,p(Real x ->
 all n(x mod(PosS p)<=n -> (1#2**PosS p)<=x seq n) -> x*RealUDiv x p===1)")
(cases)
(assume "as" "M" "p" "Rx")
(simp "RealSeq0CompRule")
(simp "RealMod0CompRule")
(assume "0<x")
(use "RealEqChar2")
(use "RealTimesReal")
(use "Rx")
(use "RealUDivRealPosFree")
(use "Rx")
(assume "n" "nBd")
(ng #t)
(use "RatLeTrans" (pt "as n"))
(use "0<x")
(use "nBd")
(use "Truth")
(use "RealRat")
;; 9
(assume "q")
(ng #t)
;; ?^20:exnc n all n0(n<=n0 -> abs(as n0*RatUDiv(as n0)+IntN 1)<=(1#2**q))
(intro 0 (pt "M(PosS p)"))
(assume "n" "nBd")
;; ?^22:abs(as n*RatUDiv(as n)+IntN 1)<=(1#2**q)
(simprat "RatTimesUDivR")
(use "Truth")
;; ?^24:0<abs(as n)
(use "RatLtLeTrans" (pt "(1#2**PosS p)"))
(use "Truth")
(use "RatLeTrans" (pt "as n"))
(use "0<x")
(use "nBd")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealTimesUDivRPosFree")

;; We will need a modified version of RealTimesUDivR, with |x|>0 for x>0

;; RealTimesUDivR2
(set-goal "all x,p(Real x -> RealPos abs x p -> x*RealUDiv x p===1)")
(cases)
(assume "as" "M" "p" "Rx" "0<|x|")
(use "RealEqChar2")
(use "RealTimesReal")
(use "Rx")
(use "RealUDivReal")
(use "Rx")
(use "0<|x|")
(use "RealRat")
(assume "q")
(inst-with-to "RealAbsReal" (pt "RealConstr as M") "Rx" "R|x|")
(inst-with-to "RealPosChar1RealConstrFree"
	      (pt "abs (RealConstr as M)")
	      (pt "p") "R|x|" "0<|x|" "RealPosChar1RealConstrFreeInst")
(intro 0 (pt "M(PosS p)"))
(assume "n" "nBd")
(assert "(1#2**PosS p)<=abs(as n)")
(use "RealPosChar1RealConstrFreeInst")
(use "nBd")
(drop "RealPosChar1RealConstrFreeInst")
(ng #t)
;; Assertion proved.
(assume "(1#2**PosS p)<=|as n|")
(simprat "RatTimesUDivR")
(use "Truth")
(use "RatLtLeTrans" (pt "(1#2**PosS p)"))
(use "Truth")
(use "(1#2**PosS p)<=|as n|")
;; Proof finished.
;; (cdp)
(save "RealTimesUDivR2")

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
;; (cdp)
(save "RealTimesUMinusId")

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
;; (cdp)
(save "RealPlusMinusZero")

;; RealAbsAbs
(set-goal "all x abs abs x eqd abs x")
(cases)
(assume "as" "M")
(ng)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "abs abs x" "abs x")

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
;; (cdp)
(save "RealAbsUMinus")

;; RealAbsUDiv
(set-goal "all x,p(Real x -> RealPos(abs x)p ->
                   abs(RealUDiv x p)===RealUDiv(abs x)p)")
(assume "x" "p" "Rx" "0<|x|")
(use "RealEqChar2")
(use "RealAbsReal")
(use "RealUDivReal")
(use "Rx")
(use "0<|x|")
(use "RealUDivReal")
(realproof)
(use "RealPosToPosAbs")
(use "0<|x|")
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
;; (cdp)
(save "RealAbsUDiv")

;; Code discarded 2023-03-11
;; Reason: the premise RealPos x p is too strong.  Use RealPos(abs x)p
;; ;; RealAbsUDiv
;; (set-goal "all x,p(Real x -> RealPos x p -> 
;;                    abs(RealUDiv x p)===RealUDiv(abs x)p)")
;; (assume "x" "p" "Rx" "0<x")
;; (use "RealEqChar2")
;; (use "RealAbsReal")
;; (use "RealUDivReal")
;; (use "Rx")
;; (use "RealPosToPosAbs")
;; (use "0<x")
;; (use "RealUDivReal")
;; (realproof)
;; (use "RealPosToPosAbs")
;; (use "RealPosToPosAbs")
;; (use "0<x")
;; ;; ?_5:all p0 
;; ;;      exnc n 
;; ;;       all n0(
;; ;;        n<=n0 -> 
;; ;;        abs((abs(RealUDiv x p))seq n0+ ~((RealUDiv abs x p)seq n0))<=
;; ;;        (1#2**p0))
;; (assume "q")
;; (intro 0 (pt "Zero"))
;; (assume "n" "Useless")
;; (cases (pt "x"))
;; (assume "as" "M" "xDef")
;; (ng)
;; (simprat (pf "(RatUDiv abs(as n)+ ~(RatUDiv abs(as n)))==0"))
;; (use "Truth")
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "RealAbsUDiv")

;; RealAbsUDivPosFree
(set-goal "all x,p(Real x ->
 all n(x mod(PosS p)<=n -> (1#2**PosS p)<=x seq n) ->
 abs(RealUDiv x p)===RealUDiv(abs x)p)")
(cases)
(assume "as" "M" "p" "Rx")
(simp "RealSeq0CompRule")
(simp "RealMod0CompRule")
(assume "0<x")
(use "RealEqChar2")
;; 7,8
(use "RealAbsReal")
(use "RealUDivRealPosFree")
(use "Rx")
(ng #t)
;; ?^13:all n(M(PosS p)<=n -> (1#2**PosS p)<=abs(as n))
(assume "n" "nBd")
(use "RatLeTrans" (pt "as n"))
(use "0<x")
(use "nBd")
(use "Truth")
;; ?^8:Real(RealUDiv abs(RealConstr as M)p)
(use "RealUDivRealPosFree")
;; 18,19
(use "RealAbsReal")
(use "Rx")
;; 19
(ng #t)
;; ?^21:all n(M(PosS p)<=n -> (1#2**PosS p)<=abs(as n))
(assume "n" "nBd")
(use "RatLeTrans" (pt "as n"))
(use "0<x")
(use "nBd")
(use "Truth")
;; ?^9:all p0 
;;      exnc n 
;;       all n0(
;;        n<=n0 -> 
;;        abs((abs(RealUDiv(RealConstr as M)p))seq n0+ 
;;            ~((RealUDiv abs(RealConstr as M)p)seq n0))<=
;;        (1#2**p0))
(assume "q")
(intro 0 (pt "Zero"))
(assume "n" "Useless")
(ng #t)
(simprat (pf "(RatUDiv abs(as n)+ ~(RatUDiv abs(as n)))==0"))
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealAbsUDivPosFree")

;; RealUDivUDivReal
(set-goal "all x,p,q(Real x -> Real(RealUDiv(RealUDiv x p)q))")
(cases)
(assume "as" "M" "p" "q" "Rx")
(inst-with-to "RealConstrToCauchy" (pt "as") (pt "M") "Rx" "Cx")
(inst-with-to "RealConstrToMon" (pt "as") (pt "M") "Rx" "MonM")
(ng #t)
;; ?^8:Real
;;     (RealConstr([n]RatUDiv(RatUDiv(as n)))([p0]M(SZero(PosS(PosS(p+q)))+p0)))
(intro 0)
;; 9,10
(ng #t)
(intro 0)
(ng #t)
(assume "p1" "n" "m" "nBd" "mBd")
(simprat "RatUDivUDiv")
(simprat "RatUDivUDiv")
;; ?^16:abs(as n+ ~(as m))<=(1#2**p1)
(use "CauchyElim" (pt "M"))
;; 17-19
(use "Cx")
;; ?^18:M p1<=n
(use "NatLeTrans" (pt "M(SZero(PosS(PosS(p+q)))+p1)"))
(use "MonElim")
(use "MonM")
(use "Truth")
(use "nBd")
;; ?^19:M p1<=m
(use "NatLeTrans" (pt "M(SZero(PosS(PosS(p+q)))+p1)"))
(use "MonElim")
(use "MonM")
(use "Truth")
(use "mBd")
;; 10
(ng #t)
;; Mon([p0]M(SZero(PosS(PosS(p+q)))+p0))
(intro 0)
(ng #t)
(assume "p1" "q1" "p1<=q1")
(use "MonElim")
(use "MonM")
(use "PosLeMonPlus")
(use "Truth")
(use "p1<=q1")
;; Proof finished.
;; (cdp)
(save "RealUDivUDivReal")

;; RealUDivUDiv
(set-goal "all x,p,q(Real x -> RealUDiv(RealUDiv x p)q===x)")
(assume "x" "p" "q" "Rx")
(use "RealEqChar2")
(use "RealUDivUDivReal")
(use "Rx")
(use "Rx")
(assume "p1")
(intro 0 (pt "Zero"))
(assume "n" "Useless")
(cases (pt "x"))
(assume "as" "M" "xDef")
(ng #t)
(simprat "RatUDivUDiv")
(simprat (pf "as n+ ~(as n)==0"))
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealUDivUDiv")

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
;; (cdp)
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
;; (cdp)
(save "RealTimesPlusOneDistrLeft")

;; 9.  Monotonicity and compatibility
;; ==================================

;; We prove monotonicity and compatibility properties for RealPlus
;; RealUMinus RealTimes RealUDiv RealAbs RealExp RealMax RealMin

;; RealLeCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x<<=z -> y<<=z1)")
(assume "x" "y" "z" "z1" "x=y" "z=z1" "x<=z")
(use "RealLeTrans" (pt "x"))
(use "RealEqElim1")
(use "x=y")
(use "RealLeTrans" (pt "z"))
(use "x<=z")
(use "RealEqElim0")
(use "z=z1")
;; Proof finished.
;; (cdp)
(save "RealLeCompat")

;; RealLeMonPlusR
(set-goal "all x,y,z(Real x -> y<<=z -> x+y<<=x+z)")
(assume "x" "y" "z" "Rx" "y<=z")
(assert "Real(x+y)")
(autoreal)
(assume "Rx+y")
(assert "Real(x+z)")
(autoreal)
(assume "Rx+z")
(use "RealLeChar2RealConstrFree")
(autoreal)
(assume "p")
;; ?^12:exnc n all n0(n<=n0 -> (x+y)seq n0<=(x+z)seq n0+(1#2**p))
(assert "exnc n all n0(n<=n0 -> y seq n0<=z seq n0+(1#2**p))")
(use "RealLeChar1RealConstrFree")
(use "y<=z")
;; ?^13:exnc n all n0(n<=n0 -> y seq n0<=z seq n0+(1#2**p)) -> 
;;      exnc n all n0(n<=n0 -> (x+y)seq n0<=(x+z)seq n0+(1#2**p))
(cases (pt "x"))
(assume "as" "M" "xDef")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z"))
(assume "cs" "K" "zDef")
(ng #t)
;; ?^22:exnc n all n0(n<=n0 -> bs n0<=cs n0+(1#2**p)) -> 
;;      exnc n all n0(n<=n0 -> as n0+bs n0<=as n0+cs n0+(1#2**p))
(assume "nEx")
(by-assume "nEx" "n" "nProp")
(intro 0 (pt "n"))
(assume "m" "n<=m")
(simp "<-" "RatPlusAssoc")
(use "RatLeMonPlus")
(use "Truth")
(use "nProp")
(use "n<=m")
;; Proof finished.
;; (cdp)
(save "RealLeMonPlusR")

;; RealLeMonPlus
(set-goal "all x,y,z(Real x -> y<<=z -> y+x<<=z+x)")
(assume "x" "y" "z" "Rx" "y<=z")
(simpreal "RealPlusComm")
(simpreal (pf "z+x===x+z"))
(use "RealLeMonPlusR")
(autoreal)
(use "y<=z")
(use "RealPlusComm")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeMonPlus")

;; RealLeMonPlusTwo
(set-goal "all x,y,z,z0(x<<=y -> z<<=z0 -> x+z<<=y+z0)")
(assume "x" "y" "z" "z0" "x<=y" "z<=z0")
(use "RealLeTrans" (pt "y+z"))
(use "RealLeMonPlus")
(autoreal)
(use "x<=y")
(use "RealLeMonPlusR")
(autoreal)
(use "z<=z0")
;; Proof finished.
;; (cdp)
(save "RealLeMonPlusTwo")

;; RealEqCompat
(set-goal "all x,y,z,z0(x===y -> z===z0 -> x===z -> y===z0)")
(assume "x" "y" "z" "z0" "x=y" "z=z0" "x=z")
(use "RealEqTrans" (pt "x"))
(use "RealEqSym")
(use "x=y")
(use "RealEqTrans" (pt "z"))
(use "x=z")
(use "z=z0")
;; Proof finished.
(save "RealEqCompat")

;; RealPlusCompat
(set-goal "all x,y,z,z0(x===y -> z===z0 -> x+z===y+z0)")
(assume "x" "y" "z" "z0" "x=y" "z=z0")
(use "RealLeAntiSym")
;; 3,4
(use "RealLeMonPlusTwo")
(use "RealEqElim0")
(use "x=y")
(use "RealEqElim0")
(use "z=z0")
;; 4
(use "RealLeMonPlusTwo")
(use "RealEqElim1")
(use "x=y")
(use "RealEqElim1")
(use "z=z0")
;; Proof finished.
;; (cdp)
(save "RealPlusCompat")

;; We now aim at RealUMinusCompat .  This needs sompe preparations
;; (from archive/koepp/lub_lemma.scm and lub_sqrt.scm )

;; RealLePlusL
(set-goal "all x,y,z(Real x -> Real z -> y<<= ~x+z -> x+y<<=z)")
(assume "x" "y" "z" "Rx" "Rz" "y<<= ~x+z")
(use "RealLeTrans" (pt "x+(~x+z)"))
(use "RealLeMonPlusR")
(autoreal)
(use "y<<= ~x+z")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusComm")
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLePlusL")

;; RealLePlusLInv
(set-goal "all x,y,z(Real x -> Real y -> x+y<<=z -> y<<= ~x+z)")
(assume "x" "y" "z" "Rx" "Ry" "x+y<=z")
(simpreal (pf "y=== ~x+x+y"))
(simpreal "<-" "RealPlusAssoc")
(use "RealLeMonPlusR")
(autoreal)
(use "x+y<=z")
(autoreal)
(simpreal "<-" (pf "x+ ~x=== ~x+x"))
(simpreal "RealPlusMinusZero")
(simpreal "RealZeroPlus")
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLePlusLInv")

;; RealLePlusR
(set-goal "all x,y,z(Real x -> Real y -> ~y+x<<=z -> x<<=y+z)")
(assume "x" "y" "z" "Rx" "Ry" "~y+x<=z")
(simpreal (pf "x===y+ ~y+x"))
(simpreal "<-" "RealPlusAssoc")
(simpreal "RealPlusMinusZero")
(use "RealLeMonPlusR")
(autoreal)
(use "~y+x<=z")
(autoreal)
(simpreal "RealPlusMinusZero")
(simpreal "RealZeroPlus")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLePlusR")

;; RealLePlusRInv
(set-goal "all x,y,z(Real y -> Real z -> x<<=y+z -> ~y+x<<=z )")
(assume "x" "y" "z" "Ry" "Rz" "x<=y+z")
(use "RealLeTrans" (pt "~y+y+z"))
(simpreal "<-" "RealPlusAssoc")
(use "RealLeMonPlusR")
(autoreal)
(use "x<=y+z")
(autoreal)
(simpreal (pf "~y+y===y+ ~y"))
(simpreal "RealPlusMinusZero")
(simpreal "RealZeroPlus")
(use "RealLeRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLePlusRInv")

;; RealLePlusUMinus
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x+ ~y<<=z -> x+ ~z<<=y)")
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

;; RealLeUMinus
(set-goal "all x,y(x<<=y -> ~y<<= ~x)")
(assume "x" "y" "x<=y")
(assert "Real(~x)")
(autoreal)
(assume "R~x")
(assert "Real(~y)")
(autoreal)
(assume "R~y")
(use "RealLeChar2RealConstrFree")
(autoreal)
(assume "p")
;; ?^12:exnc n all n0(n<=n0 -> (~y)seq n0<=(~x)seq n0+(1#2**p))
(assert "exnc n all n0(n<=n0 -> x seq n0<=y seq n0+(1#2**p))")
(use "RealLeChar1RealConstrFree")
(use "x<=y")
;; ?^13:exnc n all n0(n<=n0 -> x seq n0<=y seq n0+(1#2**p)) -> 
;;      exnc n all n0(n<=n0 -> (~y)seq n0<=(~x)seq n0+(1#2**p))
(cases (pt "x"))
(assume "as" "M" "xDef")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(ng #t)
;; ?^20:exnc n all n0(n<=n0 -> as n0<=bs n0+(1#2**p)) -> 
;;      exnc n all n0(n<=n0 -> ~(bs n0)<= ~(as n0)+(1#2**p))
(assume "nEx")
(by-assume "nEx" "n" "nProp")
(intro 0 (pt "n"))
(assume "m" "n<=m")
(use "RatLePlusR")
(ng #t)
(simp "RatPlusComm")
(use "RatLePlusRInv")
(use "nProp")
(use "n<=m")
;; Proof finished.
;; (cdp)
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
;; (cdp)
(save "RealLeUMinusInv")

;; RealUMinusCompat
(set-goal "all x,y(x===y -> ~x=== ~y)")
(assume "x" "y" "x=y")
(use "RealLeAntiSym")
;; 3,4
(use "RealLeUMinus")
(use "RealEqElim1")
(use "x=y")
;; 4
(use "RealLeUMinus")
(use "RealEqElim0")
(use "x=y")
;; Proof finished.
;; (cdp)
(save "RealUMinusCompat")

;; RealUMinusInj
(set-goal "all x,y(~x=== ~y -> x===y)")
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
;; (cdp)
(save "RealUMinusInj")

;; We now aim at RealLeMonTimesTwo

;; (pp "RealLeChar1")
;; (pp "RatZeroLePlusEqUMinusLe")
;; In RealLeChar1 a<=b+(1#2**p) occurs.
;; It will be easier to work with ~(1#2**p)+a<=b than with 0<=a+(1#2**p)
;; By RatZeroLePlusEqUMinusLe both atoms are the same.

;; First we need
;; RealZeroLeToZeroLeTimes
(set-goal "all x,y(0<<=x -> 0<<=y -> 0<<=x*y)")
(assume "x" "y" "0<=x" "0<=y")
(assert "Real(x*y)")
(autoreal)
(assume "Rx*y")
(use "RealLeChar2RealConstrFree")
(autoreal)
(assume "p")
;; ?^9:exnc n all n0(n<=n0 -> 0 seq n0<=(x*y)seq n0+(1#2**p))
(cases (pt "x"))
(assume "as" "M" "xDef")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(ng #t)
;; ?^14:exnc n all n0(n<=n0 -> 0<=as n0*bs n0+(1#2**p))

(defnc "n1" "cRBd as M")
(defnc "n2" "cRBd bs N")
(defnc "n" "n1 max n2")
;; 35

(assert "all l abs(as l)<=2**n")
(assume "l")
(simp "nDef")
(use "RatLeTrans" (pt "(2**n1#1)"))
(simp "n1Def")
(use "RealBdProp")
(use "RealConstrToCauchy")
(simp "<-" "xDef")
(autoreal)
;; ?^41:RatLe(2**n1)(2**(n1 max n2))
(ng #t)
(use "NatLeMonTwoExp")
(use "NatMaxUB1")
;; Assertion proved.
(assume "xBd")
;; 48

(assert "all l abs(bs l)<=2**n")
(assume "l")
(simp "nDef")
(use "RatLeTrans" (pt "(2**n2#1)"))
(simp "n2Def")
(use "RealBdProp")
(use "RealConstrToCauchy")
(simp "<-" "yDef")
(autoreal)
;; ?^54:RatLe(2**n2)(2**(n1 max n2))
(ng #t)
(use "NatLeMonTwoExp")
(use "NatMaxUB2")
;; Assertion proved.
(assume "yBd")
;; 61

(assert "exnc n3 allnc n(n3<=n -> ([n](0#1))n<=as n+(1#2**p))")
(use "RealLeChar1" (pt "[p]Zero") (pt "M"))
(simp "<-" "xDef")
(use "0<=x")
;; Assertion proved.
(ng #t)
;; ?^66:exnc n allnc n0(n<=n0 -> 0<=as n0+(1#2**p)) -> 
;;      exnc n all n0(n<=n0 -> 0<=as n0*bs n0+(1#2**p))
(assume "n3Ex")
(by-assume "n3Ex" "n3" "n3Prop")

(assert "exnc n5 allnc n0(n5<=n0 -> ~(1#2**p)<=as n0)")
(intro 0 (pt "n3"))
(assume "m")
(simp "<-" "RatZeroLePlusEqUMinusLe")
(use "n3Prop")
;; Assertion proved.
(drop "n3Prop")
(assume "aProp")

(assert "exnc n4 allnc n(n4<=n -> ([n](0#1))n<=bs n+(1#2**p))")
(use "RealLeChar1" (pt "[p]Zero") (pt "N"))
(simp "<-" "yDef")
(use "0<=y")
;; Assertion proved.
(ng #t)
;; ?^82:exnc n allnc n0(n<=n0 -> 0<=bs n0+(1#2**p)) -> 
;;      exnc n all n0(n<=n0 -> 0<=as n0*bs n0+(1#2**p))
(assume "n4Ex")
(by-assume "n4Ex" "n4" "n4Prop")

(assert "exnc n6 allnc n0(n6<=n0 -> ~(1#2**p)<=bs n0)")
(intro 0 (pt "n4"))
(assume "m")
(simp "<-" "RatZeroLePlusEqUMinusLe")
(use "n4Prop")
;; Assertion proved.
(drop "n4Prop")
(assume "bProp")

;;   x  y  0<=x:0<<=x
;;   0<=y:0<<=y
;;   Rx*y:Real(x*y)
;;   p  as  M  xDef:x eqd RealConstr as M
;;   bs  N  yDef:y eqd RealConstr bs N
;;   {n1}  n1Def:n1 eqd cRBd as M
;;   {n2}  n2Def:n2 eqd cRBd bs N
;;   {n}  nDef:n eqd n1 max n2
;;   xBd:all l abs(as l)<=2**n
;;   yBd:all l abs(bs l)<=2**n
;;   {n3}  aProp:exnc n allnc n0(n<=n0 -> ~(1#2**p)<=as n0)
;;   {n4}  bProp:exnc n allnc n0(n<=n0 -> ~(1#2**p)<=bs n0)
;; -----------------------------------------------------------------------------
;; ?^93:exnc n all n0(n<=n0 -> 0<=as n0*bs n0+(1#2**p))

(defnc "n5" "PosToNat(NatToPos(p+n))")

(inst-with-to
"RealLeChar1RealConstrFree" (pt "RealConstr([n](0#1))([p]Zero)") (pt "x")
"0<=x" (pt "NatToPos(p+n)") "Inst")
(simphyp-to "Inst" "xDef" "SimpInst")
(drop "Inst")
(simphyp-to "SimpInst" "<-" "n5Def" "SSInst")
(drop "SimpInst")
(ng "SSInst")
(by-assume "SSInst" "m1" "m1Prop")
;;   {m1}  m1Prop:all n(m1<=n -> 0<=as n+(1#2**n5))
;; -----------------------------------------------------------------------------
;; ?^112:exnc n all n0(n<=n0 -> 0<=as n0*bs n0+(1#2**p))

(assert "all n(m1<=n -> ~(1#2**n5)<=as n)")
(assume "n6")
(simp "<-" "RatZeroLePlusEqUMinusLe")
(use "m1Prop")
(assume "m1PropUMinus")
(drop "m1Prop")
;; 118
(inst-with-to
"RealLeChar1RealConstrFree" (pt "RealConstr([n](0#1))([p]Zero)") (pt "y")
"0<=y" (pt "NatToPos(p+n)") "yInst")
(simphyp-to "yInst" "yDef" "SimpyInst")
(drop "yInst")
(simphyp-to "SimpyInst" "<-" "n5Def" "SSyInst")
(drop "SimpyInst")
(ng "SSyInst")
(by-assume "SSyInst" "m2" "m2Prop")
;;   {m1}  m1PropUMinus:all n(m1<=n -> ~(1#2**n5)<=as n)
;;   {m2}  m2Prop:all n(m2<=n -> 0<=bs n+(1#2**n5))
;; -----------------------------------------------------------------------------
;; ?^130:exnc n all n0(n<=n0 -> 0<=as n0*bs n0+(1#2**p))

(assert "all n(m2<=n -> ~(1#2**n5)<=bs n)")
(assume "n6")
(simp "<-" "RatZeroLePlusEqUMinusLe")
(use "m2Prop")
(assume "m2PropUMinus")
(drop "m2Prop")

;;   x  y  0<=x:0<<=x
;;   0<=y:0<<=y
;;   Rx*y:Real(x*y)
;;   p  as  M  xDef:x eqd RealConstr as M
;;   bs  N  yDef:y eqd RealConstr bs N
;;   {n1}  n1Def:n1 eqd cRBd as M
;;   {n2}  n2Def:n2 eqd cRBd bs N
;;   {n}  nDef:n eqd n1 max n2
;;   xBd:all l abs(as l)<=2**n
;;   yBd:all l abs(bs l)<=2**n
;;   {n3}  aProp:exnc n allnc n0(n<=n0 -> ~(1#2**p)<=as n0)
;;   {n4}  bProp:exnc n allnc n0(n<=n0 -> ~(1#2**p)<=bs n0)
;;   {n5}  n5Def:n5 eqd PosToNat(NatToPos(p+n))
;;   {m1}  m1PropUMinus:all n(m1<=n -> ~(1#2**n5)<=as n)
;;   {m2}  m2PropUMinus:all n(m2<=n -> ~(1#2**n5)<=bs n)
;; -----------------------------------------------------------------------------
;; ?^136:exnc n all n0(n<=n0 -> 0<=as n0*bs n0+(1#2**p))

(defnc "m" "m1 max m2")
(intro 0 (pt "m"))
(assume "l" "m<=l")
(simp "RatZeroLePlusEqUMinusLe")
;;   {m}  mDef:m eqd m1 max m2
;;   l  m<=l:m<=l
;; -----------------------------------------------------------------------------
;; ?^146:~(1#2**p)<=as l*bs l
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
(use "RatLeTrans" (pt "(2**cRBd bs N#1)"))
(use "RatLeTrans" (pt "abs(bs l)"))
(use "Truth")
(use "RealBdProp")
(use "RealConstrToCauchy")
(simp "<-" "yDef")
(realproof)
(simp "nDef")
;; ?^180:RatLe(2**cRBd bs N)(2**(n1 max n2))
(simp "<-" "n2Def")
(ng #t)
(use "PosLeMonPosExp")
(use "NatMaxUB2")
(assume "bs l<=2**n")
(use "RatLeTrans" (pt "~(1#2**(NatToPos(p+n)))*2**n"))
;; 185,186
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
;; 200,201
(use "RatLeMonTimes")
(use "Truth")
;; ?^203:~(1#2**NatToPos(p+n))<=as l
(simp "<-" "n5Def")
(use "m1PropUMinus")
(use "NatLeTrans" (pt "m"))
(simp "mDef")
(use "NatMaxUB1")
(use "m<=l")
;; 201
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
;; 148
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
;; 227
(assume "0<=bs l -> F")
(assert "bs l<=0")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "0<=bs l -> F")
(assume "bs l<=0")
(assert "as l<=2**n")
(use "RatLeTrans" (pt "(2**cRBd as M#1)"))
(use "RatLeTrans" (pt "abs(as l)"))
(use "Truth")
(use "RealBdProp")
(use "RealConstrToCauchy")
(simp "<-" "xDef")
(realproof)
(simp "nDef")
;; ?^253:RatLe(2**cRBd as M)(2**(n1 max n2))
(simp "<-" "n1Def")
(ng #t)
(use "PosLeMonPosExp")
(use "NatMaxUB1")
(assume "as l<=2**n")
(use "RatLeTrans" (pt "~(1#2**(NatToPos(p+n)))*2**n"))
;; 258,259
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
;; 273,274
(use "RatLeMonTimes")
(use "Truth")
;; ?^276:~(1#2**NatToPos(p+n))<=bs l
(simp "<-" "n5Def")
(use "m2PropUMinus")
(use "NatLeTrans" (pt "m"))
(simp "mDef")
(use "NatMaxUB2")
(use "m<=l")
;; 274
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
(save "RealZeroLeToZeroLeTimes")

;; RealLeMonTimesR
(set-goal "all x,y,z(0<<=x -> y<<=z -> x*y<<=x*z)")
(assume "x" "y" "z" "0<=x" "y<=z")
(simpreal (pf "x*y===x*y+0"))
(use "RealLePlusL")
(autoreal)
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
(use "RealZeroLeToZeroLeTimes")
;; 15,16
(use "0<=x")
(use "RealLePlusLInv")
(autoreal)
(simpreal "RealPlusZero")
(use "y<=z")
(autoreal)
(use "RealEqSym")
(use "RealPlusZero")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeMonTimesR")

;; RealLeMonTimes
(set-goal "all x,y,z(0<<=x -> y<<=z -> y*x<<=z*x)")
(assume "x" "y" "z" "0<=x" "y<=z")
(simpreal (pf "y*x===x*y"))
(simpreal (pf "z*x===x*z"))
(use "RealLeMonTimesR")
(use "0<=x")
(use "y<=z")
(use "RealTimesComm")
(autoreal)
(use "RealTimesComm")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeMonTimes")

;; RealLeMonTimesTwo
(set-goal
 "all x,y,z,z0(0<<=x -> 0<<=z -> x<<=y -> z<<=z0 -> x*z<<=y*z0)")
(assume "x" "y" "z" "z0" "0<=x" "0<=z" "x<=y" "z<=z0")
(use "RealLeTrans" (pt "x*z0"))
(use "RealLeMonTimesR")
(use "0<=x")
(use "z<=z0")
(use "RealLeMonTimes")
(use "RealLeTrans" (pt "z"))
(use "0<=z")
(use "z<=z0")
(use "x<=y")
;; Proof finished.
;; (cdp)
(save "RealLeMonTimesTwo")

;; RealTimesCompat
(set-goal "all x,y,z,z0(x===y -> z===z0 -> x*z===y*z0)")
;; We first prove RealTimesCompatAux
(assert  "all x,y,z(Real z -> x===y -> x*z===y*z)")
(assume "x" "y" "z" "Rz" "x=y")
(cases (pt "x"))
(assume "as" "M" "xDef")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z"))
(assume "cs" "K" "zDef")
(simp "<-" "xDef")
(simp "<-" "yDef")
(simp "<-" "zDef")
(use "RealEqChar2")
(autoreal)
(simp "xDef")
(simp "yDef")
(simp "zDef")
(ng #t)
(assume "p")
;; ?^21:exnc n all n0(n<=n0 -> abs(as n0*cs n0+ ~(bs n0*cs n0))<=(1#2**p))
(inst-with-to "RealEqChar1"
              (pt "x") (pt "y") "x=y" (pt "p+cNatPos(cRBd cs K)") "nEx")
(by-assume "nEx" "n" "nProp")
(intro 0 (pt "n"))
(assume "m" "n<=m")
(simp (pf "~(bs m*cs m)= ~(bs m)*cs m"))
(simprat-with "<-" "RatTimesPlusDistrLeft"
	      (pt "as m")(pt "~(bs m)") (pt "cs m"))
(simp "RatAbsTimes")
(use "RatLeTrans"
     (pt "(1#2**(p+cNatPos(cRBd cs K)))*(2**cRBd cs K)"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
;; ?^37:abs(as m+ ~(bs m))<=(1#2**(p+cNatPos(cRBd cs K)))
(use "RatLeTrans" (pt "abs(x seq m+ ~(y seq m))"))
;; 39,40
(simp "xDef")
(simp "yDef")
(use "Truth")
;; 40
(use "nProp")
(use "n<=m")
;; ?^38:abs(cs m)<=2**cRBd cs K
(use "RealBdProp")
(use "RealConstrToCauchy")
(simp "<-" "zDef")
(use "Rz")
(defnc "l" "cRBd cs K")
(simp "<-" "lDef")
(ng #t)
(simp "<-" "PosExpTwoPosPlus")
;; ?^56:2**l*2**p<=2**p*2**cNatPos l
(assert "PosToNat(cNatPos(cRBd cs K))=cRBd cs K")
(simp "NatPosExFree")
(use "PosToNatToPosId")
(use "RealBdPos")
(assume "EqHyp")
(simp "lDef")
(simp "EqHyp")
(simp "PosTimesComm")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "RealTimesCompatAux")
(assume "x" "y" "z" "z0" "x=y" "z=z0")
(use "RealEqTrans" (pt "y*z"))
(use "RealTimesCompatAux")
(autoreal)
(use "x=y")
(use "RealEqTrans" (pt "z*y"))
(use "RealTimesComm")
(autoreal)
(use "RealEqTrans" (pt "z0*y"))
(use "RealTimesCompatAux")
(autoreal)
(use "z=z0")
(use "RealTimesComm")
(autoreal)
;; Proof finished
;; (cdp)
(save "RealTimesCompat")

;; RealUDivCompat below is formulated with two occurrences of q.  This
;; is for simplicity only: in RealUDiv x q the argument q only affects
;; the modulus, and increasing q preserves validity.

;; RealUDivCompat
(set-goal "all x,y,q(x===y -> RealPos abs x q -> RealPos abs y q -> 
                     RealUDiv x q===RealUDiv y q)")
(assume "x" "y" "q" "x=y" "0<|x|" "0<|y|")
(use "RealEqChar2")
(autoreal)
(assert "all p exnc n1 all n(n1<=n -> abs(y seq n+ ~(x seq n))<=(1#2**p))")
(use "RealEqChar1")
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
(assume "as" "M" "xDef" "asProp")
(cases (pt "y"))
(assume "bs" "N" "yDef" "bsProp" "EqChar" "p")
(ng)
;;   asProp:all n(M(PosS q)<=n -> (1#2**PosS q)<=abs(as n))
;;   bsProp:all n(N(PosS q)<=n -> (1#2**PosS q)<=abs(bs n))
;;   EqChar:all p exnc n all n0(n<=n0 -> abs(bs n0+ ~(as n0))<=(1#2**p))
;; -----------------------------------------------------------------------------
;; ?^22:exnc n all n0(n<=n0 -> abs(RatUDiv(as n0)+ ~(RatUDiv(bs n0)))<=(1#2**p))
(inst-with-to "EqChar" (pt "SZero(PosS q)+p") "EqCharInst")
(by-assume "EqCharInst" "l" "lProp")
(intro 0 (pt "l max M(PosS q)max N(PosS q)"))
(assume "n" "nBd")
;;   asProp:all n(M(PosS q)<=n -> (1#2**PosS q)<=abs(as n))
;;   bsProp:all n(N(PosS q)<=n -> (1#2**PosS q)<=abs(bs n))
;;   p  {l}  lProp:all n(l<=n -> abs(bs n+ ~(as n))<=(1#2**(SZero(PosS q)+p)))
;;   n  nBd:l max M(PosS q)max N(PosS q)<=n
;; -----------------------------------------------------------------------------
;; ?^29:abs(RatUDiv(as n)+ ~(RatUDiv(bs n)))<=(1#2**p)
(simprat (pf "RatUDiv(as n)==(bs n)*RatUDiv((as n)*(bs n))"))
(simprat (pf "RatUDiv(bs n)==(as n)*RatUDiv((as n)*(bs n))"))
(simprat "RatUDivTimes")
(simp "<-" "RatTimes4RewRule")
(simprat "<-" "RatTimesPlusDistrLeft")
(simp "RatAbsTimes")
(simp "RatAbsTimes")
(simp "RatTimesAssoc")
;; ?^39:abs(bs n+ ~(as n))*abs(RatUDiv(as n))*abs(RatUDiv(bs n))<=(1#2**p)
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
;; ?^50:abs(bs n+ ~(as n))<=(1#2**(SZero(PosS q)+p))
(use "lProp")
(use "NatLeTrans" (pt "l max(M(PosS q)max N(PosS q))"))
(use "NatMaxUB1")
(use "nBd")
;; ?^51:abs(RatUDiv(as n))<=2**PosS q
(ng)
(simprat (pf "2**PosS q==RatUDiv(RatUDiv(2**PosS q))"))
(use "RatLeUDivUDiv")
(ng)
(use "Truth")
(use "asProp")
(use "NatLeTrans" (pt "l max M(PosS q)"))
(use "NatMaxUB2")
(use "NatLeTrans" (pt "l max M(PosS q)max N(PosS q)"))
(use "NatMaxUB1")
(use "nBd")
;; ?^58:2**PosS q==RatUDiv(RatUDiv(2**PosS q))
(use "RatEqvSym")
(use "RatUDivUDiv")
;; ?^45:(1#2**p)==(1#2**(SZero(PosS q)+p))*2**PosS q*2**PosS q
(ng)
(simprat (pf "2**PosS q==RatUDiv(RatUDiv(2**PosS q))"))
(use "RatLeUDivUDiv")
(ng)
(use "Truth")
(ng)
(use "bsProp")
(use "NatLeTrans" (pt "l max M(PosS q)max N(PosS q)"))
(use "NatMaxUB2")
(use "nBd")
;; ?^70:2**PosS q==RatUDiv(RatUDiv(2**PosS q))
(use "RatEqvSym")
(use "RatUDivUDiv")
;; ?^41:(1#2**p)==(1#2**(SZero(PosS q)+p))*2**PosS q*2**PosS q
(ng)
;; ?^79:2**(SZero(PosS q)+p)=2**PosS q*2**PosS q*2**p
(simp "<-" "PosExpTwoPosPlus")
(simp (pf "SZero(PosS q)=PosS q+PosS q"))
(simp "<-" "PosExpTwoPosPlus")
(use "Truth")
(use "SZeroPosPlus")
;; ?^33:RatUDiv(bs n)==as n*RatUDiv(as n*bs n)
(use "RatUDivExpandL")
;; ?^84:0<abs(as n)
(use "RatLtLeTrans" (pt "(1#2**PosS q)"))
(use "Truth")
(use "asProp")
(use "NatLeTrans" (pt "l max M(PosS q)"))
(use "NatMaxUB2")
(use "NatLeTrans" (pt "l max M(PosS q)max N(PosS q)"))
(use "NatMaxUB1")
(use "nBd")
;; ?^31:RatUDiv(as n)==bs n*RatUDiv(as n*bs n)
(use "RatUDivExpandR")
;; ?^92:0<abs(bs n)
(use "RatLtLeTrans" (pt "(1#2**PosS q)"))
(use "Truth")
(use "bsProp")
(use "NatLeTrans" (pt "l max M(PosS q)max N(PosS q)"))
(use "NatMaxUB2")
(use "nBd")
;; Proof finished.
;; (cdp)
(save "RealUDivCompat")

(set-goal  "all x,y(x===y -> abs x===abs y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x=y")
(use "RealEqChar2")
(autoreal)
(assume "p")
(ng)
(inst-with-to
"RealEqChar1"
(pt "RealConstr as M") (pt "RealConstr bs N") "x=y" (pt "p") "nEx")
(ng "nEx")
(by-assume "nEx" "n" "nProp")
(intro 0 (pt "n"))
(assume "m" "n<=m")
(use "RatLeTrans" (pt "abs(as m+ ~(bs m))"))
(use "RatLeAbsMinusAbs")
(use "nProp")
(use "n<=m")
;; Proof finished.
;; (cdp)
(save "RealAbsCompat")

;; Properties of RealExp

;; RealLeMonExp
(set-goal "all x(1<<=x -> all n,m(n<=m -> x**n<<=x**m))")
(assume "x" "1<=x")
(assert "0<<=x")
(use "RealLeTrans" (pt "RealConstr([n](1#1))([p]Zero)"))
(use "RatLeToRealLe")
(use "Truth")
(use "1<=x")
;; Assertion proved.
(assume "0<=x")
(ind)
;; Base
(ng #t)
(ind)
;; BaseBase
(assume "Useless")
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
;; BaseStep
(assume "m" "IHm" "Useless")
(ng #t)
(use "RealLeTrans" (pt "RealTimes 1 x"))
(simpreal "RealOneTimes")
(use "1<=x")
(autoreal)
(use "RealLeMonTimes")
(use "0<=x")
(use "IHm")
(use "Truth")
;; Step
(assume "n" "IH")
(cases)
(assume "Absurd")
(use "EfRealLe")
(use "Absurd")
(assume "m" "n<=m")
(ng #t)
;; ?^32:x**n*x<<=x**m*x
(use "RealLeMonTimes")
(use "0<=x")
(use "IH")
(use "n<=m")
;; Proof finished.
;; (cdp)
(save "RealLeMonExp")

;; RealLeMonExpDecr
(set-goal "all x(0<<=x -> x<<=1 -> all n,m(n<=m -> x**m<<=x**n))")
(assume "x" "0<=x" "x<=1")
(ind)
;; Base
(ng #t)
(ind)
;; BaseBase
(assume "Useless")
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
;; BaseStep
(assume "m" "IHm" "Useless")
(ng #t)
(use "RealLeTrans" (pt "RealTimes 1 x"))
(use "RealLeMonTimes")
(use "0<=x")
(use "IHm")
(use "Truth")
(simpreal "RealOneTimes")
(use "x<=1")
(autoreal)
;; Step
(assume "n" "IH")
(cases)
(assume "Absurd")
(use "EfRealLe")
(use "Absurd")
(assume "m" "n<=m")
(ng #t)
;; ?^26:x**m*x<<=x**n*x
(use "RealLeMonTimes")
(use "0<=x")
(use "IH")
(use "n<=m")
;; Proof finished.
;; (cdp)
(save "RealLeMonExpDecr")

;; RealExpZeroLe
(set-goal "all x(0<<=x -> all n 0<<=x**n)")
(assume "x" "0<=x")
(ind)
(use "RatLeToRealLe")
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "RealZeroLeToZeroLeTimes")
(use "IH")
(use "0<=x")
;; Proof finished.
;; (cdp)
(save "RealExpZeroLe")

;; RealExpLeOne
(set-goal "all x(0<<=x -> x<<=1 -> all n x**n<<=1)")
(assume "x" "0<=x" "x<=1")
(ind)
(use "RatLeToRealLe")
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "RealLeTrans" (pt "RealTimes 1 1"))
(use "RealLeMonTimesTwo")
;; 10-13
(use "RealExpZeroLe")
(use "0<=x")
;; 11
(use "0<=x")
;; 12
(use "IH")
;; 13
(use "x<=1")
;; 9
(use "RatLeToRealLe")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealExpLeOne")

;; RealLeMonExpBase
(set-goal "all x,y,n(0<<=x -> x<<=y -> x**n<<=y**n)")
(assume "x" "y" "n" "0<=x" "x<=y")
(ind (pt "n"))
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
(assume "m" "IH")
(ng #t)
(use "RealLeMonTimesTwo")
(use "RealExpZeroLe")
(use "0<=x")
(use "0<=x")
(use "IH")
(use "x<=y")
;; Proof finished.
;; (cdp)
(save "RealLeMonExpBase")

;; RealExpPlus
(set-goal "all x,n,m(Real x -> x**(n+m)===x**n *x**m)")
(assume "x" "n" "m" "Rx")

(ind (pt "m"))
;; Base
(ng #t)
(simpreal "RealTimesOne")
(use "RealEqRefl")
(autoreal)
;; Step
(assume "m1" "IH")
(ng #t)
(simpreal "IH")
(simpreal "RealTimesAssoc")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealExpPlus")

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
;; (cdp)
(save "RatEqvToRealEq")

;; RealEqToRatEqv
(set-goal "all a,b(a===b -> a==b)")
(assume "a" "b" "a===b")
(use "RatLeAntiSym")
;; 3,4
(use "RealLeToRatLe")
(use "RealEqElim0")
(use "a===b")
;; 4
(use "RealLeToRatLe")
(use "RealEqElim1")
(use "a===b")
;; Proof finished.
;; (cdp)
(save "RealEqToRatEqv")

;; RealExpCompat
(set-goal  "all x,y,n(x===y -> x**n===y**n)")
(assume "x" "y" "n" "x=y")
(ind (pt "n"))
;; Base
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; Step
(assume "n1" "IH")
(ng #t)
(use "RealTimesCompat")
(use "IH")
(use "x=y")
;; Proof finished.
;; (cdp)
(save "RealExpCompat")

;; RealExpCompatTwo
(set-goal "all x,y(x===y -> all n,m(n=m -> x**n===y**m))")
(assume "x" "y" "x=y")
(ind)
;; 3,4
(assume "m" "0=m")
(simp "0=m")
(use "RealExpCompat")
(use "x=y")
;; 4
(assume "n" "IH")
(cases)
;; 9,10
(assume "Absurd")
(use "EfRealEq")
(use "Absurd")
(assume "m")
(ng #t)
(assume "n=m")
(use "RealTimesCompat")
(use "IH")
(use "n=m")
(use "x=y")
;; Proof finished.
;; (cp)
(save "RealExpCompatTwo")

;; Properties of RealMax

;; RealMaxUB1
(set-goal "all x1,x2(Real x1 -> Real x2 -> x1<<=x1 max x2)")
(assume "x1" "x2" "Rx1" "Rx2")
(use "RealLeSToLe")
(autoreal)
(use "RealLeSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "x2"))
(assume "bs" "N" "x2Def")
(ng #t)
(use "RatMaxUB1")
;; Proof finished.
;; (cdp)
(save "RealMaxUB1")

;; RealMaxUB2
(set-goal "all x1,x2(Real x1 -> Real x2 -> x2<<=x1 max x2)")
(assume "x1" "x2" "Rx1" "Rx2")
(use "RealLeSToLe")
(autoreal)
(use "RealLeSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "x2"))
(assume "bs" "N" "x2Def")
(ng #t)
(use "RatMaxUB2")
;; Proof finished.
;; (cdp)
(save "RealMaxUB2")

;; RealMaxLUB
(set-goal "all x1,x2,x3(x1<<=x3 -> x2<<=x3 -> x1 max x2<<=x3)")
(assume "x1" "x2" "x3" "x1<=x3" "x2<=x3")
(use "RealLeChar2RealConstrFree")
(autoreal)
(assume "p")
(inst-with-to
 "RealLeChar1RealConstrFree" (pt "x1") (pt "x3") "x1<=x3" (pt "p") "ExInst1")
(by-assume "ExInst1" "n" "nProp")
(inst-with-to
 "RealLeChar1RealConstrFree" (pt "x2") (pt "x3") "x2<=x3" (pt "p") "ExInst2")
(by-assume "ExInst2" "m" "mProp")
(intro 0 (pt "n max m"))
(assume "l" "lBd")
;; ?^18(x1 max x2)seq l<=x3 seq l+(1#2**p)
(assert "x2 seq l<=x3 seq l+(1#2**p)")
(use "mProp")
(use "NatLeTrans" (pt "n max m"))
(use "NatMaxUB2")
(use "lBd")
(assert "x1 seq l<=x3 seq l+(1#2**p)")
(use "nProp")
(use "NatLeTrans" (pt "n max m"))
(use "NatMaxUB1")
(use "lBd")
;; ?^24:x1 seq l<=x3 seq l+(1#2**p) -> 
;;      x2 seq l<=x3 seq l+(1#2**p) -> (x1 max x2)seq l<=x3 seq l+(1#2**p)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "x2"))
(assume "bs" "N" "x2Def")
(cases (pt "x3"))
(assume "cs" "K" "x3Def")
(ng #t)
(use "RatMaxLUB")
;; Proof finished.
;; (cdp)
(save "RealMaxLUB")

;; RealMaxEq1
(set-goal "all x1,x2(x2<<=x1 -> x1 max x2===x1)")
(assume "x1" "x2" "x2<=x1")
(use "RealLeAntiSym")
;; 3,4
(use "RealMaxLUB")
(use "RealLeRefl")
(autoreal)
(use "x2<=x1")
(use "RealMaxUB1")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealMaxEq1")

;; RealMaxEq2
(set-goal "all x1,x2(x1<<=x2 -> x1 max x2===x2)")
(assume "x1" "x2" "x1<=x2")
(use "RealLeAntiSym")
;; 3,4
(use "RealMaxLUB")
(use "x1<=x2")
(use "RealLeRefl")
(autoreal)
(use "RealMaxUB2")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealMaxEq2")

;; RealLeMonMax
(set-goal "all x1,x2,x3,x4(x1<<=x2 -> x3<<=x4 -> x1 max x3<<=x2 max x4)")
(assume "x1" "x2" "x3" "x4" "x1<=x2" "x3<=x4")
(use "RealMaxLUB")
(use "RealLeTrans" (pt "x2"))
(use "x1<=x2")
(use "RealMaxUB1")
(autoreal)
(use "RealLeTrans" (pt "x4"))
(use "x3<=x4")
(use "RealMaxUB2")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeMonMax")

;; RealMaxAssoc
(set-goal "all x1,x2,x3(Real x1 -> Real x2 -> Real x3 ->
 x1 max(x2 max x3)===x1 max x2 max x3)")
(assume "x1" "x2" "x3" "Rx1" "Rx2" "Rx3")
(use "RealLeAntiSym")
;; 3,4
(use "RealMaxLUB")
(use "RealLeTrans" (pt "x1 max x2"))
(use "RealMaxUB1")
(autoreal)
(use "RealMaxUB1")
(autoreal)
;; 6
(use "RealMaxLUB")
(use "RealLeTrans" (pt "x1 max x2"))
(use "RealMaxUB2")
(autoreal)
(use "RealMaxUB1")
(autoreal)
(use "RealMaxUB2")
(autoreal)
;; 4
(use "RealMaxLUB")
(use "RealMaxLUB")
(use "RealMaxUB1")
(autoreal)
(use "RealLeTrans" (pt "x2 max x3"))
(use "RealMaxUB1")
(autoreal)
(use "RealMaxUB2")
(autoreal)
(use "RealLeTrans" (pt "x2 max x3"))
(use "RealMaxUB2")
(autoreal)
(use "RealMaxUB2")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealMaxAssoc")

;; RealMaxCompat
(set-goal "all x1,x2,x3,x4(x1===x2 -> x3===x4 -> x1 max x3===x2 max x4)")
(assume "x1" "x2" "x3" "x4" "x1=x2" "x3=x4")
(use "RealLeAntiSym")
;; 3,4
(use "RealLeMonMax")
(simpreal "x1=x2")
(use "RealLeRefl")
(autoreal)
(simpreal "x3=x4")
(use "RealLeRefl")
(autoreal)
;; 4
(use "RealLeMonMax")
(simpreal "x1=x2")
(use "RealLeRefl")
(autoreal)
(simpreal "x3=x4")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealMaxCompat")

;; Properties of RealMin

;; RealMinLB1
(set-goal "all x1,x2(Real x1 -> Real x2 -> x1 min x2<<=x1)")
(assume "x1" "x2" "Rx1" "Rx2")
(use "RealLeSToLe")
(autoreal)
(use "RealLeSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "x2"))
(assume "bs" "N" "x2Def")
(ng #t)
(use "RatMinLB1")
;; Proof finished.
;; (cdp)
(save "RealMinLB1")
;; RealMinLB2
(set-goal "all x1,x2(Real x1 -> Real x2 -> x1 min x2<<=x2)")
(assume "x1" "x2" "Rx1" "Rx2")
(use "RealLeSToLe")
(autoreal)
(use "RealLeSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "x2"))
(assume "bs" "N" "x2Def")
(ng #t)
(use "RatMinLB2")
;; Proof finished.
;; (cdp)
(save "RealMinLB2")

;; RealMinGLB
(set-goal "all x1,x2,x3(x3<<=x1 -> x3<<=x2 -> x3<<=x1 min x2)")
(assume "x1" "x2" "x3" "x3<=x1" "x3<=x2")
(use "RealLeChar2RealConstrFree")
(autoreal)
(assume "p")
(inst-with-to
 "RealLeChar1RealConstrFree" (pt "x3") (pt "x1") "x3<=x1" (pt "p") "ExInst1")
(by-assume "ExInst1" "n" "nProp")
(inst-with-to
 "RealLeChar1RealConstrFree" (pt "x3") (pt "x2") "x3<=x2" (pt "p") "ExInst2")
(by-assume "ExInst2" "m" "mProp")
(intro 0 (pt "n max m"))
(assume "l" "lBd")
;; ?^18:x3 seq l<=(x1 min x2)seq l+(1#2**p)
(simp "RatPlusComm")
(use "RatLePlusR")
;; ?^20:~(1#2**p)+x3 seq l<=(x1 min x2)seq l

(assert "~(1#2**p)+x3 seq l<=x2 seq l")
(use "RatLePlusRInv")
(simp "RatPlusComm")
(use "mProp")
(use "NatLeTrans" (pt "n max m"))
(use "NatMaxUB2")
(use "lBd")

(assert "~(1#2**p)+x3 seq l<=x1 seq l")
(use "RatLePlusRInv")
(simp "RatPlusComm")
(use "nProp")
(use "NatLeTrans" (pt "n max m"))
(use "NatMaxUB1")
(use "lBd")
;; ?^28:~(1#2**p)+x3 seq l<=x1 seq l -> 
;;      ~(1#2**p)+x3 seq l<=x2 seq l -> ~(1#2**p)+x3 seq l<=(x1 min x2)seq l

(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "x2"))
(assume "bs" "N" "x2Def")
(cases (pt "x3"))
(assume "cs" "K" "x3Def")
(ng #t)
(use "RatMinGLB")
;; Proof finished.
;; (cdp)
(save "RealMinGLB")

;; RealMinEq1
(set-goal "all x,y(x<<=y -> x min y===x)")
(assume "x" "y" "x<=y")
(use "RealLeAntiSym")
(use "RealMinLB1")
(autoreal)
(use "RealMinGLB")
(use "RealLeRefl")
(autoreal)
(use "x<=y")
;; Proof finished.
;; (cdp)
(save "RealMinEq1")

;; RealMinEq2
(set-goal "all x,y(y<<=x -> x min y===y)")
(assume "x" "y" "y<=x")
(use "RealLeAntiSym")
(use "RealMinLB2")
(autoreal)
(use "RealMinGLB")
(use "y<=x")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealMinEq2")

;; RealLeMonMin
(set-goal "all x1,x2,x3,x4(x1<<=x2 -> x3<<=x4 -> x1 min x3<<=x2 min x4)")
(assume "x1" "x2" "x3" "x4" "x1<=x2" "x3<=x4")
(use "RealMinGLB")
(use "RealLeTrans" (pt "x1"))
(use "RealMinLB1")
(autoreal)
(use "x1<=x2")
(use "RealLeTrans" (pt "x3"))
(use "RealMinLB2")
(autoreal)
(use "x3<=x4")
;; Proof finished.
;; (cdp)
(save "RealLeMonMin")

;; RealMinAssoc
(set-goal "all x1,x2,x3(Real x1 -> Real x2 -> Real x3 ->
  x1 min(x2 min x3)===x1 min x2 min x3)")
(assume "x1" "x2" "x3" "Rx1" "Rx2" "Rx3")
(use "RealLeAntiSym")
;; 3,4
(use "RealMinGLB")
(use "RealLeMonMin")
(use "RealLeRefl")
(autoreal)
(use "RealMinLB1")
(autoreal)
(use "RealLeTrans" (pt "x2 min x3"))
(use "RealMinLB2")
(autoreal)
(use "RealMinLB2")
(autoreal)
;; 4
(use "RealMinGLB")
(use "RealLeTrans" (pt "x1 min x2"))
(use "RealMinLB1")
(autoreal)
(use "RealMinLB1")
(autoreal)
(use "RealLeTrans" (pt "x2 min x3"))
(use "RealLeMonMin")
(use "RealMinLB2")
(autoreal)
(use "RealLeRefl")
(autoreal)
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealMinAssoc")

;; RealMinComm
(set-goal "all x1,x2(Real x1 -> Real x2 -> x1 min x2===x2 min x1)")
(assume "x1" "x2" "Rx1" "Rx2")
(use "RealLeAntiSym")
(use "RealMinGLB")
(use "RealMinLB2")
(autoreal)
(use "RealMinLB1")
(autoreal)
(use "RealMinGLB")
(use "RealMinLB2")
(autoreal)
(use "RealMinLB1")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealMinComm")

;; RealMinCompat
(set-goal "all x1,x2,x3,x4(x1===x2 -> x3===x4 -> x1 min x3===x2 min x4)")
(assume "x1" "x2" "x3" "x4" "x1=x2" "x3=x4")
(use "RealLeAntiSym")
;; 3,4
(use "RealLeMonMin")
(simpreal "x1=x2")
(use "RealLeRefl")
(autoreal)
(simpreal "x3=x4")
(use "RealLeRefl")
(autoreal)
;; 4
(use "RealLeMonMin")
(simpreal "x1=x2")
(use "RealLeRefl")
(autoreal)
(simpreal "x3=x4")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealMinCompat")

;; 10.  Further properties
;; =======================

;; RealLeToNNeg
(set-goal "all x,y(x<<=y -> RealNNeg(~x+y))")
(assume "x" "y" "x<=y")
(use "RealZeroLeToNNeg")
(use "RealLePlusLInv")
(autoreal)
(simpreal "RealPlusZero")
(use "x<=y")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeToNNeg")

;; RealNNegToLe
(set-goal "all x,y(Real x -> Real y -> RealNNeg(~x+y) -> x<<=y)")
(assume "x" "y" "Rx" "Ry" "NNegHyp")
(simpreal (pf "x===x+0"))
(use "RealLePlusL")
(autoreal)
(use "RealNNegToZeroLe")
(use "NNegHyp")
(use "RealEqSym")
(use "RealPlusZero")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealNNegToLe")

;; RealLeAbs
(set-goal "all x,y(x<<=y -> ~x<<=y -> abs x<<=y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x<=y" "~x<=y")
(use "RealLeChar2RealConstrFree")
(autoreal)
(assume "p")
(ng #t)
;; ?^10:exnc n all n0(n<=n0 -> abs(as n0)<=bs n0+(1#2**p))
(inst-with-to
"RealLeChar1" (pt "as") (pt "M") (pt "bs") (pt "N") "x<=y" (pt "p") "n1Ex")
(by-assume "n1Ex" "n1" "n1Prop")
(ng "~x<=y")
(inst-with-to
 "RealLeChar1" (pt "[n]~(as n)")
 (pt "M") (pt "bs") (pt "N") "~x<=y" (pt "p") "n2Ex")
(by-assume "n2Ex" "n2" "n2Prop")
(defnc "n" "n1 max n2")
(intro 0 (pt "n"))
(assume "m" "n<=m")
(use "RatLeAbs")
(use "n1Prop")
(use "NatLeTrans" (pt "n"))
(simp "nDef")
(use "NatMaxUB1")
(use "n<=m")
(use "n2Prop")
(use "NatLeTrans" (pt "n"))
(simp "nDef")
(use "NatMaxUB2")
(use "n<=m")
;; Proof finished.
;; (cdp)
(save "RealLeAbs")

;; RealLeIdAbs
(set-goal "all x(Real x -> x<<=abs x)")
(cases)
(assume "as" "M" "Rx")
(use "RealSeqLeToLe" (pt "Zero"))
(use "Rx")
(realproof)
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealLeIdAbs")

;; RealLeAbsInv
(set-goal "all x,y(Real x -> abs x<<=y -> ~y<<=x)")
(assume "x" "y" "Rx" "|x|<=y")
(inst-with-to "RealUMinusUMinus" (pt "x") "RealUMinusUMinusInst")
(simpreal "<-" "RealUMinusUMinusInst")
(drop "RealUMinusUMinusInst")
(use "RealLeUMinus")
(use "RealLeTrans" (pt "abs~ x"))
(use "RealLeIdAbs")
(realproof)
(simpreal "RealAbsUMinus")
(use "|x|<=y")
(use "Rx")
(use "Rx")
;; Proof finished.
;; (cdp)
(save "RealLeAbsInv")

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
;; (cdp)
(save "RealLeAbsPlus")

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
;; (cdp)
(save "RealAbsTimes")

;; RealLeAbsId
(set-goal "all x(0<<=x -> abs x<<=x)")
(assume "x")
(cases (pt "x"))
(assume "as" "M" "xDef" "0<=x")
(use "RealLeChar2RealConstrFree")
(autoreal)
(assume "p")
(ng #t)
;; ?^9:exnc n all n0(n<=n0 -> abs(as n0)<=as n0+(1#2**p))
(inst-with-to
"RealLeChar1RealConstrFree"
(pt "RealConstr([n](0#1))([p]Zero)") (pt "RealConstr as M")
"0<=x" (pt "PosS p") "nEx")
(by-assume "nEx" "n" "nProp")
(intro 0 (pt "n"))
(assume "m" "mBd")
(ng "nProp")
;; ?^17:abs(as m)<=as m+(1#2**p)
(use "RatLeAbs")
(use "Truth")
;; ?^19:~(as m)<=as m+(1#2**p)
(use "RatLeTrans" (pt "~ ~(1#2**PosS p)"))
;; 20,21
(simp "RatLe7RewRule")
;; ?^22:~(1#2**PosS p)<=as m
(simp "<-" "RatZeroLePlusEqUMinusLe")
(use "nProp")
(use "mBd")
;; ?^21:~ ~(1#2**PosS p)<=as m+(1#2**p)
(simprat "<-" (pf "(1#2**PosS p)+(1#2**PosS p)==(1#2**p)"))
;; 25,26
(use "RatLeTrans" (pt "0+(1#2**PosS p)"))
(use "Truth")
(simp "RatPlusAssoc")
(use "RatLeMonPlus")
(use "nProp")
(use "mBd")
(use "Truth")
(use "RatPlusHalfExpPosS")
;; Proof finished.
;; (cdp)
(save "RealLeAbsId")

;; RealEqAbsId
(set-goal "all x(0<<=x -> abs x===x)")
(assume "x" "0<=x")
(use "RealEqIntro")
(use "RealLeAbsId")
(use "0<=x")
(use "RealLeIdAbs")
(realproof)
;; Proof finished.
;; (cdp)
(save "RealEqAbsId")

;; ;; RealAbsAbs
;; (set-goal "all x abs abs x eqd abs x")
;; (cases)
;; (assume "as" "M")
;; (ng)
;; (use "InitEqD")
;; ;; Proof finished.
;; ;; (cdp)
;; (add-rewrite-rule "abs abs x" "abs x")

;; RealAbsZero
(set-goal "all x(Real x -> abs x===0 -> x===0)")
(assume "x" "Rx" "Abs0")
(use "RealLeAntiSym")
;; 3,4
;; x<<=0
(simpreal "<-" "Abs0")
(use "RealLeIdAbs")
(use "Rx")
;; ?^4:0<<=x
(use "RealLeUMinusInv")
(ng #t)
(use "RealLeTrans" (pt "abs ~x"))
(use "RealLeIdAbs")
(realproof)
(simpreal "RealAbsUMinus")
(simpreal "Abs0")
(use "RatLeToRealLe")
(use "Truth")
(realproof)
;; Proof finished.
;; (cdp)
(save "RealAbsZero")

;; RealLeZeroAbs
(set-goal "all x(Real x -> 0<<=abs x)")
(cases)
(assume "as" "M" "Rx")
(use "RealSeqLeToLe" (pt "Zero"))
(autoreal)
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealLeZeroAbs")

;; RealAbsExp
(set-goal "all x,n(Real x -> abs(x**n)===abs x**n)")
(assume "x" "n" "Rx")
(ind (pt "n"))
;; Base
(ng #t)
(use "RealEqRefl")
(use "RealRat")
;; Step
(assume "m" "IH")
(ng #t)
;; ?^8:abs(x**m*x)===abs x**m*abs x
(simpreal "RealAbsTimes")
(simpreal "IH")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealAbsExp")

;; RealAbsMax
(set-goal "all x(Real x -> abs x===x max~x)")
(assume "x" "Rx")
(use "RealLeAntiSym")
;; 3,4
(use "RealLeAbs")
(use "RealMaxUB1")
(autoreal)
(use "RealMaxUB2")
(autoreal)
;; 4
(use "RealMaxLUB")
(use "RealLeIdAbs")
(autoreal)
(simpreal "<-" "RealAbsUMinus")
(use "RealLeIdAbs")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealAbsMax")

;; Properties of RealUDiv

;; RealLeUDivUDiv
(set-goal "all x,y,p,q((1#2**p)<<=x -> (1#2**q)<<=y -> x<<=y ->
 RealUDiv y(PosS q)<<=RealUDiv x(PosS p))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "p" "q" "pHyp" "qHyp" "x<=y")

(assert "Real(RealUDiv(RealConstr as M)(PosS p))")
(use "RealUDivReal")
(realproof)
(use "RealPosToPosAbs")
(use "RealLeToPos")
(use "pHyp")
;; Assertion proved.
(assume "R1/x")

(assert "Real(RealUDiv(RealConstr bs N)(PosS q))")
(use "RealUDivReal")
(realproof)
(use "RealPosToPosAbs")
(use "RealLeToPos")
(use "qHyp")
;; Assertion proved.
(assume "R2/y")

(use "RealLeChar2RealConstrFree")
(autoreal)
(assume "p1")
(ng #t)
;; ?^24:exnc n all n0(n<=n0 -> RatUDiv(bs n0)<=RatUDiv(as n0)+(1#2**p1))

(assert "RealPos(RealConstr as M)(PosS p)")
(use  "RealLeToPos")
(use "pHyp")
(assume "pPosHyp")

(assert "RealPos(RealConstr bs N)(PosS q)")
(use  "RealLeToPos")
(use "qHyp")
(assume "qPosHyp")

(defnc "q1" "p1+PosS(PosS q)+PosS(PosS p)")
(inst-with-to
 "RealLeChar1RealConstrFree"
 (pt "RealConstr as M") (pt "RealConstr bs N") "x<=y" (pt "q1") "ExHyp")
(by-assume "ExHyp" "n1" "n1Prop")
(ng "n1Prop")
(drop "x<=y")

(intro 0 (pt "M(PosS(PosS p)) max N(PosS(PosS q)) max n1"))
(assume "n" "nBd")
;; ?^48:RatUDiv(bs n)<=RatUDiv(as n)+(1#2**p1)

;; Need positivity of as n and bs n
(assert "(1#2**PosS(PosS p))<=as n")
(use "RatLePlusCancelR" (pt "(1#2**PosS(PosS p))"))
(simprat "RatPlusHalfExpPosS")
(use "RatLeTrans" (pt "as(M(PosS(PosS p)))"))
(use "pPosHyp")
(use "RatLePlusR")
(simp "RatPlusComm")
(use "RatLeTrans" (pt "abs(as(M(PosS(PosS p)))+ ~(as n))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(realproof)
(use "Truth")
;; ?^61:M(PosS(PosS p))<=n
(use "NatLeTrans" (pt "M(PosS(PosS p))max N(PosS(PosS q))"))
(use "NatMaxUB1")
(use "NatLeTrans" (pt "M(PosS(PosS p))max N(PosS(PosS q))max n1"))
(use "NatMaxUB1")
(use "nBd")
;; Assertion proved.
(assume "asBd")

(assert "(1#2**PosS(PosS q))<=bs n")
(use "RatLePlusCancelR" (pt "(1#2**PosS(PosS q))"))
(simprat "RatPlusHalfExpPosS")
(use "RatLeTrans" (pt "bs(N(PosS(PosS q)))"))
(use "qPosHyp")
(use "RatLePlusR")
(simp "RatPlusComm")
(use "RatLeTrans" (pt "abs(bs(N(PosS(PosS q)))+ ~(bs n))"))
(use "Truth")
(use "CauchyElim" (pt "N"))
(use "RealConstrToCauchy")
(realproof)
(use "Truth")
;; ?^80:N(PosS(PosS q))<=n
(use "NatLeTrans" (pt "M(PosS(PosS p))max N(PosS(PosS q))"))
(use "NatMaxUB2")
(use "NatLeTrans" (pt "M(PosS(PosS p))max N(PosS(PosS q))max n1"))
(use "NatMaxUB1")
(use "nBd")
;; Assertion proved.
(assume "bsBd")

(assert "0<as n")
(use "RatLtLeTrans" (pt "(1#2**PosS(PosS p))"))
(use "Truth")
(use "asBd")
;; Assertion proved.
(assume "asPos")

(assert "0<bs n")
(use "RatLtLeTrans" (pt "(1#2**PosS(PosS q))"))
(use "Truth")
(use "bsBd")
;; Assertion proved.
(assume "bsPos")

(simprat (pf "RatUDiv(bs n)==as n*RatUDiv(as n)*RatUDiv(bs n)"))
;; 97,98
(simprat (pf "RatUDiv(as n)+(1#2**p1)==
 bs n*RatUDiv(as n)*RatUDiv(bs n)+
 (1#2**p1)*(bs n)*(as n)*RatUDiv(as n)*RatUDiv(bs n)"))
;; 99,100
(simprat "<-" "RatTimesPlusDistrLeft")
(use "RatLeMonTimes")
;; 102,103
;; ?^102:0<=RatUDiv(bs n)
(use "RatLtToLe")
(use "RatPosTimes" (pt "bs n"))
(simprat "RatTimesUDivR")
(use "Truth")
(use "RatLtLeTrans" (pt "bs n"))
(use "bsPos")
(use "Truth")
(use "RatLtToLe")
(use "bsPos")
;; ?^103:as n*RatUDiv(as n)<=
;;       bs n*RatUDiv(as n)+(1#2**p1)*bs n*as n*RatUDiv(as n)
(simprat "<-" "RatTimesPlusDistrLeft")
(use "RatLeMonTimes")
;; ?^113:0<=RatUDiv(as n)
(use "RatLtToLe")
(use "RatPosTimes" (pt "as n"))
(simprat "RatTimesUDivR")
(use "Truth")
(use "RatLtLeTrans" (pt "as n"))
(use "asPos")
(use "Truth")
(use "RatLtToLe")
(use "asPos")
;; ?^114:as n<=bs n+(1#2**p1)*bs n*as n
(use "RatLeTrans" (pt "bs n+(1#2**q1)"))
;; 123,124
(use "n1Prop")
(use "NatLeTrans" (pt "M(PosS(PosS p))max N(PosS(PosS q))max n1"))
(use "NatMaxUB2")
(use "nBd")
;; ?^124:bs n+(1#2**q1)<=bs n+(1#2**p1)*bs n*as1 n
(use "RatLeMonPlus")
(use "Truth")
;; ?^129:(1#2**q1)<=(1#2**p1)*bs n*as n
(simp "q1Def")
;; ?^130:(1#2**(p1+PosS(PosS q)+PosS(PosS p)))<=(1#2**p1)*bs n*as n
(simp "<-" "PosExpTwoPosPlus")
(simp "<-" "PosExpTwoPosPlus")
(simp (pf "(1#2**p1*2**PosS(PosS q)*2**PosS(PosS p))=
           (1#2**p1)*(1#2**PosS(PosS q))*(1#2**PosS(PosS p))"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "Truth")
(use "bsBd")
(use "asBd")
;; ?^134:(1#2**p1*2**PosS(PosS q)*2**PosS(PosS p))=
;;       (1#2**p1)*(1#2**PosS(PosS q))*(1#2**PosS(PosS p))
(use "Truth")
;; ?^100:RatUDiv(as n)+(1#2**p1)==
;;       bs n*RatUDiv(as n)*RatUDiv(bs n)+
;;       (1#2**p1)*bs n*as n*RatUDiv(as n)*RatUDiv(bs n)
(simprat (pf "bs n*RatUDiv(as n)*RatUDiv(bs n)==RatUDiv(as n)"))
;; 143,144
;; ?^143:RatUDiv(as n)+(1#2**p1)==
;;       RatUDiv(as n)+(1#2**p1)*bs n*as n*RatUDiv(as n)*RatUDiv(bs n)
(simprat (pf "(1#2**p1)*bs n*as n*RatUDiv(as n)*RatUDiv(bs n)==(1#2**p1)"))
(use "Truth")
;; ?^146:(1#2**p)*bs n*as n*RatUDiv(as n)*RatUDiv(bs n)==(1#2**p)
(simprat (pf "(1#2**p1)*bs n*as n*RatUDiv(as n)*RatUDiv(bs n)==
              (1#2**p1)*bs n*(as n*RatUDiv(as n))*RatUDiv(bs n)"))
(simprat "RatTimesUDivR")
(ng #t)
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesUDivR")
(use "Truth")
;; ?^154:0<abs(bs n)
(use "RatLtLeTrans" (pt "bs n"))
(use "bsPos")
(use "Truth")
;; ?^150:0<abs(as n)
(use "RatLtLeTrans" (pt "as n"))
(use "asPos")
(use "Truth")
;; ?^148:(1#2**p1)*bs n*as n*RatUDiv(as n)*RatUDiv(bs n)==
;;       (1#2**p1)*bs n*(as n*RatUDiv(as n))*RatUDiv(bs n)
(use "Truth")
;; ?^144:bs n*RatUDiv(as n)*RatUDiv(bs n)==RatUDiv(as n)
(simp (pf "bs n*RatUDiv(as n)=RatUDiv(as n)*bs n"))
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesUDivR")
(use "Truth")
;; ?^163:0<abs(bs n)
(use "RatLtLeTrans" (pt "bs n"))
(use "bsPos")
(use "Truth")
;; ?^160:bs n*RatUDiv(as n)=RatUDiv(as n)*bs n
(use "RatTimesComm")
;; ?^98:RatUDiv(bs n)==as n*RatUDiv(as n)*RatUDiv(bs n)
(simprat "RatTimesUDivR")
(use "Truth")
;; ?^167:0<abs(as n)
(use "RatLtLeTrans" (pt "as n"))
(use "asPos")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealLeUDivUDiv")

;; RealLeUDivUDivInv
(set-goal "all x,y,p,q,p1,q1(Real x -> Real y ->
 (1#2**p)<<=RealUDiv x p1 -> 
 (1#2**q)<<=RealUDiv y q1 ->
 RealUDiv x p1<<=RealUDiv y q1 -> y<<=x)")
(assume "x" "y" "p" "q" "p1" "q1" "Rx" "Ry" "xBd" "yBd" "LH")
(assert "RealUDiv(RealUDiv y q1)(PosS q)<<=
         RealUDiv(RealUDiv x p1)(PosS p)")
(use "RealLeUDivUDiv")
(use "xBd")
(use "yBd")
(use "LH")
(assume "Hyp")

(simpreal "<-" (pf "RealUDiv(RealUDiv x p1)(PosS p)===x"))
(simpreal "<-" (pf "RealUDiv(RealUDiv y q1)(PosS q)===y"))
(use "Hyp")

(use "RealUDivUDiv")
(use "Ry")
(use "RealUDivUDiv")
(use "Rx")
;; Proof finished.
;; (cdp)
(save "RealLeUDivUDivInv")

;; RealLeUDiv
(set-goal "all x,p,y,q(Real x -> RealPos x p -> Real y -> RealPos y q ->
 RealUDiv x p<<=y -> RealUDiv y q<<=x)")
(assume "x" "p" "y" "q" "Rx" "0<x" "Ry" "0<y" "1/x<=y")
(use "RealLeTrans" (pt "x*RealUDiv x p*RealUDiv y q"))
;; 3,4
(simpreal "RealTimesUDivR")
(simpreal "RealOneTimes")
(use "RealLeRefl")
(autoreal)
(use "0<x")
(use "Rx")
;; ?^4:x*RealUDiv x p*RealUDiv y q<<=x
(use "RealLeTrans" (pt "x*y*RealUDiv y q"))
;; 11,12
;; ?^11:x*RealUDiv x p*RealUDiv y q<<=x*y*RealUDiv y q
(use "RealLeMonTimesTwo")
;; ?^13:0<<=x*RealUDiv x p
(simpreal "RealTimesUDivR")
(use "RatLeToRealLe")
(use "Truth")
(use "0<x")
(use "Rx")
(use "RealPosToZeroLeUDiv")
(use "Ry")
(use "0<y")
;; ?^15:x*RealUDiv x p<<=x*y
(use "RealLeMonTimesTwo")
(use "RealPosToZeroLe" (pt "p"))
(use "Rx")
(use "0<x")
(use "RealPosToZeroLeUDiv")
(use "Rx")
(use "0<x")
(use "RealLeRefl")
(use "Rx")
(use "1/x<=y")
(use "RealLeRefl")
(realproof)
;; ?^12:x*y*RealUDiv y q<<=x
(simpreal "<-" "RealTimesAssoc")
(simpreal "RealTimesUDivR")
(simpreal "RealTimesOne")
(use "RealLeRefl")
(autoreal)
(use "0<y")
(autoreal)
;; Proof finished.
(save "RealLeUDiv")

;; RealLeUDivTwoExp
(set-goal "all x,p(RealPos x p -> (1#2**p)<<=x -> RealUDiv x p<<=2**p)")
(assume "x" "p" "0<x" "LeHyp")
(use "RealLeUDiv" (pt "p"))
;; 3-7
(autoreal)
;; ?^4:RealPos(2**p)p
(use "Truth")
;; 5
(autoreal)
;; 6
(use "0<x")
;; ?^7:RealUDiv(2**p)p<<=x
(simpreal (pf "RealUDiv(2**p)p===(1#2**p)"))
(use "LeHyp")
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealLeUDivTwoExp")

;; RealLeUDivTwoExpPosS
(set-goal "all x,p(RealPos x p -> (1#2**PosS p)<<=x ->
  RealUDiv x p<<=2**PosS p)")
(assume "x" "p" "0<x" "LeHyp")
(use "RealLeUDiv" (pt "p"))
;; 3-7
(autoreal)
;; ?^4:RealPos(2**PosS p)p
(use "Truth")
;; 5
(autoreal)
;; 6
(use "0<x")
;; ?^7:RealUDiv(2**PosS p)p<<=x
(simpreal (pf "RealUDiv(2**PosS p)p===(1#2**PosS p)"))
(use "LeHyp")
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealLeUDivTwoExpPosS")

;; End of properties of RealUDiv

;; RealApprox
(set-goal "all x,p(Real x -> exl a abs(a+ ~x)<<=(1#2**p))")
(assume "x" "p" "Rx")
(intro 0 (pt "x seq(x mod p)"))
(use "RealLeIntro")
(autoreal)
(assume "q")
(cases (pt "x"))
(assume "as" "M" "xDef")
(defnc "a" "(1#2**p)seq((1#2**p)mod(PosS q))")
(simp "<-" "aDef")
(ng)
(use "RatLeTrans"
(pt "abs(as(M p)+ ~(as(M(p+PosS(PosS q)))))+
     abs(as(M(p+PosS(PosS q)))+ ~(as(M(PosS(PosS q)))))"))
;; 19,20
(use "RatLeAbsMinus")
;; 20
(use "RatLeMonPlus")
;; 21,22
(simp "aDef")
;; ?^23:abs(as(M p)+ ~(as(M(p+PosS(PosS q)))))<=(1#2**p)
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(simp "<-" "xDef")
(use "Rx")
(use "Truth")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(simp "<-" "xDef")
(use "Rx")
(simp "PosLe4RewRule")
(use "Truth")
;; ?^22:abs(as(M(p+PosS(PosS q)))+ ~(as(M(PosS(PosS q)))))<=(1#2**q)
(use "RatLeTrans" (pt "(1#2**PosS(PosS q))"))
;; 34,35
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(simp "<-" "xDef")
(use "Rx")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(simp "<-" "xDef")
(use "Rx")
(ng #t)
(use "Truth")
(use "Truth")
;; 35
(ng #t)
(use "PosLeMonPosExpPos")
(use "PosLeTrans" (pt "PosS q"))
(use "Truth")
(use "Truth")
;; (cdp)
;; Proof finished.
(save "RealApprox")

;; (add-sound "RealApprox")

;; ok, RealApproxSound has been added as a new theorem:

;; allnc x,p(
;;  Real x -> (ExLTMR (cterm (a) abs(a+ ~x)<<=(1#2**p)))(cRealApprox x p))

;; with computation rule

;; cRealApprox eqd([x,p]x seq(x mod p))

;; (deanimate "RealApprox")

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
;; (cdp)
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
;; (cdp)
(save "RealZeroTimes")

;; RealLeZeroSquare
(set-goal "all x(Real x -> 0<<=x*x)")
(assume "x" "Rx")
(use "RealSeqLeToLe" (pt "Zero"))
(autoreal)
(assume "n" "Useless")
(ng #t)
(cases (pt "x"))
(assume "as" "M" "RasM")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealLeZeroSquare")

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
;; (cdp)
(save "RealEqPlusMinus")
(save "RealEqvPlusMinus")

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
;; (cdp)
(save "RealPlusInsert")

;; ApproxSplitPos
(set-goal "all x,y,z,p(Real x -> Real y -> Real z -> RealPos(y+ ~x)p ->
                       z<<=y oru x<<=z)")

(assert "all as,M(Real(RealConstr as M) -> 
 all p,n,m(M p<=n -> M p<=m -> as n<=as m+(1#2**p)))")
(assume "as" "M" "RasM" "p" "n" "m" "nBd" "mBd")
(use "RatLePlusR")
(simp "RatPlusComm")
(use "RatLeTrans" (pt "abs(as n+ ~(as m))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "RasM")
(use "nBd")
(use "mBd")
;; Assertion proved.
(assume "ApproxSplitAux1")

(assert "all as,M(Real(RealConstr as M) -> 
 all p,n,m(M p<=n -> M p<=m -> as n+ ~(1#2**p)<=as m))")
(assume "as" "M" "RasM" "p" "n" "m" "nBd" "mBd")
(use "RatLeTrans" (pt "as m+(1#2**p)+ ~(1#2**p)"))
(use "RatLeMonPlus")
(use "RatLePlusR")
(simp "RatPlusComm")
(use "RatLeTrans" (pt "abs(as n+ ~(as m))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "RasM")
(use "nBd")
(use "mBd")
(use "Truth")
(simprat "RatEqvPlusMinusRev")
(use "Truth")
;; Assertion proved.
(assume "ApproxSplitAux2")

(assert "all a,b (a+b)*(1#2)+(b+ ~a)*(1#4)==b+ ~((b+ ~a)*(1#4))")
(assume "a" "b")
(use "RatEqvTimesCancelR" (pt "(4#1)"))
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(ng #t)
(simprat "RatTimesPlusDistrLeft")
(ng #t)

(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(ng #t)

(assert "all a a*2==a+a")
(assume "c")
(simp (pf "2=(1#1)+1"))
(simprat "RatTimesPlusDistr")
(use "Truth")
(use "Truth")
;; Auxiliary assertion proved.
(assume "Aux1")

(assert "all a a*4==a*2+a*2")
(assume "c")
(simp (pf "4=(2#1)+2"))
(simprat "RatTimesPlusDistr")
(use "Truth")
(use "Truth")
;; Auxiliary assertion proved.
(assume "Aux2")

(simprat "Aux2")
(simprat "Aux1")
(simp "RatPlusComm")
(ng #t)
(simp "<-" (pf "0+ ~a+a+a+b*2+b= ~a+a+a+b*2+b"))
(simprat "RatEqvPlusMinusPlus")
(ng #t)
(simp (pf "b*2+b*2+ ~b+a=a+(b*2+b*2+ ~b)"))
(ng #t)
(simp (pf "a+b*2+b*2+ ~b=a+b*2+(b*2+ ~b)"))
(use "RatPlusCompat")
(use "Truth")
(simprat "Aux1")
(use "RatEqvSym")
(use "RatEqvPlusMinusRev")
(use "Truth")
(use "RatPlusComm")
(use "Truth")
;; Assertion proved
(assume "ApproxSplitAux3")

(assert "all a,b a+(b+ ~a)*(1#4)==(a+b)*(1#2)+ ~((b+ ~a)*(1#4))")
(assume "a" "b")
(assert "~((b+ ~a)*(1#4))=(a+ ~b)*(1#4)")
(simp "<-" "RatTimes4RewRule")
(ng #t)
(simp "RatPlusComm")
(use "Truth")
;; Auxiliary assertion proved.
(assume "Assertion")

(simp "Assertion")
(simp (pf "(b+ ~a)*(1#4)= ~ ~((b+ ~a)*(1#4))"))
(simp "Assertion")
(simp (pf "a+b=b+a"))
;; ?^13:a+ ~((a+ ~b)*(1#4))==(b+a)*(1#2)+(a+ ~b)*(1#4)
(simprat "ApproxSplitAux3")
(use "Truth")
(use "RatPlusComm")
(use "Truth")
;; Assertion proved.
(assume "ApproxSplitAux4")

;; Now the global proof.
(assume "x" "y" "z" "p" "Rx" "Ry" "Rz")
(cases (pt "x"))
(assume "as" "M" "xDef")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z"))
(assume "cs" "K" "zDef")
(ng #t)
(def "n" "N(PosS(PosS p))max M(PosS(PosS p))")
(simp "<-" "nDef")
(assume "x<y")
(def "m" "n max K(PosS(PosS p))")
(cases (pt "cs m<=(1#2)*(as n+(bs n))"))
;; 26,27
(ng #t)
(assume "Left")
(intro 0)
;; ?^30:RealConstr cs K<<=RealConstr bs N
(use "RealLeChar2")
(simp "<-" "zDef")
(use "Rz")
(simp "<-" "yDef")
(use "Ry")
;; ?^33:all p exnc n all n0(n<=n0 -> cs n0<=bs n0+(1#2**p))
(assume "q")
(intro 0 (pt "m"))
(assume "l" "m<=l")
(use "RatLeTrans" (pt "bs l"))
;; 39,40
(use "RatLeTrans" (pt "cs m+(1#2**(PosS(PosS p)))"))
;; 41,42
;; ?^41:cs l<=cs m+(1#2**PosS(PosS p))
(use "ApproxSplitAux1" (pt "K"))
(simp "<-" "zDef")
(use "Rz")
(use "NatLeTrans" (pt "m"))
(simp "mDef")
(use "NatMaxUB2")
(use "m<=l")
(simp "mDef")
(use "NatMaxUB2")
;; ?^42:cs m+(1#2**PosS(PosS p))<=bs l
(use "RatLeTrans" (pt "(as n+bs n)*(1#2)+(bs n+ ~(as n))*(1#4)"))
(use "RatLeMonPlus")
(simp "RatTimesComm")
(use "Left")
(use "RatLeTrans" (pt "(1#2**p)*(1#4)"))
(ng #t)
;; ?^58:SZero(SZero(2**p))<=2**PosS(PosS p)
(simp "PosSSucc")
(simp "PosSSucc")
(use "Truth")
;; ?^57:(1#2**p)*(1#4)<=(bs n+ ~(as n))*(1#4)
(use "RatLeMonTimes")
(use "Truth")
(use "x<y")
;; ?^52:(as n+bs n)*(1#2)+(bs n+ ~(as n))*(1#4)<=bs l
(simprat "ApproxSplitAux3")
;; ?^63:bs n+ ~((bs n+ ~(as n))*(1#4))<=bs l
(use "RatLeTrans" (pt "bs n+ ~(1#2**PosS(PosS p))"))
(use "RatLeMonPlus")
(use "Truth")
(simp "RatLe7RewRule")
;; ?^68:(1#2**PosS(PosS p))<=(bs n+ ~(as n))*(1#4)
(use "RatLeTrans" (pt "(1#2**p)*(1#4)"))
;; 69,70
;; ?^69:(1#2**PosS(PosS p))<=(1#2**p)*(1#4)
(simp "PosSSucc")
(simp "PosSSucc")
(use "Truth")
;; ?^70:(1#2**p)*(1#4)<=(bs n+ ~(as n))*(1#4)
(use "RatLeMonTimes")
(use "Truth")
(use "x<y")
;; ?^65:bs n+ ~(1#2**PosS(PosS p))<=bs l
(use "ApproxSplitAux2" (pt "N"))
(simp "<-" "yDef")
(use "Ry")
(simp "nDef")
(use "NatMaxUB1")
(use "NatLeTrans" (pt "m"))
(simp "mDef")
(use "NatLeTrans" (pt "n"))
(simp "nDef")
(use "NatMaxUB1")
(use "NatMaxUB1")
(use "m<=l")
(use "Truth")
;; Left case completed
;; 27
(assume "Right")
(intro 1)
;; ?^87:RealConstr as M<<=RealConstr cs K
(use "RealLeChar2")
(simp "<-" "xDef")
(use "Rx")
(simp "<-" "zDef")
(use "Rz")
;; ?^90:all p exnc n all n0(n<=n0 -> as n0<=cs n0+(1#2**p))
(assume "q")
(intro 0 (pt "m"))
(assume "l" "m<=l")
(use "RatLeTrans" (pt "cs l"))
;; 96,97
;; ?^96:as l<=cs l
(use "RatLeTrans" (pt "as n+(1#2**(PosS(PosS p)))"))
;; 98,99
;; ?^98:as l<=as n+(1#2**PosS(PosS p))
(use "ApproxSplitAux1" (pt "M"))
(simp "<-" "xDef")
(use "Rx")
(use "NatLeTrans" (pt "m"))
(simp "mDef")
(use "NatLeTrans" (pt "n"))
(simp "nDef")
(use "NatMaxUB2")
(use "NatMaxUB1")
(use "m<=l")
(simp "nDef")
(use "NatMaxUB2")
;; ?^99:as n+(1#2**PosS(PosS p))<=cs l
(use "RatLeTrans" (pt "as n+(bs n+ ~(as n))*(1#4)"))
;; 111,112
;; ?^111:as n+(1#2**PosS(PosS p))<=as n+(bs n+ ~(as n))*(1#4)
(use "RatLeMonPlus")
(use "Truth")
(use "RatLeTrans" (pt "(1#2**p)*(1#4)"))
(ng #t)
;; ?^117:SZero(SZero(2**p))<=2**PosS(PosS p)
(simp "PosSSucc")
(simp "PosSSucc")
(use "Truth")
;; ?^116:(1#2**p)*(1#4)<=(bs n+ ~(as n))*(1#4)
(use "RatLeMonTimes")
(use "Truth")
(use "x<y")
;; ?^112:as n+(bs n+ ~(as n))*(1#4)<=cs l
(simprat "ApproxSplitAux4")
;; ?^122:(as n+bs n)*(1#2)+ ~((bs n+ ~(as n))*(1#4))<=cs l
(use "RatLeTrans" (pt "cs m+ ~(1#2**PosS(PosS p))"))
;; ?^123:(as n+bs n)*(1#2)+ ~((bs n+ ~(as n))*(1#4))<=cs m+ ~(1#2**PosS(PosS p))
(use "RatLeMonPlus")
;; 125,126
;; ?^125:(as n+bs n)*(1#2)<=cs m
(use "RatLtToLe")
(use "RatNotLeToLt")
(simp "RatTimesComm")
(use "Right")
;; ?^126:~((bs n+ ~(as n))*(1#4))<= ~(1#2**PosS(PosS p))
(simp "RatLe7RewRule")
;; ?^130:(1#2**PosS(PosS p))<=(bs n+ ~(as n))*(1#4) ;same goal as 68
(use "RatLeTrans" (pt "(1#2**p)*(1#4)"))
;; 131,132
;; ?^131:(1#2**PosS(PosS p))<=(1#2**p)*(1#4)
(simp "PosSSucc")
(simp "PosSSucc")
(use "Truth")
;; ?^132:(1#2**p)*(1#4)<=(bs n+ ~(as n))*(1#4)
(use "RatLeMonTimes")
(use "Truth")
(use "x<y")
;; ?^124:cs m+ ~(1#2**PosS(PosS p))<=cs l
(use "ApproxSplitAux2" (pt "K"))
(simp "<-" "zDef")
(use "Rz")
(simp "mDef")
(use "NatMaxUB2")
(use "NatLeTrans" (pt "m"))
(simp "mDef")
(use "NatMaxUB2")
(use "m<=l")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "ApproxSplitPos")

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
;;        as1(M0(PosS(PosS p))max M(PosS(PosS p))max M1(PosS(PosS p)))<=
;;        (1#2)*
;;        (as(M0(PosS(PosS p))max M(PosS(PosS p)))+
;;         as0(M0(PosS(PosS p))max M(PosS(PosS p)))))])])]

;; (add-sound "ApproxSplitPos")

;; ok, ApproxSplitPosSound has been added as a new theorem:

;; allnc x,y,z,p(
;;  Real x -> 
;;  Real y -> 
;;  Real z -> 
;;  RealPos(y+ ~x)p -> 
;;  (OrUMR (cterm () z<<=y) (cterm () x<<=z))(cApproxSplitPos x y z p))

;; with computation rule

;; cApproxSplitPos eqd
;; ([x,x0,x1,p]
;;   [if x
;;     ([as,M]
;;      [if x0
;;        ([as0,M0]
;;         [if x1
;;           ([as1,M1]
;;            as1(M0(PosS(PosS p))max M(PosS(PosS p))max M1(PosS(PosS p)))<=
;;            (1#2)*
;;            (as(M0(PosS(PosS p))max M(PosS(PosS p)))+
;;             as0(M0(PosS(PosS p))max M(PosS(PosS p)))))])])])

;; (deanimate "ApproxSplitPos")

;; Instead of RealPos(y+ ~x)p we can also have RealLt x y p.

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

;; RealNotPosToLe
(set-goal "all x(Real x -> all p(RealPos x p -> F) -> x<<=0)")
(cases)
(assume "as" "M" "Rx" "NotPosHyp")
(ng)
(use "RealLeChar2")
(autoreal)
(assume "p")
(intro 0 (pt "M(PosS(PosS p))"))
(assume "n" "nBd")
(ng #t)
(use "RatLeTrans" (pt "as(M(PosS(PosS p)))+(1#2**PosS(PosS p))"))
(use "CauchyChar1" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "nBd")
(use "Truth")
;; ?^15:as(M(PosS(PosS p)))+(1#2**PosS(PosS p))<=(1#2**p)
(use "RatLeTrans" (pt "(1#2**PosS p)+(1#2**PosS p)"))
(use "RatLeMonPlus")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "NotPosHyp")
(ng #t)
(use "PosLtToLe")
(use "PosLtMonPosExpTwoPos")
(use "Truth")
(simprat "RatPlusHalfExpPosS")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealNotPosToLe")

;; RealNotLtToLe
(set-goal "all x,y(Real x -> Real y -> all p(RealLt y x p -> F) -> x<<=y)")
(assume "x" "y" "Rx" "Ry" "NotLtHyp")
(simpreal (pf "y===y+0"))
(use "RealLePlusR")
(autoreal)
;; ?^7:~y+x<<=0
(simpreal "RealPlusComm")
(use "RealNotPosToLe")
(autoreal)
(assume "p" "PosHyp")
(use "NotLtHyp" (pt "p"))
(use "RealLtIntro")
(use "PosHyp")
(autoreal)
(use "RealEqSym")
(use "RealPlusZero")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealNotLtToLe")

;; RealLtAbs
(set-goal "all x,y,p(RealLt abs x y p -> RealLt x y p)")
(assume "x" "y" "p")
(cases (pt "x"))
(assume "as" "M" "x=(as,M)")
(cases (pt "y"))
(assume "bs" "N" "y=(bs,N)")
(assume "absx<y")
(use "RealLtIntro")
(ng)
(use "RatLeTrans" (pt "bs(N(PosS(PosS p))max M(PosS(PosS p)))+ 
                       ~abs(as(N(PosS(PosS p))max M(PosS(PosS p))))"))
(use "absx<y")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealLtAbs")

;; RealLtAbsRealPosUMinus
(set-goal "all x,y,p(RealLt abs x y p -> RealPos(y+ ~x)p)")
(cases)
(assume "as" "M" )
(cases)
(assume "bs" "N" "p" "absx<y")
(ng)
(use "RatLeTrans" (pt "bs(N(PosS(PosS p))max M(PosS(PosS p)))+ 
                       ~abs(as(N(PosS(PosS p))max M(PosS(PosS p))))"))
(use "absx<y")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealLtAbsRealPosUMinus")

;; ApproxSplit
(set-goal "all x,y,z,p(Real x -> Real y -> Real z -> RealLt x y p ->
                       z<<=y oru x<<=z)")
(assume "x" "y" "z" "p" "Rx" "Ry" "Rz" "x<y")
(use "ApproxSplitPos" (pt "p"))
(autoreal)
(use "RealLtElim")
(use "x<y")
;; Proof finished.
;; (cdp)
(save "ApproxSplit")

;; (add-sound "ApproxSplit")

;; ok, ApproxSplitSound has been added as a new theorem:

;; allnc x,y,z,p(
;;  Real x -> 
;;  Real y -> 
;;  Real z -> 
;;  RealLt x y p -> 
;;  (OrUMR (cterm () z<<=y) (cterm () x<<=z))(cApproxSplit x y z p))

;; with computation rule

;; cApproxSplit eqd cApproxSplitPos

;; We do not deanimate ApproxSplit since the extracted term is short.

(animate "ApproxSplit")

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
;; Assertion proved.
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
;; (cdp)
(save "RealAllncTotalIntro")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
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
;; (cdp)
(save "RealAllncTotalElim")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [alpha3697]alpha3697

;; RealLePlusCancelL
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x+y<<=x+z -> y<<=z)")
(assume "x" "y" "z")
(cases (pt "x"))
(assume "as" "M" "xDef")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z"))
(assume "cs" "K" "zDef" "Rx" "Ry" "Rz" "x+y<<=x+z")
(use "RealLeChar2")
(autoreal)
(ng "x+y<<=x+z")

(assert
 "all p exnc n allnc n0(n<=n0 -> ([n]as n+bs n)n0<=([n]as n+cs n)n0+(1#2**p))")
(use "RealLeChar1" (pt "([p]M(PosS p)max N(PosS p))")
     (pt "([p]M(PosS p)max K(PosS p))"))
(use "x+y<<=x+z")
(ng #t)
;; ?^16:all p exnc n allnc n0(n<=n0 -> as n0+bs n0<=as n0+cs n0+(1#2**p)) -> 
;;      all p exnc n all n0(n<=n0 -> bs n0<=cs n0+(1#2**p))

(assume "AllExHyp" "p")
(inst-with-to "AllExHyp" (pt "p") "nEx")
(by-assume "nEx" "n" "nProp")
(intro 0 (pt "n"))
(assume "m" "n<=m")
(inst-with-to "nProp" (pt "m") "n<=m" "mProp")
(use "RatLePlusCancelL" (pt "as m"))
(use "mProp")
;; Proof finished.
;; (cdp)
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
;; (cdp)
(save "RealLePlusCancelR")

;; RealLePlusUMinusR
(set-goal "all x,y,z(Real y -> Real z -> x<<=y+ ~z -> z<<=y+ ~x)")
(assume "x" "y" "z" "Ry" "Rz" "x<=y-z")
(use "RealLePlusCancelR" (pt "x"))
(autoreal)
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "~x+x===x+ ~x"))
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusZero")
(simpreal "RealPlusComm")
(use "RealLePlusCancelR" (pt "~z"))
(autoreal)
(simpreal "<-" "RealPlusAssoc")
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusZero")
(use "x<=y-z")
(autoreal)
;; 12
(use "RealPlusComm")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealLePlusUMinusR")

;; RealLtToLe
(set-goal "all x,y,p(Real x -> Real y -> RealLt x y p -> x+(1#2**PosS p)<<=y)")
(assume "x" "y" "p" "Rx" "Ry" "x<y")
(use "RealLePlusCancelL" (pt "~x"))
(autoreal)
(use "RealLeCompat" (pt "RealConstr([n]1#2**(PosS p))([p] Zero)") (pt "y + ~x"))
;; 7-9
(simpreal "RealPlusAssoc")
(simpreal (pf "~x+x===x+ ~x"))
(simpreal "RealPlusMinusZero")
(simpreal "RealZeroPlus")
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; 8
(use "RealPlusComm")
(autoreal)
;; 9
(use "RealPosToLe")
(autoreal)
(use "RealLtElim")
(use "x<y")
;; Proof finished.
;; (cp)
(save "RealLtToLe")

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
;; (cdp)
(save "RealEqPlusCancelL")
(save "RealEqvPlusCancelL")

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
;; (cdp)
(save "RealEqPlusCancelR")
(save "RealEqvPlusCancelR")

;; RealLeTimesCancelL
(set-goal "all x,y,z,p(Real x -> Real y -> Real z -> RealPos x p ->
 x*y<<=x*z -> y<<=z)")
(assume "x" "y" "z" "p" "Rx" "Ry" "Rz" "PosHyp" "x*y<<=x*z")
(use "RealLeTrans" (pt "y+0"))
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(use "RealLePlusL")
(autoreal)
;; ?^10:0<<= ~y+z
(use "RealLeTrans" (pt "RealUDiv x p*(x*(~y+z))"))
;; 11,12
(use "RealZeroLeToZeroLeTimes")
;; 13,14
;; ?^13:0<<=RealUDiv x p
(use "RealPosToZeroLeUDiv")
(use "Rx")
(use "PosHyp")
;; ?^14:0<<=x*(~y+z)
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesIdUMinus")
(use "RealLePlusLInv")
(autoreal)
(simpreal "RealPlusZero")
(use "x*y<<=x*z")
(autoreal)
;; ?^12:RealUDiv x p*(x*(~y+z))<<= ~y+z
(simpreal "RealTimesAssoc")
(simpreal "<-" (pf "x*RealUDiv x p===(RealUDiv x p)*x"))
(simpreal "RealTimesUDivR")
(simpreal "RealOneTimes")
(use "RealLeRefl")
(autoreal)
(use "PosHyp")
(autoreal)
(use "RealTimesComm")
(autoreal)
;; Proof finished.
;; (cdp)
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
;; (cdp)
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
;; (cdp)
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
;; (cdp)
(save "RealEqTimesCancelR")

;; RealLeAllPlusToLe
(set-goal "all x,y(Real x -> Real y -> all p x<<=y+(1#2**p) -> x<<=y)")
(assert
 "all x,y(Real x -> Real y -> all p x+0<<=y+(1#2**p) -> x+0<<=y+0)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "Rx" "Ry" "AllLe")
(ng #t)
(use "RealLeIntro")
(ng "AllLe")
(realproof)
(simp (pf "(RealConstr bs([p]N(PosS p)))eqd(RealConstr bs N)+0"))
(realproof)
(use "InitEqD")
;; 9
(assume "p")
(ng #t)
;; ?^14:as(M(PosS(PosS p)))<=bs(N(PosS(PosS p)))+(1#2**p)
(use "RatLeAllPlusToLe")
(assume "q")
;; ?^16:as(M(PosS(PosS p)))<=bs(N(PosS(PosS p)))+(1#2**p)+(1#2**q)
(inst-with-to "AllLe" (pt "q") "AllLeInst")
(inst-with-to
"RealLeElim2"
(pt "RealConstr as M +0")
(pt "RealConstr bs N +(1#2**q)")
"RealLeInst")
(ng "RealLeInst")
(simp "<-" "RatPlusAssoc")
(simp (pf "(1#2**p)+(1#2**q) = (1#2**q)+(1#2**p)"))
(simp "RatPlusAssoc")
;; (use "RatLeTrans" (pt "as(M(PosS(PosS p)))+(1#2**q)"))
;; (use "Truth")
(use "RealLeInst")
(use "AllLeInst")
(use "RatPlusComm")
;; Assertion proved.
(assume "RealLeAllPlusToLeAux" "x" "y" "Rx" "Ry" "AllHyp")
(simpreal (pf "x===x+0"))
(simpreal (pf "y===y+0"))
(use "RealLeAllPlusToLeAux")
(autoreal)
(assume "p")
(simpreal "RealPlusZero")
(use "AllHyp")
(use "Rx")
(use "RealEqSym")
(use "RealPlusZero")
(use "Ry")
(use "RealEqSym")
(use "RealPlusZero")
(use "Rx")
;; Proof finished.
;; (cdp)
(save "RealLeAllPlusToLe")

;; RealLeAllAbsToEq ;was RealEqIntro1
(set-goal "all x,y(Real x -> Real y -> all p abs(x+ ~y)<<=(1#2**p) -> x===y)")
(assume "x" "y" "Rx" "Ry" "AllAbsLe")
(use "RealLeAntiSym")
;; 3,4
;; ?^3:x<<=y
(use "RealLeAllPlusToLe")
(autoreal)
(assume "p")
(use "RealLePlusR")
(autoreal)
(simpreal "RealPlusComm")
(use "RealLeTrans" (pt "abs(x+ ~y)"))
(use "RealLeIdAbs")
(autoreal)
(use "AllAbsLe")
(autoreal)
;; ?^4:y<<=x
(use "RealLeAllPlusToLe")
(autoreal)
(assume "p")
;; ?^21:y<<=x+(1#2**p)
(simpreal "RealPlusComm")
(use "RealLePlusR")
(autoreal)
(simpreal "RealPlusComm")
(use "RealLePlusL")
(autoreal)
(simpreal "RealPlusComm")
(use "RealLeAbsInv")
(realproof)
(use "AllAbsLe")
(autoreal)
;; Proof finishewd.
;; (cdp)
(save "RealLeAllAbsToEq")

;; RealPlusHalfExpPosS
(set-goal "all p RealPlus(1#2**PosS p)(1#2**PosS p)===(1#2**p)")
(assume "p")
(simpreal "<-" "RatPlusRealPlus")
(use "RatEqvToRealEq")
(use "RatPlusHalfExpPosS")
;; Proof finished.
;; (cdp)
(save "RealPlusHalfExpPosS")

;; RealPosPlus
(set-goal "all x,y,p(
 0<<=x -> Real y -> RealPos y p -> RealPos(x+y)(PosS(PosS p)))")
(assume "x" "y" "p")
(cases (pt "x"))
(assume "as" "M" "xDef")
(cases (pt "y"))
 (assume "bs" "N" "yDef" "0<=x" "Ry" "0<y")
(ng #t)
(defnc "n" "M(PosS(PosS(PosS(PosS p))))max N(PosS(PosS(PosS(PosS p))))")
(simp "<-" "nDef")
;; ?^15:(1#2**PosS(PosS p))<=as n+bs n
(use "RatLePlusR")
;; ?^16:~(as n)+(1#2**PosS(PosS p))<=bs n
(use "RatLeTrans" (pt "(1#2**PosS(PosS p))+(1#2**PosS(PosS p))"))
;; 17,18
(use "RatLeMonPlus")
;; ?^19:~(as n)<=(1#2**PosS(PosS p))
(simprat (pf "~(as n)== ~(as n)+0"))
(use "RatLePlusRInv")
;; ?^23:0<=as n+(1#2**PosS(PosS p))
(simprat "<-" "RatPlusHalfExpPosS")
(simp "RatPlusAssoc")
(use "RatLeTrans"
(pt "as(M(PosS(PosS(PosS(PosS p)))))+(1#2**PosS(PosS(PosS p)))"))
;; 26,27
(inst-with-to "RealConstrLeElim2"
(pt "[n](0#1)") (pt "[p]Zero") (pt "as") (pt "M") "0<=x" "Inst")
(ng "Inst")
(use "Inst")
(use "RatLeMonPlus")
(use "CauchyChar1" (pt "M"))
(use "RealConstrToCauchy")
(realproof)
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(realproof)
(use "Truth")
(simp "nDef")
(use "NatLeTrans" (pt "M(PosS(PosS(PosS(PosS p))))"))
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(realproof)
(use "Truth")
(use "NatMaxUB1")
(use "Truth")
(use "Truth")
(use "Truth")
;; ?^18:(1#2**PosS(PosS p))+(1#2**PosS(PosS p))<=bs n
(simprat "RatPlusHalfExpPosS")
(use "RealPosChar1" (pt "N"))
(use "Ry")
(use "0<y")
(simp "nDef")
(use "NatLeTrans" (pt "N(PosS(PosS(PosS(PosS p))))"))
(use "MonElim")
(use "RealConstrToMon" (pt "bs"))
(use "Ry")
(ng #t)
(use "PosLeTrans" (pt "PosS(PosS p)"))
(use "PosLeTrans" (pt "PosS p"))
(use "Truth")
(use "Truth")
(use "Truth")
(use "NatMaxUB2")
;; Proof finished.
;; (cdp)
(save "RealPosPlus")

;; Inserted 2021-02-04

;; RealLeAbsMinus1
(set-goal "all x,y,z(Real x -> Real y -> abs(x+ ~y)<<=z -> x<<=y+z)")
(assume "x" "y" "z" "Rx" "Ry" "LeHyp")
(use "RealLePlusR")
(autoreal)
(simpreal "RealPlusComm")
(use "RealLeTrans" (pt "abs(x+ ~y)"))
(use "RealLeIdAbs")
(autoreal)
(use "LeHyp")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeAbsMinus1")

;; RealAbsPlusUMinus
(set-goal "all x,y(Real x -> Real y -> abs(x+ ~y)===abs(y+ ~x))")
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

;; RealLeAbsMinus2
(set-goal "all x,y,z(Real x -> Real y -> abs(x+ ~y)<<=z -> y<<=x+z)")
(assume "x" "y" "z" "Rx" "Ry" "LeHyp")
(use "RealLePlusR")
(autoreal)
(use "RealLeTrans" (pt "abs(~x+y)"))
(use "RealLeIdAbs")
(autoreal)
(simpreal "RealPlusComm")
(simpreal "RealAbsPlusUMinus")
(use "LeHyp")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeAbsMinus2")

;; RealLeAbsMinus
(set-goal "all x,y,z (Real x -> Real y -> Real z ->
 abs(x+ ~y) <<= abs(x+ ~z)+abs(z+ ~y))")
(assume "x" "y" "z" "x_r" "y_r" "z_r")
(simpreal (pf "x+ ~y ===(x+ ~z)+(z+ ~y)"))
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

;; RealLeMinusAbs
(set-goal "all x,y(Real x -> Real y -> abs x+ ~abs y<<=abs(x+ ~y))")
(assume "x" "y" "Rx" "Ry")
(use "RealLeCompat" (pt "abs(x+ ~y+y)+ ~abs y") (pt "abs(x+ ~y)"))
;; 3-5
;; ?^3:abs(x+ ~y+y)+ ~abs y===abs x+ ~abs y
(use "RealPlusCompat")
(use "RealAbsCompat")
(use "RealEqTrans" (pt "x+(~y+y)"))
(use "RealEqSym")
(use "RealPlusAssoc")
(autoreal)
;; ?^10:x+(~y+y)===x
(use "RealEqTrans" (pt "x+0"))
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealEqTrans" (pt "y+ ~y"))
(use "RealPlusComm")
(autoreal)
(use "RealPlusMinusZero")
(realproof)
(use "RealPlusZero")
(realproof)
(use "RealEqRefl")
(realproof)
;; ?^4:abs(x+ ~y)===abs(x+ ~y)
(use "RealEqRefl")
(realproof)
;; ?^5:abs(x+ ~y+y)+ ~abs y<<=abs(x+ ~y)
(use "RealLeTrans" (pt "abs (x+ ~y)+abs y+ ~(abs y)"))
(use "RealLeMonPlusTwo")
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeRefl")
(autoreal)
(use "RealLeCompat" (pt "abs (x+ ~y)") (pt "abs (x+ ~y)"))
(use "RealEqSym")
(use "RealEqTrans" (pt "abs (x+ ~y)+(abs y+ ~(abs y))"))
(use "RealEqSym")
(use "RealPlusAssoc")
(autoreal)
(use "RealEqTrans" (pt "abs (x+ ~y)+0"))
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealPlusMinusZero")
(autoreal)
(use "RealPlusZero")
(autoreal)
(use "RealEqRefl")
(autoreal)
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeMinusAbs")

;; RealLeAbsMinusAbs
(set-goal "all x,y(Real x -> Real y -> abs(abs x+ ~abs y)<<=abs(x+ ~y))")
(assume "x" "y" "Rx" "Ry")
(use "RealLeAbs")
(use "RealLeMinusAbs")
(autoreal)
;; ?^4:~(abs x+ ~abs y)<<=abs(x+ ~y)
(use "RealLeCompat" (pt "abs y+ ~abs x") (pt "abs(y+ ~x)"))
;; 7-9
;; ?^7:abs y+ ~abs x=== ~(abs x+ ~abs y)
(use "RealEqSym")
(use "RealEqTrans" (pt "~abs x+ ~(~(abs y))"))
(use "RealUMinusPlus")
(autoreal)
(use "RealEqTrans" (pt "~(~(abs y))+ ~(abs x)"))
(use "RealPlusComm")
(autoreal)
(use "RealPlusCompat")
(use "RealUMinusUMinus")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; ?^8:abs(y+ ~x)===abs(x+ ~y)
(use "RealAbsPlusUMinus")
(autoreal)
;; ?^9:abs y+ ~abs x<<=abs(y+ ~x)
(use "RealLeMinusAbs")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeAbsMinusAbs")

;; RealLeTransRat
(set-goal "all a,x,b(a<<=x -> x<<=b -> a<=b)")
(assume "a" "x" "b" "a<=x" "x<=b")
(use "RealLeToRatLe")
(use "RealLeTrans" (pt "x"))
(use "a<=x")
(use "x<=b")
;; Proof finished.
;; (cdp)
(save "RealLeTransRat")

;; RealLeBound
(set-goal "all x(Real x -> x<<=2**(cRBd(x seq)(x mod)))")
(cases)
(assume "as" "M" "Rx")
(simp "RealSeq0CompRule")
(simp "RealMod0CompRule")
;; ?^5:RealConstr as M<<=2**RealBd as M
(use "RealLeSToLe")
(use "Rx")
(use "RealRat")
(use "RealLeSIntro")
(simp "RealSeq0CompRule")
(assume "n")
(use "RatLeTrans" (pt "abs(as n)"))
(use "Truth")
(use "RealBdProp")
(use "RealConstrToCauchy")
(use "Rx")
;; Proof finished.
;; (cdp)
(save "RealLeBound")

;; From semws18/completeness.scm (by Max Zeuner)

;; RatCauchyConvMod
(set-goal "all as,M,p,n(Real(RealConstr as M) -> M p<=n ->
                        abs(as n+ ~(RealConstr as M))<<=(1#2**p))")
(assume "as" "M" "p" "n" "Rx" "nBd")
(use "RealLeChar2RealConstrFree")
(autoreal)
(ng #t)
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

;; RatCauchyConvModRealConstrFree
(set-goal
 "allnc x,p,n(Real x -> x mod p<=n -> abs(x seq n+ ~x)<<=(1#2**p))")
(cases)
(assume "as" "M" "p" "n" "Rx" "nBd")
(use "RatCauchyConvMod")
(use "Rx")
(use "nBd")
;; Proof finished.
;; (cdp)
(save "RatCauchyConvModRealConstrFree")

;; From Jan Belle's exp.scm:

;; RealLeExpBernoulli
(set-goal "all x,n(~1<<=x -> 1+n*x<<=(1+x)**n)")
(assume "x" "n" "-1<=x")
(ind (pt "n"))
;; Base
(ng #t)
(simpreal "RealZeroTimes")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; Step
(assume "m" "IH")
(simp "RealExp1CompRule")
(simpreal "<-" (pf "(1+x)*(1+x)**m===(1+x)**m*(1+x)"))
;; 11,12
;; ?^11:1+Succ m*x<<=(1+x)*(1+x)**m
(use "RealLeTrans" (pt "(1+m*x)*(1+x)"))
;; 13,14
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "RealTimesPlusDistrLeft")
(simpreal (pf "RealTimes 1 1+m*x*1+(1*x+m*x*x)===1+m*x+x+m*x*x"))
;; ?^27:1+Succ m*x<<=1+m*x+x+m*x*x
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealLeMonPlusTwo")
(use "RatLeToRealLe")
(use "Truth")
;; ?^38:Succ m*x<<=m*x+(x+m*x*x)
(simpreal "RealPlusAssoc")
(ng #t)
(simpreal (pf "(IntS m#1)===RealPlus m 1"))
(simpreal "RealTimesPlusDistrLeft")
(simpreal "RealOneTimes")
;; ?^51:m*x+x<<=m*x+x+m*x*x
(use "RealLeTrans" (pt "m*x+x+0"))
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(use "RealLeMonPlusTwo")
(use "RealLeRefl")
(autoreal)
;; ?^59:0<<=m*x*x
(simpreal "<-" "RealTimesAssoc")
(use "RealLeTrans" (pt "RealTimes 0 0"))
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonTimesTwo")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
;; ?^71:0<<=x*x
(use "RealLeZeroSquare")
(autoreal)
;; ?^46:IntS m===RealPlus m 1
(use "RatEqvToRealEq")
(ng #t)
;; ((IntS (NatToInt m)) = ((NatToInt m) IntPlus (IntPos 1)))
(simp (pf "IntPos 1=NatToInt(Succ Zero)"))
(simp "NatToIntPlus")
(use "Truth")
(use "Truth")
(autoreal)
;; ?^28:RealTimes 1 1+m*x*1+(1*x+m*x*x)===1+m*x+x+m*x*x
(simpreal "RealOneTimes")
(simpreal "RealOneTimes")
(simpreal "RealTimesOne")
(simpreal "RealPlusAssoc")
(use "RealEqRefl")
(autoreal)
;; ?^14:(1+m*x)*(1+x)<<=(1+x)*(1+x)**m
(simpreal "RealTimesComm")
(use "RealLeMonTimesR")
;; ?^95:0<<=1+x
(use "RealLePlusR")
(autoreal)
(simpreal "RealPlusZero")
(use "-1<=x")
(autoreal)
(use "IH")
(autoreal)
;; ?^12:(1+x)*(1+x)**m===(1+x)**m*(1+x)
(use "RealTimesComm")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLeExpBernoulli")

;; Added 2020-08-28

;; RealLtIrrefl
(set-goal "all x,p(Real x -> RealLt x x p -> F)")
(assume "x" "p" "Rx" "x<x")
(use-with
 "RealPosSemiCompat"
 (pt "x+ ~x")
 (pt "RealConstr([n](IntZero#1))([p]Zero)")
 (pt "p") "?" "?")
(use "RealPlusMinusZero")
(use "Rx")
(use "RealLtElim")
(use "x<x")
;; Proof finished.
;; (cdp)
(save "RealLtIrrefl")

;; RealLtLeTrans
(set-goal "all x,y,z,p(Real x ->
 RealLt x y p -> y<<=z -> RealLt x z(PosS(PosS(PosS(PosS p)))))")
(assume "x" "y" "z" "p" "Rx" "x<y" "y<=z")
(use "RealLtIntro")
(use "RealPosSemiCompat" (pt "z+ ~y+(y+ ~x)"))
;; ?^4:z+ ~y+(y+ ~x)===z+ ~x
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusAssoc")
(simpreal "RealPlusComm")
(simpreal "RealPlusAssoc")
(simpreal "RealEqPlusMinus")
(use "RealEqRefl")
(autoreal)
;; ?^5:RealPos(z+ ~y+(y+ ~x))(PosS(PosS p))
(use "RealPosPlus")
(simpreal "RealPlusComm")
(use "RealLePlusLInv")
(autoreal)
(simpreal "RealPlusZero")
(use "y<=z")
(autoreal)
(use "RealLtElim")
(use "x<y")
;; Proof finished.
;; (cdp)
(save "RealLtLeTrans")

;; RealLeLtTrans
(set-goal "all x,y,z,p(Real z ->
 x<<=y -> RealLt y z p -> RealLt x z(PosS(PosS(PosS(PosS p)))))")
(assume "x" "y" "z" "p" "Rz" "x<=y" "y<z")
(use "RealLtIntro")
(use "RealPosSemiCompat" (pt "y+ ~x+(z+ ~y)"))
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
;; ?^5:RealPos(y+ ~x+(z+ ~y))(PosS(PosS p))
(use "RealPosPlus")
(simpreal "RealPlusComm")
(use "RealLePlusLInv")
(autoreal)
(simpreal "RealPlusZero")
(use "x<=y")
(autoreal)
(use "RealLtElim")
(use "y<z")
;; Proof finished.
;; (cdp)
(save "RealLeLtTrans")

;; RealLeToNotLt
(set-goal "all x,y,p(x<<=y -> RealLt y x p -> F)")
(assume "x" "y" "p" "x<=y" "Ltyxp")
(use "RealLtIrrefl" (pt "x") (pt "PosS(PosS(PosS(PosS p)))"))
(autoreal)
(use "RealLeLtTrans" (pt "y"))
(autoreal)
(use "x<=y")
(use "Ltyxp")
;; Proof finished.
;; (cdp)
(save "RealLeToNotLt")

;; RatLtToRealLt
(set-goal "all a,b(a<b -> exl p RealLt a b p)")
(assume "a" "b" "a<b")
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

;; Code discarded 2022-10-07.
;; ;; 11.  Convergence
;; ;; ================

;; ;; We study convergence of a sequence xs of real numbers to a real
;; ;; number x with modulus M.  It will be convenient to introduce the
;; ;; notation RealConv xs x M to express this fact.

;; (add-var-name "xs" "ys" (py "nat=>rea"))

;; (add-ids
;;  (list (list "RealConv"
;; 	     (make-arity (py "nat=>rea") (py "rea") (py "pos=>nat"))))
;;  '("all xs,x,M(all n Real(xs n) -> Real x -> Mon M ->
;;                all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) ->
;;                RealConv xs x M)" "RealConvIntro"))

;; ;; RealConvElim1
;; (set-goal "all xs,x,M(RealConv xs x M -> all n Real(xs n))")
;; (assume "xs" "x" "M")
;; (elim)
;; (search)
;; ;; Proof finished.
;; ;; (cdp)
;; (save "RealConvElim1")

;; ;; RealConvElim2
;; (set-goal "all xs,x,M(RealConv xs x M -> Real x)")
;; (assume "xs" "x" "M")
;; (elim)
;; (search)
;; ;; Proof finished.
;; ;; (cdp)
;; (save "RealConvElim2")

;; ;; RealConvElim3
;; (set-goal "all xs,x,M(RealConv xs x M -> Mon M)")
;; (assume "xs" "x" "M")
;; (elim)
;; (search)
;; ;; Proof finished.
;; ;; (cdp)
;; (save "RealConvElim3")

;; ;; RealConvElim4
;; (set-goal "all xs,x,M(RealConv xs x M -> all p,n(M p<=n ->
;;  abs(xs n+ ~x)<<=(1#2**p)))")
;; (assume "xs" "x" "M")
;; (elim)
;; (search)
;; ;; Proof finished.
;; ;; (cdp)
;; (save "RealConvElim4")

;; ;; We prove further properties of RealConv.

;; ;; RealConvLe
;; (set-goal "all x,y,xs,ys,M,N(
;;  all n xs n<<=ys n -> RealConv xs x M -> RealConv ys y N -> x<<=y)")
;; (assume "x" "y" "xs" "ys" "M" "N" "LeHyp" "xsConv" "ysConv")
;; (use "RealLeAllPlusToLe")
;; (autoreal)
;; ;; ?^5:all p x<<=y+(1#2**p)
;; (assume "p")
;; ;; Idea: for n := M(PosS p)max N(PosS p) we have x<<=
;; ;; xs n+(1#2**PosS p)<<=
;; ;; ys n+(1#2**PosS p)<<=
;; ;; y+(1#2**PosS p)+(1#2**PosS p)<<=
;; ;; y+(1#2**p)

;; (defnc "n" "M(PosS p)max N(PosS p)")
;; (use "RealLeTrans" (pt "xs n+(1#2**PosS p)"))
;; ;; ?^14:x<<=xs n+(1#2**PosS p)
;; (use "RealLeAbsMinus2")
;; (autoreal)
;; (use "RealConvElim4" (pt "M"))
;; (use "xsConv")
;; (simp "nDef")
;; (use "NatMaxUB1")
;; ;; ?^15:xs n+(1#2**PosS p)<<=y+(1#2**p)
;; (use "RealLeTrans" (pt "ys n+(1#2**PosS p)"))
;; (use "RealLeMonPlus")
;; (autoreal)
;; (use "LeHyp")
;; ;; ?^23:ys n+(1#2**PosS p)<<=y+(1#2**p)
;; (use "RealLeTrans" (pt "y+(1#2**PosS p)+(1#2**PosS p)"))
;; (use "RealLeMonPlus")
;; (autoreal)
;; ;; ?^29:ys n<<=y+(1#2**PosS p)
;; (use "RealLeAbsMinus1")
;; (autoreal)
;; (use "RealConvElim4" (pt "N"))
;; (use "ysConv")
;; (simp "nDef")
;; (use "NatMaxUB2")
;; ;; ?^27:y+(1#2**PosS p)+(1#2**PosS p)<<=y+(1#2**p)
;; (simpreal "<-" "RealPlusAssoc")
;; (use "RealLeMonPlusR")
;; (autoreal)
;; (use "RatLeToRealLe")
;; (simprat
;;  (pf "(2**PosS p+2**PosS p#2**PosS p*2**PosS p)==(1#2**PosS p)+(1#2**PosS p)"))
;; (simprat "RatPlusHalfExpPosS")
;; (use "Truth")
;; (use "Truth")
;; (autoreal)
;; ;; Proof finished.
;; ;; (cdp)
;; (save "RealConvLe")

;; ;; RealConvEq
;; (set-goal "all x,y,xs,ys,M,N(
;;  all n xs n===ys n -> RealConv xs x M -> RealConv ys y N -> x===y)")
;; (assume "x" "y" "xs" "ys" "M" "N" "EqHyp" "xsConv" "ysConv")
;; (use "RealLeAntiSym")
;; ;; 3,4
;; (use "RealConvLe" (pt "xs") (pt "ys") (pt "M") (pt "N"))
;; (assume "n")
;; (use "RealEqElim0")
;; (use "EqHyp")
;; (use "xsConv")
;; (use "ysConv")
;; ;; 4
;; (use "RealConvLe" (pt "ys") (pt "xs") (pt "N") (pt "M"))
;; (assume "n")
;; (use "RealEqElim1")
;; (use "EqHyp")
;; (use "ysConv")
;; (use "xsConv")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "RealConvEq")

;; RealHalfPlus
(set-goal "allnc x(Real x -> x===(1#2)*(x+x))")
(assume "x" "Rx")
(simpreal (pf "x+x===2*x"))
(simpreal "RealTimesAssoc")
(ng #t)
(use "RealEqSym")
(use "RealOneTimes")
(autoreal)
(simpreal (pf "x+x===1*x+1*x"))
(simpreal "<-" "RealTimesPlusDistrLeft")
(use "RealEqRefl")
(autoreal)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealHalfPlus")

;; RealAbsAvBd
(set-goal "allnc x,y,z(Real x -> Real y -> abs x<<=z -> abs y<<=z ->
 abs((1#2)*(x+y))<<=z)")
(assume "x" "y" "z" "Rx" "Ry" "xBd" "yBd")
(use "RealLeAbs")
;; 3,4
(simpreal (pf "z===(1#2)*(z+z)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlusTwo")
(use "RealLeTrans" (pt "abs x"))
(use "RealLeIdAbs")
(use "Rx")
(use "xBd")
(use "RealLeTrans" (pt "abs y"))
(use "RealLeIdAbs")
(use "Ry")
(use "yBd")
;; ?^6:z===(1#2)*(z+z)
(use "RealHalfPlus")
(autoreal)
;; ?^4:~((1#2)*(x+y))<<=z
(simpreal "<-" (pf "~ ~z===z"))
(use "RealLeUMinus")
(simpreal (pf "~z===RealTimes(1#2)(~z+ ~z)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlusTwo")
(simpreal "<-" (pf "~ ~x===x"))
(use "RealLeUMinus")
(use "RealLeTrans" (pt "abs x"))
(simpreal "<-" "RealAbsUMinus")
(use "RealLeIdAbs")
(autoreal)
(use "xBd")
(use "RealUMinusUMinus")
(use "Rx")

(simpreal "<-" (pf "~ ~y===y"))
(use "RealLeUMinus")
(use "RealLeTrans" (pt "abs y"))
(simpreal "<-" "RealAbsUMinus")
(use "RealLeIdAbs")
(autoreal)
(use "yBd")
(use "RealUMinusUMinus")
(use "Ry")
;; ?^23:~z===(1#2)*(~z+ ~z)
(use "RealHalfPlus")
(autoreal)
(use "RealUMinusUMinus")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealAbsAvBd")

