;; 2021-10-21.  int.scm

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "pos.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")"))

;; ;; lib/list.scm needed for representing pos as list of booleans

;; (if (not (assoc "list" ALGEBRAS))
;;     (myerror "First execute (libload \"list.scm\")"))

(if (not (assoc "pos" ALGEBRAS))
    (myerror "First execute (libload \"pos.scm\")"))

(display "loading int.scm ...") (newline)

(define (synt-non-zero? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term))
	(type (term-to-type term)))
    (and
     (alg-form? type)
     (or
      (string=? (alg-form-to-name type) "pos")
      (and
       (term-in-const-form? op)
       (let* ((const (term-in-const-form-to-const op))
	      (name (const-to-name const)))
	 (cond
	  ((member name '("PosToNat" "Succ" "IntPos" "IntNeg")) #t)
	  ((member name '("NatToPos"))
	   (synt-non-zero? (car args)))
	  ((member name '("NatPlus" "IntPlus"))
	   (or (and (synt-pos? (car args)) (synt-nneg? (cadr args)))
	       (and (synt-nneg? (car args)) (synt-pos? (cadr args)))))
	  ((member name '("NatTimes" "IntTimes"))
	   (and (synt-non-zero? (car args)) (synt-non-zero? (cadr args))))
	  ((member name '("NatExp" "IntExp"))
	   (synt-non-zero? (car args)))
	  ((member name '("NatToInt"))
	   (synt-non-zero? (car args)))
	  (else #f))))))))

(define (synt-pos? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term))
	(type (term-to-type term)))
    (and
     (alg-form? type)
     (or
      (string=? (alg-form-to-name type) "pos")
      (and
       (term-in-const-form? op)
       (let* ((const (term-in-const-form-to-const op))
	      (name (const-to-name const)))
	 (cond
	  ((member name '("PosToNat" "Succ" "IntPos")) #t)
	  ((member name '("NatPlus" "IntPlus"))
	   (or (and (synt-pos? (car args)) (synt-nneg? (cadr args)))
	       (and (synt-nneg? (car args)) (synt-pos? (cadr args)))))
	  ((member name '("NatTimes" "IntTimes"))
	   (or (and (synt-pos? (car args)) (synt-pos? (cadr args)))
	       (and (synt-neg? (car args)) (synt-neg? (cadr args)))))
	  ((member name '("NatExp" "IntExp"))
	   (synt-pos? (car args)))
	  ((member name '("NatToInt"))
	   (synt-pos? (car args)))
	  (else #f))))))))

(define (synt-nneg? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term))
	(type (term-to-type term)))
    (and
     (alg-form? type)
     (or
      (member (alg-form-to-name type) '("pos" "nat"))
      (and
       (term-in-const-form? op)
       (let* ((const (term-in-const-form-to-const op))
	      (name (const-to-name const)))
	 (cond
	  ((member name '("IntZero" "IntPos")) #t)
	  ((member name '("IntPlus"))
	   (and (synt-nneg? (car args) (synt-nneg? (cadr args)))))
	  ((member name '("IntTimes"))
	   (or (and (synt-nneg? (car args)) (synt-nneg? (cadr args)))
	       (and (synt-neg? (car args)) (synt-neg? (cadr args)))))
	  ((member name '("IntExp"))
	   (synt-nneg? (car args)))
	  ((member name '("NatToInt"))
	   (synt-nneg? (car args)))
	  (else #f))))))))

(define (synt-neg? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term))
	(type (term-to-type term)))
    (and
     (alg-form? type)
     (term-in-const-form? op)
     (let* ((const (term-in-const-form-to-const op))
	    (name (const-to-name const)))
       (cond
	((member name '("IntNeg")) #t)
	((member name '("NatPlus" "IntPlus"))
	 (or (and (synt-neg? (car args)) (synt-npos? (cadr args)))
	     (and (synt-npos? (car args)) (synt-neg? (cadr args)))))
	((member name '("NatTimes" "IntTimes"))
	 (or (and (synt-pos? (car args)) (synt-neg? (cadr args)))
	     (and (synt-neg? (car args)) (synt-pos? (cadr args)))))
	(else #f))))))

(define (synt-npos? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term))
	(type (term-to-type term)))
    (and
     (alg-form? type)
     (term-in-const-form? op)
     (let* ((const (term-in-const-form-to-const op))
	    (name (const-to-name const)))
       (cond
	((member name '("Zero" "IntZero" "IntNeg")) #t)
	((member name '("NatPlus" "IntPlus"))
	 (and (synt-npos? (car args)) (synt-npos? (cadr args))))
	((member name '("IntTimes"))
	 (or (and (synt-npos? (car args) (synt-nneg? (cadr args))))
	     (and (synt-nneg? (car args) (synt-npos? (cadr args))))))
	(else #f))))))

;; 1.  Integers
;; ============

;; An integer is either positive or zero or negative.

(add-algs
 "int" '("IntPos" "pos=>int") '("IntZero" "int") '("IntNeg" "pos=>int"))
(add-var-name  "k" "j" "i" (py "int"))

(add-totality "int")
(add-totalnc "int")
(add-co "TotalInt")
(add-co "TotalIntNc")

(add-eqp "int")
(add-co "EqPInt")
(add-eqpnc "int")
(add-co "EqPIntNc")

;; IntTotalVar
(set-goal "all k TotalInt k")
(cases)
(assume "p")
(use "TotalIntIntPos")
(use "PosTotalVar")
(use "TotalIntIntZero")
(assume "p")
(use "TotalIntIntNeg")
(use "PosTotalVar")
;; Proof finished.
(save "IntTotalVar")

;; IntEqToEqD
(set-goal "all k,j(k=j -> k eqd j)")
(cases) 
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(assume "p=q")
(simp "p=q")
(use "InitEqD")
;; 7
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
;; 8
(assume "q")
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
;; 3
(cases)
;; 20-22
(assume "q" "Absurd")
(use "EfEqD")
(use "Absurd")
;; 21
(assume "Useless")
(use "InitEqD")
;; 22
(assume "q" "Absurd")
(use "EfEqD")
(use "Absurd")
;; 4
(assume "p")
(cases)
;; 29-31
(assume "q" "Absurd")
(use "EfEqD")
(use "Absurd")
;; 30
(assume "Absurd")
(use"EfEqD")
(use "Absurd")
;; 32
(assume "q")
(ng)
(assume "p=q")
(simp "p=q")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "IntEqToEqD")

;; IntIfTotal
(set-goal "allnc k^(TotalInt k^ ->
 allnc alpha^,(pos=>alpha)^1,(pos=>alpha)^2(
 Total alpha^ ->
 allnc p^(TotalPos p^ -> Total((pos=>alpha)^1 p^)) ->
 allnc p^(TotalPos p^ -> Total((pos=>alpha)^2 p^)) ->
 Total[if k^ (pos=>alpha)^1 alpha^ (pos=>alpha)^2]))")
(assume "k^" "Tk" "alpha^" "(pos=>alpha)^1" "(pos=>alpha)^2"
	"Talpha" "Tf1" "Tf2")
(elim "Tk")
(assume "p^" "Tp")
(ng #t)
(use "Tf1")
(use "Tp")
(use "Talpha")
(assume "p^" "Tp")
(ng #t)
(use "Tf2")
(use "Tp")
;; Proof finished.
(save "IntIfTotal")

;; To prove extensionality of pconsts of level >=2 we will need
;; properties of EqPInt.  There are collected here.

;; EqPIntToTotalLeft
(set-goal "allnc k^,j^(EqPInt k^ j^ -> TotalInt k^)")
(assume "k^" "j^" "EqPkj")
(elim "EqPkj")
;; 3-5
(assume "p^1" "p^2" "EqPp1p2")
(use "TotalIntIntPos")
(use "EqPPosToTotalLeft" (pt "p^2"))
(use "EqPp1p2")
;; 4
(use "TotalIntIntZero")
;; 5
(assume "p^1" "p^2" "EqPp1p2")
(use "TotalIntIntNeg")
(use "EqPPosToTotalLeft" (pt "p^2"))
(use "EqPp1p2")
;; Proof finished.
(save "EqPIntToTotalLeft")

;; EqPIntToTotalRight
(set-goal "allnc k^,j^(EqPInt k^ j^ -> TotalInt j^)")
(assume "k^" "j^" "EqPkj")
(elim "EqPkj")
;; 3-5
(assume "p^1" "p^2" "EqPp1p2")
(use "TotalIntIntPos")
(use "EqPPosToTotalRight" (pt "p^1"))
(use "EqPp1p2")
;; 4
(use "TotalIntIntZero")
;; 5
(assume "p^1" "p^2" "EqPp1p2")
(use "TotalIntIntNeg")
(use "EqPPosToTotalRight" (pt "p^1"))
(use "EqPp1p2")
;; Proof finished.
(save "EqPIntToTotalRight")

;; EqPIntToEqD
(set-goal "allnc k^,j^(EqPInt k^ j^ -> k^ eqd j^)")
(assume "k^" "j^" "EqPkj")
(elim "EqPkj")
;; 3-5
(assume "p^1" "p^2" "EqPp1p2")
(simp (pf "p^1 eqd p^2"))
(use "InitEqD")
(use "EqPPosToEqD")
(use "EqPp1p2")
;; 4
(use "InitEqD")
;; 5
(assume "p^1" "p^2" "EqPp1p2")
(simp (pf "p^1 eqd p^2"))
(use "InitEqD")
(use "EqPPosToEqD")
(use "EqPp1p2")
;; Proof finished.
(save "EqPIntToEqD")
;; (cdp)

;; EqPIntRefl
(set-goal "allnc k^(TotalInt k^ -> EqPInt k^ k^)")
(assume "k^" "Tk")
(elim "Tk")
;; 3-5
(assume "p^" "Tp")
(use "EqPIntIntPos")
(use "EqPPosRefl")
(use "Tp")
;; 4
(use "EqPIntIntZero")
;; 5
(assume "p^" "Tp")
(use "EqPIntIntNeg")
(use "EqPPosRefl")
(use "Tp")
;; Proof finished.
(save "EqPIntRefl")
;; (cdp)

;; EqPIntSym
(set-goal "allnc k^,j^(EqPInt k^ j^ -> EqPInt j^ k^)")
(assume "k^" "j^" "EqPkj")
(elim "EqPkj")
(assume "p^" "q^" "EqPpq")
(use "EqPIntIntPos")
(use "EqPPosSym")
(use "EqPpq")
(use "EqPIntIntZero")
(assume "p^" "q^" "EqPpq")
(use "EqPIntIntNeg")
(use "EqPPosSym")
(use "EqPpq")
;; Proof finished.
(save "EqPIntSym")
;; (cdp)

;; make-numeric-term-wrt-pos produces an int object for n<=0, and a pos
;; object for a positive integer.

(define (make-numeric-term-wrt-pos n)
  (cond ((zero? n) (make-term-in-const-form (constr-name-to-constr "IntZero")))
	((= n 1) (pt "One"))
	((< n 0)  (make-term-in-app-form
		    (make-term-in-const-form (constr-name-to-constr "IntNeg"))
		    (make-numeric-term-wrt-pos (- n))))
	((even? n) (make-term-in-app-form
		    (make-term-in-const-form (constr-name-to-constr "SZero"))
		    (make-numeric-term-wrt-pos (/ n 2))))
	((odd? n) (make-term-in-app-form
		   (make-term-in-const-form (constr-name-to-constr "SOne"))
		   (make-numeric-term-wrt-pos (/ (- n 1) 2))))
	(else
	 (myerror "make-numeric-term-wrt-pos" "integer expected" n))))

(define (make-numeric-term n)
  (if NAT-NUMBERS
      (make-numeric-term-wrt-nat n)
      (make-numeric-term-wrt-pos n)))

;; (define make-numeric-term make-numeric-term-wrt-pos)

(add-token
 "IntN"
 'prefix-op
 (lambda (x) (mk-term-in-app-form (pt "IntNeg") x)))

(add-token
 "IntP"
 'prefix-op
 (lambda (x) (mk-term-in-app-form (pt "IntPos") x)))

(add-display
 (py "int")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (= 1 (length args)))
	 (let ((name (const-to-name (term-in-const-form-to-const op))))
	   (cond
	    ((string=? name "IntNeg")
	     (list 'prefix-op "IntN" (term-to-token-tree (car args))))
	    ((string=? name "IntPos")
	     (term-to-token-tree (car args)))
;; added 2007-09-05
	    ((string=? name "NatToInt")
	     (term-to-token-tree (car args)))
	    (else #f)))
	 #f))))

(define (int-numeral-value? value)
  (and (nbe-constr-value? value)
       (let* ((name (nbe-constr-value-to-name value))
	      (args (nbe-constr-value-to-args value))
	      (vals (map nbe-object-to-value args)))
	 (or (and (string=? "IntPos" name)
		  (pos-numeral-value? (car vals)))
	     (string=? "IntZero" name)
	     (and (string=? "IntNeg" name)
		  (pos-numeral-value? (car vals)))))))

(define (int-numeral-value-to-number value)
  (let* ((name (nbe-constr-value-to-name value))
	 (args (nbe-constr-value-to-args value))
	 (vals (map nbe-object-to-value args)))
    (cond
     ((string=? "IntNeg" name) (- (pos-numeral-value-to-number (car vals))))
     ((string=? "IntZero" name) 0)
     ((string=? "IntPos" name) (pos-numeral-value-to-number (car vals)))
     (else (myerror "int-numeral-value-to-number" "unexpected arg" value)))))

;; 2. Parsing and display for arithmetical operations
;; ==================================================

(add-program-constant "NatToInt" (py "nat=>int"))

;; When later we have proved totality of PosToNat and NatToInt we need
;; to replace their item accordingly.

;; We want the path from "pos" to "int" going through "nat" to be in
;; the association list AFTER the edge from "pos" to "int" because in
;; this case the function "algebras-to-embedding" choose the edge and
;; not the path.

(add-item-to-algebra-edge-to-embed-term-alist
 "nat" "int"
 (let ((var (make-var (make-alg "nat") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
         (make-term-in-const-form
          (pconst-name-to-pconst "NatToInt"))
         (make-term-in-var-form var)))))

(add-item-to-algebra-edge-to-embed-term-alist
 "pos" "int"
 (let ((var (make-var (make-alg "pos") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
         (make-term-in-const-form
          (constr-name-to-constr "IntPos"))
         (make-term-in-var-form var)))))

;; (alg-le? (make-alg "pos") (make-alg "int"))
;; (alg-le? (make-alg "pos") (make-alg "nat"))
;; (alg-le? (make-alg "nat") (make-alg "pos"))
;; (alg-le? (make-alg "nat") (make-alg "int"))

(add-program-constant "IntS" (py "int=>int"))
(add-program-constant "IntPred" (py "int=>int"))
(add-program-constant "IntPlus" (py "int=>int=>int"))
(add-program-constant "IntUMinus" (py "int=>int"))
(add-program-constant "IntMinus" (py "int=>int=>int"))
(add-program-constant "IntTimes" (py "int=>int=>int"))
(add-program-constant "IntAbs" (py "int=>int"))
(add-program-constant "IntSg" (py "int=>int"))
(add-program-constant "IntExp" (py "int=>nat=>int"))
(add-program-constant "IntMax" (py "int=>int=>int"))
(add-program-constant "IntMin" (py "int=>int=>int"))
(add-program-constant "IntLt" (py "int=>int=>boole"))
(add-program-constant "IntLe" (py "int=>int=>boole"))

;; Program constants used for extraction of program constants to
;; Haskell, where computation rules
;;
;;    f (SZero x) = ... x ...
;;
;; must be transformed into e.g.
;;    f n | even n = ... TranslationPosHalfEven n ...

(add-program-constant "TranslationPosAsInt" (py "int=>pos"))

(add-token-and-type-to-name "+" (py "int") "IntPlus")

(add-token "~" 'prefix-op (make-term-creator1 "~" "int"))
(add-token-and-type-to-name "~" (py "int") "IntUMinus")

(add-token "-" 'add-op (make-term-creator "-" "int"))
(add-token-and-type-to-name "-" (py "int") "IntMinus")

(add-token-and-type-to-name "*" (py "int") "IntTimes")

(add-token "abs" 'prefix-op (make-term-creator1 "abs" "int"))
(add-token-and-type-to-name "abs" (py "int") "IntAbs")

(add-token "sg" 'prefix-op (make-term-creator1 "sg" "int"))
(add-token-and-type-to-name "sg" (py "int") "IntSg")

(add-token-and-types-to-name "**" (list (py "int") (py "pos")) "IntExp")
(add-token-and-types-to-name "**" (list (py "int") (py "nat")) "IntExp")

(add-token-and-type-to-name "max" (py "int") "IntMax")
(add-token-and-type-to-name "min" (py "int") "IntMin")
(add-token-and-type-to-name "<" (py "int") "IntLt")
(add-token-and-type-to-name "<=" (py "int") "IntLe")

(add-display (py "int") (make-display-creator "IntPlus" "+" 'add-op))
(add-display (py "int") (make-display-creator1 "IntUMinus" "~" 'prefix-op))
(add-display (py "int") (make-display-creator "IntMinus" "-" 'add-op))
(add-display (py "int") (make-display-creator "IntTimes" "*" 'mul-op))
(add-display (py "nat") (make-display-creator1 "IntAbs" "abs" 'prefix-op))
(add-display (py "int") (make-display-creator1 "IntAbs" "abs" 'prefix-op))
(add-display (py "int") (make-display-creator1 "IntSg" "sg" 'prefix-op))
(add-display (py "int") (make-display-creator "IntExp" "**" 'exp-op))
(add-display (py "int") (make-display-creator "IntMax" "max" 'mul-op))
(add-display (py "int") (make-display-creator "IntMin" "min" 'mul-op))
(add-display (py "boole") (make-display-creator "IntLt" "<" 'rel-op))
(add-display (py "boole") (make-display-creator "IntLe" "<=" 'rel-op))

;; 3. Arithmetic for integers
;; ==========================

;; IntEqTotal
(set-goal "allnc i^(
 TotalInt i^ -> allnc j^(TotalInt j^ -> TotalBoole(i^ =j^)))")
(assume "i^" "Ti")
(elim "Ti") ;3-5
(assume "p^" "Tp" "j^" "Tj")
(elim "Tj") ;7-9
(assume "q^" "Tq")
(use "PosEqTotal")
(use "Tp")
(use "Tq")
;; 8
(ng #t)
(use "TotalBooleFalse")
;; 9
(ng #t)
(strip)
(use "TotalBooleFalse")
;; 4
(assume "j^" "Tj")
(elim "Tj")
(ng #t)
(strip)
(use "TotalBooleFalse")
(ng #t)
(use "TotalBooleTrue")
(ng #t)
(strip)
(use "TotalBooleFalse")
;; 5
(assume "p^" "Tp" "j^" "Tj")
(elim "Tj")
(ng #t)
(strip)
(use "TotalBooleFalse")
(ng #t)
(use "TotalBooleFalse")
(assume "q^" "Tq")
(ng #t)
(use "PosEqTotal")
(use "Tp")
(use "Tq")
;; Proof finished.
(save "IntEqTotal")

;; Rules for IntS, IntPred

(add-computation-rules
 "IntS IntZero" "IntP One"
 "IntS(IntP p)" "IntP(PosS p)"
 "IntS(IntN One)" "IntZero"
 "IntS(IntN(SZero p))" "IntN(PosPred(SZero p))"
 "IntS(IntN(SOne p))" "IntN(SZero p)")

;; IntSTotal
(set-totality-goal "IntS")
(assume "k^" "Tk")
(elim "Tk")

(assume "p^" "Tp")
(elim "Tp")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "TotalPosOne")

(assume "p^1" "Tp1" "Useless")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "Tp1")

(assume "p^1" "Tp1" "Useless")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "PosSTotal")
(use "Tp1")

(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")

(assume "p^1" "Tp1")
(elim "Tp1")
(ng #t)
(use "TotalIntIntZero")

(assume "p^2" "Tp2" "Useless")
(ng #t)
(use "TotalIntIntNeg")
(use "PosPredTotal")
(use "TotalPosSZero")
(use "Tp2")

(assume "p^2" "Tp2" "Useless")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosSZero")
(use "Tp2")
;; Proof finished.
(save-totality)

;; Rules for NatToInt

(add-computation-rules
 "NatToInt Zero" "IntZero"
 "NatToInt(Succ n)" "IntS(NatToInt n)")

;; NatToIntTotal
(set-totality-goal "NatToInt")
(assume "n^" "Tn")
(elim "Tn")
;; ?_3:TotalInt Zero
(use "TotalIntIntZero")
;; ?_4:allnc nat^(TotalNat nat^ -> TotalInt nat^ -> TotalInt(Succ nat^))
(assume "m^" "Tm" "IH")
(ng #t)
;; ?_6:TotalInt(IntS m^)
(use "IntSTotal")
(use "IH")
;; Proof finished.
(save "NatToIntTotal")

(replace-item-in-algebra-edge-to-embed-term-alist
 "nat" "int"
 (let ((var (make-var (make-alg "nat") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
	 (make-term-in-const-form
	  (pconst-name-to-pconst "NatToInt"))
	 (make-term-in-var-form var)))))

;; Rules for IntPred

(add-computation-rules
 "IntPred IntZero" "IntN One"
 "IntPred(IntN p)" "IntN(PosS p)"
 "IntPred(IntP One)" "IntZero"
 "IntPred(IntP(SZero p))" "IntP(PosPred(SZero p))"
 "IntPred(IntP(SOne p))" "IntP(SZero p)")

;; IntPredTotal
(set-totality-goal "IntPred")
(use "AllTotalElim")
(cases)
;; 3-5
(cases)
;; 6-8
(ng)
(use "IntTotalVar")
;; 7
(assume "p")
(ng)
(use "IntTotalVar")
;; 8
(assume "p")
(ng)
(use "IntTotalVar")
;; 4
(ng)
(use "IntTotalVar")
;; 5
(assume "p")
(ng)
(use "IntTotalVar")
;; Proof finished.
(save-totality)

(set-goal "all p IntPred(PosS p)=p")
(cases)
;; 2-4
(ng)
(use "Truth")
;; 3
(assume "p")
(ng)
(use "Truth")
;; 4
(assume "p")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntPred(PosS p)" "IntPos p")

(set-goal "all k IntPred(IntS k)=k")
(cases)
;; 2-4
(cases)
(ng)
(use "Truth")
(assume "p")
(ng #t)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
;; 3
(use "Truth")
;; 4
(cases)
(ng)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntPred(IntS k)" "k")

(set-goal "all k IntS(IntPred k)=k")
(cases)
(cases)
(use "Truth")
(ng)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
(use "Truth")
(cases)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntS(IntPred k)" "k")

;; IntSInj
(set-goal "all k,j(IntS k=IntS j -> k=j)")
(assume "k" "j" "Sk=Sj")
(assert "IntPred(IntS k)=IntPred(IntS j)")
 (simp "Sk=Sj")
 (use "Truth")
(ng)
(assume "k=j")
(use "k=j")
;; Proof finished.
(save "IntSInj")

;; IntPredInj
(set-goal "all k,j(IntPred k=IntPred j -> k=j)")
(assume "k" "j" "Pk=Pj")
(assert "IntS(IntPred k)=IntS(IntPred j)")
 (simp "Pk=Pj")
 (use "Truth")
(ng)
(assume "k=j")
(use "k=j")
;; Proof finished.
(save "IntPredInj")

;; (display-pconst "IntPred")
;; (display-pconst "IntS")

;; Rules for IntPlus

(add-computation-rules
 "IntZero+k" "k"
 "IntP p+IntZero" "IntP p"
 "IntP p+IntP q" "IntP(p+q)"

 "IntP p+IntN q"
 "[if (p=q)
      IntZero
      [if (p<q) (IntN(q--p)) (IntP(p--q))]]"

 "IntN p+IntZero" "IntN p"

 "IntN p+IntP q"
 "[if (p=q)
      IntZero
      [if (p<q) (IntP(q--p)) (IntN(p--q))]]"

 "IntN p+IntN q" "IntN(p+q)")

;; IntPlusTotal
(set-totality-goal "IntPlus")
(use "AllTotalElim")
(cases)
;; 3-5
(assume "p")
(use "AllTotalElim")
(cases)
;; 8-10
(assume "q")
(use "IntTotalVar")
;; 9
(use "IntTotalVar")
;; 10
(assume "q")
(use "IntTotalVar")
;; 4
(use "AllTotalElim")
(assume "k")
(use "IntTotalVar")
;; 5
(assume "p")
(use "AllTotalElim")
(cases)
;; 17-19
(assume "q")
(use "IntTotalVar")
;; 18
(use "IntTotalVar")
;; 19
(assume "q")
(use "IntTotalVar")
;; Proof finished.
(save-totality)

;; Code discarded 2016-04-02
;; ;; IntPlusTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "IntPlus")
;; 	    (proof-to-formula (theorem-name-to-proof "IntPlusTotal")))))
;; (assume "k^" "k^0" "TMRk0k" "l^" "l^0" "TMRl0l")
;; (elim "TMRk0k")

;; ;; ?_3:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(pos^0+l^0)(pos^ +l^))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRl0l")

;; ;; ?_7:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0+pos^0)(p^ +pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (use "TotalIntIntPosMR")
;; (use "PosPlusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_8:TotalIntMR(p^0+0)(p^ +0)
;; (ng #t)
;; (use "TotalIntIntPosMR")
;; (use "TMRp0p")

;; ;; ?_9:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0+IntN pos^0)(p^ +IntN pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; ;; ?_17:TotalIntMR
;; ;;      [if (p^0=q^10) 0 [if (p^0<q^10) (IntN(q^10--p^0)) (p^0--q^10)]]
;; ;;      [if (p^ =q^1) 0 [if (p^ <q^1) (IntN(q^1--p^)) (p^ --q^1)]]
;; (use "BooleIfTotalReal")
;; (use "PosEqTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntZeroMR")
;; ;; ?_20:TotalIntMR[if (p^0<q^10) (IntN(q^10--p^0)) (p^0--q^10)]
;; ;;      [if (p^ <q^1) (IntN(q^1--p^)) (p^ --q^1)]
;; (use "BooleIfTotalReal")
;; (use "PosLtTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntNegMR")
;; (use "PosMinusTotalReal")
;; (use "TMRq10q1")
;; (use "TMRp0p")
;; (use "TotalIntIntPosMR")
;; (use "PosMinusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_4:TotalIntMR(0+l^0)(0+l^)
;; (ng #t)
;; (use "TMRl0l")

;; ;; ?_5:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(IntN pos^0+l^0)(IntN pos^ +l^))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRl0l")

;; ;; ?_36:allnc pos^,pos^0(
;; ;;       TotalPosMR pos^0 pos^ --> TotalIntMR(IntN p^0+pos^0)(IntN p^ +pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "BooleIfTotalReal")
;; (use "PosEqTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntZeroMR")
;; ;; ?_43:TotalIntMR[if (p^0<q^10) (q^10--p^0) (IntN(p^0--q^10))]
;; ;;      [if (p^ <q^1) (q^1--p^) (IntN(p^ --q^1))]
;; (use "BooleIfTotalReal")
;; (use "PosLtTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntPosMR")
;; (use "PosMinusTotalReal")
;; (use "TMRq10q1")
;; (use "TMRp0p")
;; (use "TotalIntIntNegMR")
;; (use "PosMinusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_37:TotalIntMR(IntN p^0+0)(IntN p^ +0)
;; (ng #t)
;; (use "TotalIntIntNegMR")
;; (use "TMRp0p")

;; ;; ?_38:allnc pos^,pos^0(
;; ;;       TotalPosMR pos^0 pos^ -->
;; ;;       TotalIntMR(IntN p^0+IntN pos^0)(IntN p^ +IntN pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntNegMR")
;; (use "PosPlusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; ;; Proof finished.
;; (save "IntPlusTotalReal")

(set-goal "all k k+IntZero=k")
(cases)
(ng #t)
(assume "p")
(use "Truth")
(use "Truth")
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k+IntZero" "k")

;; PosPlusIntPlus
(set-goal "all p,q p+q=IntPlus p q")
(assume "p" "q")
(use "Truth")
;; Proof finished.
(save "PosPlusIntPlus")

;; The computation rules for IntPlus involve case distinctions, which
;; makes it unpleasant to work with normalization.  As a substitute we
;; provide some lemmas expressing conditional equations.

;; IntPlusPNN
(set-goal "all p,q(p<q -> p+IntN q=IntN(q--p))")
(assume "p" "q" "p<q")
(ng)
(simp "p<q")
(ng)
(assert "p=q -> F")
 (assume "p=q")
 (simphyp-with-to "p<q" "p=q" "Absurd")
 (use "Absurd")
(assume "p=q -> F")
(simp "p=q -> F")
(use "Truth")
;; Proof finished.
(save "IntPlusPNN")

;; IntPlusPNP
(set-goal "all p,q(q<p -> p+IntN q=p--q)")
(assume "p" "q" "q<p")
(assert "p=q -> F")
 (assume "p=q")
 (simphyp-with-to "q<p" "p=q" "Absurd")
 (use "Absurd")
(assume "p=q -> F")
(ng)
(simp "p=q -> F")
(ng)
(drop "p=q -> F")
(assert "p<q -> F")
 (assume "p<q")
 (assert "p<p")
  (use "PosLtTrans" (pt "q"))
  (use "p<q")
  (use "q<p")
 (assume "Absurd")
 (use "Absurd")
(assume "p<q -> F")
(simp "p<q -> F")
(use "Truth")
;; Proof finished.
(save "IntPlusPNP")

;; IntPlusNPP
(set-goal "all p,q(p<q -> IntN p+q=q--p)")
(assume "p" "q" "p<q")
(ng)
(simp "p<q")
(ng)
(assert "p=q -> F")
 (assume "p=q")
 (simphyp-with-to "p<q" "p=q" "Absurd")
 (use "Absurd")
(assume "p=q -> F")
(simp "p=q -> F")
(use "Truth")
;; Proof finished.
(save "IntPlusNPP")

;; IntPlusNPN
(set-goal "all p,q(q<p -> IntN p+q=IntN(p--q))")
(assume "p" "q" "q<p")
(assert "p=q -> F")
 (assume "p=q")
 (simphyp-with-to "q<p" "p=q" "Absurd")
 (use "Absurd")
(assume "p=q -> F")
(ng)
(simp "p=q -> F")
(ng)
(drop "p=q -> F")
(assert "p<q -> F")
 (assume "p<q")
 (assert "p<p")
  (use "PosLtTrans" (pt "q"))
  (use "p<q")
  (use "q<p")
 (assume "Absurd")
 (use "Absurd")
(assume "p<q -> F")
(simp "p<q -> F")
(use "Truth")
;; Proof finished.
(save "IntPlusNPN")

;; IntPlusComm
(set-goal "all k,j k+j=j+k")
;; We need an auxiliary lemma
(assert "all p,q p+IntN q=IntN q+p")
(assume "p" "q")
(use "PosLeLtCases" (pt "p") (pt "q"))
;; 3,4
(assume "p<=q")
(use "PosLeCases" (pt "p") (pt "q"))
;; 6-8
(use "p<=q")
;; 7
(assume "p<q")
(ng #t)
(simp "p<q")
(assert "q<p -> p<p")
 (use "PosLeLtTrans")
 (use "p<=q")
(assume "q<p -> F")
(ng)
(simp "q<p -> F")
(ng)
(cases (pt "p=q"))
;; 19-20
(assume "p=q")
(simp "p=q")
(use "Truth")
;; 20
(assume "p=q -> F")
(assert "q=p -> F")
 (assume "q=p")
 (use "p=q -> F")
 (simp "q=p")
 (use "Truth")
(assume "q=p -> F")
(simp "q=p -> F")
(use "Truth")
;; 8
(assume "p=q")
(simp "p=q")
(use "Truth")
;; 4
(assume "q<p")
(ng)
(simp "q<p")
(assert "p<q -> q<q")
 (use "PosLtTrans")
 (use "q<p")
(assume "p<q -> F")
(ng)
(simp "p<q -> F")
(ng)
(cases (pt "p=q"))
;; 43-44
(assume "p=q")
(simp "p=q")
(use "Truth")
;; 44
(assume "p=q -> F")
(assert "q=p -> F")
 (assume "q=p")
 (use "p=q -> F")
 (simp "q=p")
 (use "Truth")
(assume "q=p -> F")
(simp "q=p -> F")
(use "Truth")
;; Assertion proved
(assume "IntPlusCommAux")
;; Now the proof of IntPlusComm starts properly.
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(use "PosPlusComm")
;; 7
(ng)
(use "Truth")
;; 8
(assume "q")
(use "IntPlusCommAux")
;; 3
(assume "int")
(ng)
(use "Truth")
;; 4
(assume "q")
(cases)
;; 16-18
(assume "p")
(simp "IntPlusCommAux")
(use "Truth")
;; 17
(ng)
(use "Truth")
;; 18
(assume "p")
(ng)
(use "PosPlusComm")
;; Proof finished.
(save "IntPlusComm")

;; To prove IntPlusAssoc (from IntPlusAssocPPN) we use IntUMinus.
;; Therefore we postpone this until we get to IntUMinus.

;; IntPSZero
(set-goal "all p IntP(SZero p)=IntP p + IntP p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
;; 4
(assume "p" "IH")
(ng #t)
(simp "<-" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
(save "IntPSZero")

;; IntPSOne
(set-goal "all p IntP(SOne p)=IntS(IntP p + IntP p)")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IntPSZero")
;; 4
(assume "p" "IH")
(ng #t)
(simp "<-" "IH")
(use "Truth")
;; Proof finished.
(save "IntPSOne")

;; IntPNatToPosEqNatToInt
(set-goal "all n(Zero<n -> IntP(NatToPos n)=NatToInt n)")
(ind)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "n" "IH" "Useless")
(simp "SuccPosS")
(simp "<-" "IntS1CompRule")
(simp "IH")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "IntPNatToPosEqNatToInt")

;; PosToNatToIntId
(set-goal "all p NatToInt(PosToNat p)=IntP p")
(assume "p")
(simp "<-" "IntPNatToPosEqNatToInt")
(use "NatToPosToNatId")
(use "NatLt0Pos")
;; Proof finished.
(save "PosToNatToIntId")

;; Added 2021-10-19

;; IntPlusCompat
(set-goal "all k,j,i,i0(k=j -> i=i0 -> k+i=j+i0)")
(assume "k" "j" "i" "i0" "k=j" "i=i0")
(simp "k=j")
(simp "i=i0")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "IntPlusCompat")

(add-program-constant "IntToPos" (py "int=>pos"))
(add-computation-rules
 "IntToPos 0" "1"
 "IntToPos p" "p"
 "IntToPos IntN p" "p")

(set-totality-goal "IntToPos")
(fold-alltotal)
(cases)
(assume "p")
(use "TotalVar")
(use "TotalVar")
(use "TotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; The following is not used any more:
;; NatToIntDouble
;; (set-goal "all nat NatToInt(NatDouble nat)=NatToInt nat + NatToInt nat")
;; (ind)
;; (ng #t)
;; (use "Truth")
;; (assume "nat" "IH")
;; (ng #t)
;; (simp "IH")
;; ;; ?_7:IntS(IntS(IntPlus nat nat))=IntS nat+IntS nat
;; (use "Truth")
;; ;; Proof finished.
;; (save "NatToIntDouble")

;; Rules for IntUMinus

(add-computation-rules
 "~IntZero" "IntZero"
 "~IntP p" "IntN p"
 "~IntN p" "IntP p")

;; IntUMinusTotal
(set-totality-goal "IntUMinus")
(use "AllTotalElim")
(cases)
;; 3-5
(assume "p")
(use "IntTotalVar")
;; 4
(use "IntTotalVar")
;; 5
(assume "p")
(use "IntTotalVar")
;; Proof finished.
(save-totality)

(set-goal "all k ~ ~k=k")
(cases)
;; 2-4
(assume "p")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~ ~k" "k")

(set-goal "all k,j ~(k+j)= ~k+ ~j")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(use "Truth")
;; 7
(use "Truth")
;; 8
(assume "q")
(ng)
(cases (pt "p=q"))
(assume "p=q")
(use "Truth")
(assume "p=q -> F")
(ng)
(cases (pt "p<q"))
(assume "p<q")
(use "Truth")
(assume "p<q -> F")
(use "Truth")
;; 3
(assume "k")
(use "Truth")
;; 4
(assume "p")
(cases)
;; 23-25
(assume "q")
(ng)
(cases (pt "p=q"))
(assume "p=q")
(use "Truth")
(assume "p=q -> F")
(ng)
(cases (pt "p<q"))
(assume "p<q")
(use "Truth")
(assume "p<q -> F")
(use "Truth")
;; 24
(use "Truth")
;; 25
(assume "q")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~(k+j)" "~k+ ~j")

;; IntUMinusInj
(set-goal "all k,j (~k= ~j)=(k=j)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(use "Truth")
;; 7
(ng)
(use "Truth")
;; 8
(assume "q")
(ng)
(use "Truth")
;; 3
(cases)
(assume "q")
(ng)
(use "Truth")
(ng)
(use "Truth")
(assume "q")
(ng)
(use "Truth")
;; 4
(assume "p")
(cases)
;; 23-25
(assume "q")
(ng)
(use "Truth")
;; 24
(ng)
(use "Truth")
;; 25
(assume "q")
(ng)
(use "Truth")
;; Proof finished.
(save "IntUMinusInj")

(set-goal "all k ~(IntS k)=IntPred~k")
(cases)
;; 2-4
(assume "p")
(use "Truth")
;; 3
(ng)
(use "Truth")
;; 4
(ng)
(cases)
(ng)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~(IntS k)" "IntPred~k")

(set-goal "all k ~(IntPred k)=IntS~k")
(assume "k")
(simp "<-" "IntUMinusInj")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~(IntPred k)" "IntS~k")

;; (display-pconst "IntUMinus")

;; Rules for IntMinus

(add-computation-rules
 "k-j" "k+ ~j")

;; IntMinusTotal
(set-totality-goal "IntMinus")
(use "AllTotalElim")
(assume "k")
(use "AllTotalElim")
(assume "j")
(ng)
(use "IntTotalVar")
;; Proof finished.
(save-totality)

;; Code discarded 2016-04-02
;; ;; IntMinusTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "IntMinus")
;; 	    (proof-to-formula (theorem-name-to-proof "IntMinusTotal")))))
;; (assume "k^" "k^0" "TMRk0k" "l^" "l^0" "TMRl0l")
;; (elim "TMRk0k")

;; ;; ?_3:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(pos^0-l^0)(pos^ -l^))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRl0l")

;; ;; ?_7:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0-pos^0)(p^ -pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; ;; ?_11:TotalIntMR
;; ;;      [if (p^0=q^10) 0 [if (p^0<q^10) (IntN(q^10--p^0)) (p^0--q^10)]]
;; ;;      [if (p^ =q^1) 0 [if (p^ <q^1) (IntN(q^1--p^)) (p^ --q^1)]]
;; (use "BooleIfTotalReal")
;; (use "PosEqTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntZeroMR")
;; (use "BooleIfTotalReal")
;; (use "PosLtTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntNegMR")
;; (use "PosMinusTotalReal")
;; (use "TMRq10q1")
;; (use "TMRp0p")
;; (use "TotalIntIntPosMR")
;; (use "PosMinusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_8:TotalIntMR(p^0-0)(p^ -0)
;; (ng #t)
;; (use "TotalIntIntPosMR")
;; (use "TMRp0p")

;; ;; ?_9:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0-IntN pos^0)(p^ -IntN pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntPosMR")
;; (use "PosPlusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_4:TotalIntMR(0-l^0)(0-l^)
;; (elim "TMRl0l")
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntNegMR")
;; (use "TMRq10q1")
;; (use "TotalIntIntZeroMR")
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntPosMR")
;; (use "TMRq10q1")

;; ;; ?_5:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(IntN pos^0-l^0)(IntN pos^ -l^))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRl0l")

;; ;; ?_45:allnc pos^,pos^0(
;; ;;       TotalPosMR pos^0 pos^ --> TotalIntMR(IntN p^0-pos^0)(IntN p^ -pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntNegMR")
;; (use "PosPlusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_46:TotalIntMR(IntN p^0-0)(IntN p^ -0)
;; (ng #t)
;; (use "TotalIntIntNegMR")
;; (use "TMRp0p")

;; ;; ?_47:allnc pos^,pos^0(
;; ;;       TotalPosMR pos^0 pos^ -->
;; ;;       TotalIntMR(IntN p^0-IntN pos^0)(IntN p^ -IntN pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; ;; ?_56:TotalIntMR
;; ;;      [if (p^0=q^10) 0 [if (p^0<q^10) (q^10--p^0) (IntN(p^0--q^10))]]
;; ;;      [if (p^ =q^1) 0 [if (p^ <q^1) (q^1--p^) (IntN(p^ --q^1))]]
;; (use "BooleIfTotalReal")
;; (use "PosEqTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntZeroMR")
;; (use "BooleIfTotalReal")
;; (use "PosLtTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntPosMR")
;; (use "PosMinusTotalReal")
;; (use "TMRq10q1")
;; (use "TMRp0p")
;; (use "TotalIntIntNegMR")
;; (use "PosMinusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; ;; Proof finished.
;; (save "IntMinusTotalReal")

;; The following can only be done after IntTimes IntMax IntMin
;; IntTimesUMinusId
;; all k,j ~k*j= ~(k*j)
;; IntTimesIdUMinus
;; all k,j k* ~j= ~(k*j)
;; IntUMinusMax
;; IntUMinusMin

;; Next: IntPlusAssoc.  It suffices to prove IntPlusAssocPPN:
;; p+(q+IntN r)=p+q+IntN r.  This requires
;; comparison of p3 with q<p+p2, i.e., consideration of 5 cases:
;; p3<p2 p3=p2 p2<p3<p1+p2 p3=p1+p2 p1+p2<p3

;; IntPlusAssoc
(set-goal "all k,j,i k+(j+i)=k+j+i")
;; IntPlusAssocPPN
(assert "all p,q,r
 p+(q+IntN r)=IntP p+IntP q+IntN r")
(assume "p" "q" "r")
(use "PosLeLtCases" (pt "r") (pt "q"))
(assume "r<=q")
(use "PosLeCases"  (pt "r") (pt "q"))
(use "r<=q")
(drop "r<=q")
(assume "r<q")
;; Case r<q
(assert "r<p+q")
 (use "PosLtTrans" (pt "q"))
 (use "r<q")
 (use "Truth")
(assume "r<p+q")
;; ?_15:p+(q+IntN r)=IntPlus p q+IntN r
(simp "IntPlus2CompRule")
;; ?_16:p+(q+IntN r)=p+q+IntN r
(simp "IntPlusPNP")
;; ?_17:IntPlus p(q--r)=p+q+IntN r
(simp "IntPlusPNP")
;; ?_19:IntPlus p(q--r)=p+q--r
(simp "IntPlus2CompRule")
;; ?_21:=(p+(q--r))(p+q--r)
(simp "PosPlusMinus")
(use "Truth")
(use "r<q")
(use "r<p+q")
(use "r<q")
;; Case r=q
(assume "r=q")
(assert "IntP q+IntN r=0")
 (ng #t)
 (simp "r=q")
 (use "Truth")
(assume "q-r=0")
(simp "q-r=0")
(drop "q-r=0")
(simp "IntPlus2CompRule")
(simp "IntPlusPNP")
(simp "r=q")
(use "Truth")
(simp "r=q")
(use "Truth")
;; Case q<r.  Need further case distinction on r with p+q
(use "PosLeLtCases" (pt "r") (pt "p+q"))
(assume "r<=p+q")
(use "PosLeCases"  (pt "r") (pt "p+q"))
(use "r<=p+q")
(drop "r<=p+q")
(assume "r<p+q")
;; Case q<r<p+q
(assume "q<r")
(assert "r--q<p")
 (assert "p=p+q--q")
  (use "Truth")
 (assume "p=p+q-q")
 (simp "p=p+q-q")
 (drop "p=p+q-q")
 (use "PosLtMonMinusLeft")
 (use "r<p+q")
 (use "q<r")
(assume "r-q<p")
(simp "IntPlusPNN")
(simp "IntPlusPNP")
(simp "IntPlus2CompRule")
(simp "IntPlusPNP")
(simp "PosMinusMinus")
(use "Truth")
(use "r<p+q")
(use "q<r")
(use "r<p+q")
(use "r-q<p")
(use "q<r")
;; Case r=p+q
(drop "r<=p+q")
(assume "r=p+q" "q<r")
(simp "r=p+q")
(ng #t)
(assert "q=p+q -> F")
 (assume "q=p+q")
 (assert "q<p+q -> F")
  (simp "<-" "q=p+q")
  (assume "q<q")
  (use "q<q")
 (assume "q<p+q -> F")
 (use "q<p+q -> F")
 (use "Truth")
(assume "q=p+q -> F")
(simp "q=p+q -> F")
(use "Truth")
;; Case p+q<r
(assume "p+q<r" "q<r")
(simp "IntPlus2CompRule")
(simp "IntPlusPNN")
(simp "IntPlusPNN")
(simp "IntPlusPNN")
(simp "PosPlusComm")
(simp "PosMinusMinusLeft")
(use "Truth")
(simp "PosPlusComm")
(use "p+q<r")
(use "p+q<r")
(assert "p+q--q<r--q")
 (use "PosLtMonMinusLeft")
 (use "p+q<r")
 (use "Truth")
 (ng #t)
(assume "Hyp")
(use "Hyp")
(use "q<r")
;; Proof of assertion finished.
(assume "IntPlusAssocPPN")
;; Now we can tackle IntPlusAssoc.
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(cases)
;; 10-12
(assume "r")
(use "PosPlusAssoc" (pt "p") (pt "q") (pt "r"))
;; 11
(use "Truth")
;; 12
(assume "r")
(use "IntPlusAssocPPN")
;; 7
(assume "i")
(use "Truth")
;; 8
(assume "q")
(cases)
;; 17-19
(assume "r")
;; ?_20:p+(IntN q+r)=p+IntN q+r
(assert "IntN q+r=r+IntN q")
 (use "IntPlusComm")
(assume "IntN q+r=r+IntN q")
(simp "IntN q+r=r+IntN q")
(drop "IntN q+r=r+IntN q")
(simp "IntPlusAssocPPN")
(assert "IntPlus p r=IntPlus r p")
 (use "IntPlusComm")
(assume "IntPlus p r=IntPlus r p")
(simp "IntPlus p r=IntPlus r p")
(drop "IntPlus p r=IntPlus r p")
(simp "<-" "IntPlusAssocPPN")
(use "IntPlusComm")
;; 18
(use "Truth")
;; 19
(assume "r")
;; ?_33:p+(IntN q+IntN r)=p+IntN q+IntN r
(simp "<-" "IntUMinusInj")
(assert "IntN q= ~q")
 (use "Truth")
(assume "IntN q= ~q")
(simp "IntN q= ~q")
(assert "IntN r= ~r")
 (use "Truth")
(assume "IntN r= ~r")
(simp "IntN r= ~r")
;; ?_42:~(p+(~q+ ~r))= ~(p+ ~q+ ~r)
(simp "IntUMinus1RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus0RewRule")
;; ?_50:~p+IntPlus q r= ~p+q+r
(assert "~p+q+r=r+(~p+q)")
 (use "IntPlusComm")
(assume "~p+q+r=r+(~p+q)")
(simp "~p+q+r=r+(~p+q)")
(drop "~p+q+r=r+(~p+q)")
;; ?_55:~p+IntPlus q r=r+(~p+q)
(assert "~p+q=q+ ~p")
 (use "IntPlusComm")
(assume "~p+q=q+ ~p")
(simp "~p+q=q+ ~p")
(drop "~p+q=q+ ~p")
;; ?_60:~p+IntPlus q r=r+(q+ ~p)
(simp "IntPlusComm")
;; ?_61:IntPlus q r+ ~p=r+(q+ ~p)
(assert "IntN p= ~p")
 (use "Truth")
(assume "IntN p= ~p")
(simp "<-" "IntN p= ~p")
;; ?_65:IntPlus q r+IntN p=r+(q+IntN p)
(assert "IntPlus q r=IntPlus r q")
 (use "IntPlusComm")
(assume "IntPlus q r=IntPlus r q")
(simp "IntPlus q r=IntPlus r q")
(drop "IntPlus q r=IntPlus r q")
(simp "<-" "IntPlusAssocPPN")
(use "Truth")
;; 3
(assume "j" "i")
(use "Truth")
;; 4
(assume "p")
(cases)
;; 74-76
(assume "q")
(cases)
;; 78-80
(assume "r")
;; ?_81:IntN p+IntPlus q r=IntN p+q+r
(assert "IntPlus q r=IntPlus r q")
 (use "IntPlusComm")
(assume "IntPlus q r=IntPlus r q")
(simp "IntPlus q r=IntPlus r q")
(drop "IntPlus q r=IntPlus r q")
;; ?_86:IntN p+IntPlus r q=IntN p+q+r
(simp "IntPlusComm")
;; ?_87:IntPlus r q+IntN p=IntN p+q+r
(assert "IntN p+q+r=r+(IntN p+q)")
 (use "IntPlusComm")
(assume "IntN p+q+r=r+(IntN p+q)")
(simp "IntN p+q+r=r+(IntN p+q)")
(drop "IntN p+q+r=r+(IntN p+q)")
;; ?_92:IntPlus r q+IntN p=r+(IntN p+q)
(assert "IntN p+q=q+IntN p")
 (use "IntPlusComm")
(assume "IntN p+q=q+IntN p")
(simp "IntN p+q=q+IntN p")
(drop "IntN p+q=q+IntN p")
(simp "<-" "IntPlusAssocPPN")
(use "Truth")
;; 79
(use "Truth")
;; 80
(assume "r")
;; ?_99:IntN p+(q+IntN r)=IntN p+q+IntN r
(simp "<-" "IntUMinusInj")
(assert "IntN p= ~p")
 (use "Truth")
(assume "IntN p= ~p")
(simp "IntN p= ~p")
(assert "IntN r= ~r")
 (use "Truth")
(assume "IntN r= ~r")
(simp "IntN r= ~r")
;; ?_108:~(~p+(q+ ~r))= ~(~p+q+ ~r)
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
;; ?_116:p+(~q+r)=p+ ~q+r
(assert "~q+r=r+ ~q")
 (use "IntPlusComm")
(assume "~q+r=r+ ~q")
(simp "~q+r=r+ ~q")
(drop "~q+r=r+ ~q")
;; ?_121:p+(r+ ~q)=p+ ~q+r
(assert "IntN q= ~q")
 (use "Truth")
(assume "IntN q= ~q")
(simp "<-" "IntN q= ~q")
(simp "IntPlusAssocPPN")
;; ?_126:IntPlus p r+IntN q=p+IntN q+r
(assert "p+IntN q+r=r+(p+IntN q)")
 (use "IntPlusComm")
(assume "p+IntN q+r=r+(p+IntN q)")
(simp "p+IntN q+r=r+(p+IntN q)")
(drop "p+IntN q+r=r+(p+IntN q)")
(simp "IntPlusAssocPPN")
(assert "IntPlus p r=IntPlus r p")
 (use "IntPlusComm")
(assume "IntPlus p r=IntPlus r p")
(simp "IntPlus p r=IntPlus r p")
(use "Truth")
;; 75
(assume "i")
(use "Truth")
;; 76
(assume "q")
(cases)
;; 139-141
(assume "r")
;; ?_142:IntN p+(IntN q+r)=IntN p+IntN q+r
(simp "<-" "IntUMinusInj")
(assert "IntN p= ~p")
 (use "Truth")
(assume "IntN p= ~p")
(simp "IntN p= ~p")
(assert "IntN q= ~q")
 (use "Truth")
(assume "IntN q= ~q")
(simp "IntN q= ~q")
;; ?_151:~(~p+(~q+r))= ~(~p+ ~q+r)
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus0RewRule")
(assert "IntN r= ~r")
 (use "Truth")
(assume "IntN r= ~r")
(simp "<-" "IntN r= ~r")
(use "IntPlusAssocPPN")
;; 140
(use "Truth")
;; 141
(assume "r")
;; ?_164:IntN p+(IntN q+IntN r)=IntN p+IntN q+IntN r
(use "Truth")
;; Proof finished.
(save "IntPlusAssoc")
;; We also add IntPlusAssoc as rewrite rule
(add-rewrite-rule "k+(j+i)" "k+j+i")

;; IntPlusIdOne
(set-goal "all k k+1=IntS k")
(cases)
;; 2-4
(assume "p")
(use "Truth")
;; 3
(use "Truth")
;; 4
(cases)
;; 6-8
(use "Truth")
;; 7
(assume "p")
(use "Truth")
;; 8
(assume "p")
(use "Truth")
;; Proof finished.
(save "IntPlusIdOne")
;; (add-rewrite-rule "i+One" "IntS i")

;; IntPlusIdIntPSZero
(set-goal "all k,p k+IntP(SZero p)=k+IntP p+IntP p")
(assume "k" "p")
(simp "SZeroPosPlus")
(simp "PosPlusIntPlus")
(use "IntPlusAssoc")
;; Proof finished.
(save "IntPlusIdIntPSZero")
;; (add-rewrite-rule "k+IntP(SZero p)" "k+IntP p+IntP p")

;; IntPlusIdIntPSOne
(set-goal "all k,p k+IntP(SOne p)=IntS(k+IntP(SZero p))")
(assume "k" "p")
(simp "IntPSOne")
(simp "SZeroPosPlus")
(simp "<-" "IntPlusIdOne")
(simp "<-" "IntPlusIdOne")
(simp "PosPlusIntPlus")
(simp "IntPlusAssoc")
(use "Truth")
;; Proof finished.
(save "IntPlusIdIntPSOne")
;; (add-rewrite-rule "i+IntP(SOne p)" "IntS(i+IntP(SZero p))")

;; IntPlusIdIntNSZero
(set-goal "all k,p k+IntN(SZero p)=k+IntN p+IntN p")
(assume "k" "p")
(simp "<-" "IntUMinusInj")
(ng)
(use "IntPlusIdIntPSZero")
;; Proof finished.
(save "IntPlusIdIntNSZero")
;; (add-rewrite-rule "i+IntN(SZero p)" "i+IntN p+IntN p")

;; IntPlusIdIntNSOne
(set-goal "all k,p k+IntN(SOne p)=IntPred(k+IntN(SZero p))")
(assume "k" "p")
(simp "<-" "IntUMinusInj")
(ng)
(use "IntPlusIdIntPSOne")
(save "IntPlusIdIntNSOne")
;; (add-rewrite-rule "i+IntN(SOne p)" "IntPred(i+IntN(SZero p))")

;; IntPlusOneId
(set-goal "all k 1+k=IntS k")
(assume "k")
(simp "IntPlusComm")
(use "IntPlusIdOne")
;; Proof finished.
(save "IntPlusOneId")
;; (add-rewrite-rule "One+i" "IntS i")
 
;; IntPlusIntPSZeroId
(set-goal "all k,p IntP(SZero p)+k=k+IntP p+IntP p")
(assume "k" "p")
(simp "IntPlusComm")
(use "IntPlusIdIntPSZero")
;; Proof finished.
;; (add-rewrite-rule "IntP(SZero p)+k" "k+IntP p+IntP p")

;; IntPlusIntPSOneId
(set-goal "all k,p IntP(SOne p)+k=IntS(k+IntP(SZero p))")
(assume "k" "p")
(simp "IntPlusComm")
(use "IntPlusIdIntPSOne")
;; Proof finished.
;; (add-rewrite-rule "IntP(SOne p)+i" "IntS(i+IntP(SZero p))")

;; IntPlusIntNSZeroId
(set-goal "all k,p IntN(SZero p)+k=k+IntN p+IntN p")
(assume "k" "p")
(simp "IntPlusComm")
(use "IntPlusIdIntNSZero")
;; Proof finished.
;; (add-rewrite-rule "IntN(SZero p)+i" "i+IntN p+IntN p")

;; IntPlusIdIntNSOne
(set-goal "all k,p IntN(SOne p)+k=IntPred(k+IntN(SZero p))")
(assume "k" "p")
(simp "IntPlusComm")
(use "IntPlusIdIntNSOne")
;; Proof finished.
;; (add-rewrite-rule "IntN(SOne p)+i" "IntPred(i+IntN(SZero p))")

;; IntPlusIntSId
(set-goal "all k,j IntS k+j=IntS(k+j)")
(assume "k" "j")
(simp "<-" "IntPlusOneId")
(simp "<-" "IntPlusOneId")
(simp "IntPlusAssoc")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntS k+j" "IntS(k+j)")

;; IntPlusIdIntS
(set-goal "all k,j k+IntS j=IntS(k+j)")
(assume "k" "j")
(simp "<-" "IntPlusIdOne")
(simp "<-" "IntPlusIdOne")
(simp "IntPlusAssoc")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k+IntS j" "IntS(k+j)")

;; Rules for IntTimes

(add-computation-rules
 "IntZero*k" "IntZero"
 "IntP p*IntZero" "IntZero"
 "IntP p*IntP q" "IntP(p*q)"
 "IntP p*IntN q" "IntN(p*q)"
 "IntN p*IntZero" "IntZero"
 "IntN p*IntP q" "IntN(p*q)"
 "IntN p*IntN q" "IntP(p*q)")

;; IntTimesTotal
(set-totality-goal "IntTimes")
(use "AllTotalElim")
(cases)
;; 3-5
(assume "p")
(use "AllTotalElim")
(cases)
;; 8-10
(assume "q")
(use "IntTotalVar")
;; 9
(use "IntTotalVar")
;; 10
(assume "q")
(use "IntTotalVar")
;; 4
(use "AllTotalElim")
(assume "k")
(use "IntTotalVar")
;; 5
(assume "p")
(use "AllTotalElim")
(cases)
;; 17-19
(assume "q")
(use "IntTotalVar")
;; 18
(use "IntTotalVar")
;; 19
(assume "q")
(use "IntTotalVar")
;; Proof finished.
(save-totality)

;; Code discarded 2016-04-02
;; ;; IntTimesTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "IntTimes")
;; 	    (proof-to-formula (theorem-name-to-proof "IntTimesTotal")))))
;; (assume "k^" "k^0" "TMRk0k" "l^" "l^0" "TMRl0l")
;; (elim "TMRk0k")

;; ;; ?_3:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(pos^0*l^0)(pos^ *l^))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRl0l")

;; ;; ?_7:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0*pos^0)(p^ *pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (use "TotalIntIntPosMR")
;; (use "PosTimesTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_8:TotalIntMR(p^0*0)(p^ *0)
;; (ng #t)
;; (use "TotalIntIntZeroMR")

;; ;; ?_9:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0*IntN pos^0)(p^ *IntN pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntNegMR")
;; (use "PosTimesTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_4:TotalIntMR(0*l^0)(0*l^)
;; (ng #t)
;; (use "TotalIntIntZeroMR")

;; ;; ?_5:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(IntN pos^0*l^0)(IntN pos^ *l^))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRl0l")

;; ;; ?_22:allnc pos^,pos^0(
;; ;;       TotalPosMR pos^0 pos^ --> TotalIntMR(IntN p^0*pos^0)(IntN p^ *pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (use "TotalIntIntNegMR")
;; (use "PosTimesTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_23:TotalIntMR(IntN p^0*0)(IntN p^ *0)
;; (ng #t)
;; (use "TotalIntIntZeroMR")

;; ;; ?_24:allnc pos^,pos^0(
;; ;;       TotalPosMR pos^0 pos^ -->
;; ;;       TotalIntMR(IntN p^0*IntN pos^0)(IntN p^ *IntN pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntPosMR")
;; (use "PosTimesTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; ;; Proof finished.
;; (save "IntTimesTotalReal")

(set-goal "all k k*IntZero=IntZero")
(cases)
(assume "p")
(use "Truth")
(use "Truth")
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k*IntZero" "IntZero")

(set-goal "all k k*IntP One=k")
(cases)
;; 2-4
(assume "p")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k*IntP One" "k")

(set-goal "all k IntP One*k=k")
(cases)
;; 2-4
(assume "p")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntP One*k" "k")

;; IntTimesComm
(set-goal "all k,j k*j=j*k")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(use "PosTimesComm")
;; 7
(ng)
(use "Truth")
;; 8
(assume "q")
(ng)
(use "PosTimesComm")
;; 3
(assume "j")
(use "Truth")
;; 4
(assume "p")
(cases)
;; 16-18
(assume "q")
(ng)
(use "PosTimesComm")
;; 17
(ng)
(use "Truth")
;; 18
(assume "q")
(ng)
(use "PosTimesComm")
;; Proof finished.
(save "IntTimesComm")

;; IntTimesAssoc
(set-goal "all k,j,i k*(j*i)=k*j*i")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(cases)
;; 10-12
(assume "r")
(use "Truth")
;; 11
(use "Truth")
;; 12
(assume "r")
(use "Truth")
;; 7
(assume "int")
(use "Truth")
;; 8
(assume "q")
(cases)
;; 17-19
(assume "r")
(use "Truth")
;; 18
(use "Truth")
;; 19
(assume "r")
(use "Truth")
;; 3
(strip)
(use "Truth")
;; 4
(assume "p")
(cases)
;; 24-26
(assume "q")
(cases)
;; 28-30
(assume "r")
(use "Truth")
;; 29
(use "Truth")
;; 30
(assume "r")
(use "Truth")
;; 25
(assume "int")
(use "Truth")
;; 26
(assume "q")
(cases)
;; 35-37
(assume "r")
(use "Truth")
;; 36
(use "Truth")
;; 37
(assume "r")
(use "Truth")
;; Proof finished.
(save "IntTimesAssoc")
(add-rewrite-rule "k*(j*i)" "k*j*i")

;; We show that one IntUMinus can be moved out of a product.

;; ;; IntTimesIdUMinus
(set-goal "all k,j k* ~j= ~(k*j)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(use "Truth")
;; 7
(use "Truth")
;; 8
(assume "q")
(ng)
(use "Truth")
;; 3
(assume "k")
(use "Truth")
;; 4
(assume "p")
(cases)
;; 15-17
(assume "q")
(ng)
(use "Truth")
;; 16
(use "Truth")
;; 17
(assume "q")
(ng)
(use "Truth")
;; Proof finished.
;; (save "IntTimesIdUMinus")
(add-rewrite-rule "k* ~j" "~(k*j)")

;; IntTimesUMinusId
(set-goal "all k,j ~k*j= ~(k*j)")
(assume "k" "j")
(simp "IntTimesComm")
(ng)
(simp "IntTimesComm")
(use "Truth")
;; Proof finished.
;; (save "IntTimesUMinusId")
(add-rewrite-rule "~k*j" "~(k*j)")

;; IntTimesPlusDistr.  It suffices to prove IntTimesPlusDistrPPN:
;; p*(q+IntN r)=p*q+p*IntN r.  This requires comparison of r with q,
;; i.e., the consideration of the 3 cases r<q r=q q<r.

;; IntTimesPlusDistr
(set-goal "all k,j,i k*(j+i)=k*j+k*i")
;; IntTimesPlusDistrPPN
(assert "all p,q,r p*(q+IntN r)=p*q+p*IntN r")
(assume "p" "q" "r")
(use "PosLeLtCases" (pt "r") (pt "q"))
(assume "r<=q")
(use "PosLeCases"  (pt "r") (pt "q"))
(use "r<=q")
(drop "r<=q")
(assume "r<q")
;; Case r<q
(simp "IntPlusPNP")
(simp "IntTimes3CompRule")
(simp "IntTimes2CompRule")
(simp "IntPlusPNP")
(use "PosTimesMinusDistr")
(use "r<q")
(use "PosLeLtMonTimes")
(use "Truth")
(use "r<q")
(use "r<q")
(assume "r=q")
;; Case r=q
(simp "r=q")
(ng #t)
(use "Truth")
(assume "q<r")
;; Case q<r
(simp "IntPlusPNN")
(simp "IntTimes3CompRule")
(simp "IntTimes3CompRule")
(simp "IntPlusPNN")
(use "PosTimesMinusDistr")
(use "q<r")
(use "PosLeLtMonTimes")
(use "Truth")
(use "q<r")
(use "q<r")
;; Proof of assertion finished.
(assume "IntTimesPlusDistrPPN")
;; Now we can tackle IntTimesPlusDistr
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(cases)
;; 10-12
(assume "r")
(use "PosTimesPlusDistr" (pt "p") (pt "q") (pt "r"))
;; 11
(use "Truth")
;; 12
(assume "r")
(use "IntTimesPlusDistrPPN")
;; 7
(assume "i")
(use "Truth")
;; 8
(assume "q")
(cases)
;; 17-19
(assume "r")
(simp "IntPlusComm")
(simp "IntTimesPlusDistrPPN")
(simp "IntPlusComm")
(use "Truth")
;; 18
(use "Truth")
;; 19
(assume "r")
(ng)
(use "Truth")
;; 3
(strip)
(use "Truth")
;; 4
(assume "p")
(cases)
;; 28-30
(assume "q")
(cases)
;; 32-34
(assume "r")
(simp "IntPlus2CompRule")
(ng)
(use "Truth")
;; 33
(use "Truth")
;; 34
(assume "r")
(simp "<-" "IntUMinusInj")
(simp "<-" "IntTimes5RewRule")
(simp "IntUMinus1RewRule")
(simp "<-" "IntTimes5RewRule")
(simp "<-" "IntTimes5RewRule")
(use "IntTimesPlusDistrPPN")
;; 29
(assume "i")
(use "Truth")
;; 30
(assume "q")
(cases)
;; 51-53
(assume "r")
(simp "<-" "IntUMinusInj")
(simp "<-" "IntTimes5RewRule")
(simp "IntUMinus1RewRule")
(simp "<-" "IntTimes5RewRule")
(simp "<-" "IntTimes5RewRule")
(simp "IntPlusComm")
(simp "IntUMinus2CompRule")
(simp "IntTimesPlusDistrPPN")
(simp "IntPlusComm")
(use "Truth")
;; 52
(use "Truth")
;; 53
(assume "r")
(ng)
(use "Truth")
;; Proof finished.
(save "IntTimesPlusDistr")
(add-rewrite-rule "k*(j+i)" "k*j+k*i")

;; IntTimesPlusDistrLeft
(set-goal "all k,j,i (k+j)*i=(k*i)+(j*i)")
(assume "k" "j" "i")
(simp "IntTimesComm")
(simp "IntTimesPlusDistr")
(simp "IntTimesComm")
(assert "i*j=j*i")
 (use "IntTimesComm")
(assume "i*j=j*i")
(simp "i*j=j*i")
(use "Truth")
;; Proof finished.
(save "IntTimesPlusDistrLeft")
(add-rewrite-rule "(k+j)*i" "(k*i)+(j*i)")

;; Rules for IntAbs

(add-computation-rules
 "abs IntZero" "IntZero"
 "abs IntP p" "IntP p"
 "abs IntN p" "IntP p")

;; IntAbsTotal
(set-totality-goal "IntAbs")
(use "AllTotalElim")
(cases)
(assume "p")
(use "IntTotalVar")
(use "IntTotalVar")
(assume "p")
(use "IntTotalVar")
;; Proof finished.
(save-totality)

(set-goal "all k abs(~k)=abs k")
(cases)
(assume "p")
(use "Truth")
(use "Truth")
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "abs(~k)" "abs k")

(set-goal "all k,j abs(k*j)=abs k*abs j")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(use "Truth")
;; 7
(use "Truth")
;; 8
(assume "q")
(use "Truth")
;; 3
(assume "j")
(use "Truth")
;; 4
(assume "p")
(cases)
;; 13-15
(assume "q")
(use "Truth")
;; 14
(use "Truth")
;; 15
(assume "q")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "abs(k*j)" "abs k*abs j")

;; Rules for IntSg

(add-computation-rules
 "sg IntZero" "IntZero"
 "sg IntP p" "IntP One"
 "sg IntN p" "IntN One")

;; IntSgTotal
(set-totality-goal "IntSg")
(use "AllTotalElim")
(cases)
(assume "p")
(use "IntTotalVar")
(use "IntTotalVar")
(assume "p")
(use "IntTotalVar")
;; Proof finished.
(save-totality)

;; IntSgUMinus
(set-goal "all k sg~k= ~sg k")
(cases)
(strip)
(use "Truth")
(use "Truth")
(strip)
(use "Truth")
;; Proof finished.
(save "IntSgUMinus")

;; Rules for IntExp : int=>nat=>int

(add-computation-rules
 "k**Zero" "IntP One"
 "k**Succ n" "k**n*k")

;; IntExpTotal
(set-totality-goal "IntExp")
(use "AllTotalElim")
(assume "k")
(use "AllTotalElim")
(ind)
(use "IntTotalVar")
(assume "n" "IH")
(ng)
(use "IntTimesTotal")
(use "IH")
(use "IntTotalVar")
;; Proof finished.
(save-totality)

;; Strategy: do computations at the lowest possible level.  Raise outside.

;; We may assume that the given term is an original; otherwise use
;; term-to-original first.  If it is say a sum, take the original of
;; both components.  Let alg be the lub of their types.  If it is below
;; the type of the given term, do the addition at level alg already
;; (after embedding both components into alg via algebras-to-embedding)
;; and then embed the result into the type of the given term.

(set-goal "all p,n (IntP p)**n=IntP(p**n)")
(assume "p")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(simp "IH")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "(IntP p)**n" "IntP(p**n)")

(set-goal "all r 0**r=0")
(assume "r")
(use "PosLeLtCases" (pt "r") (pt "1"))
(ng)
(assume "r=1")
(simp "r=1")
(use "Truth")
(assume "1<r")
(simp "SuccPosPred")
(ng)
(use "Truth")
(use "1<r")
;; Proof finished.
(add-rewrite-rule "0**r" "0")

;; Rules for IntMax

(add-computation-rules
 "IntZero max IntZero" "IntZero"
 "IntZero max IntP p" "IntP p"
 "IntZero max IntN p" "IntZero"
 "IntP p max IntZero" "IntP p"
 "IntP p max IntP q" "IntP(p max q)"
 "IntP p max IntN q" "IntP p"
 "IntN p max IntZero" "IntZero"
 "IntN p max IntP q" "IntP q"
 "IntN p max IntN q" "IntN(p min q)")

;; IntMaxTotal
(set-totality-goal "IntMax")
(use "AllTotalElim")
(cases)
;; 3-5
(assume "p")
(use "AllTotalElim")
(cases)
;; 8-10
(assume "q")
(use "IntTotalVar")
;; 9
(use "IntTotalVar")
;; 10
(assume "q")
(use "IntTotalVar")
;; 4
(use "AllTotalElim")
(cases)
;; 14-16
(assume "q")
(use "IntTotalVar")
;; 15
(use "IntTotalVar")
;; 16
(assume "q")
(use "IntTotalVar")
;; 5
(assume "p")
(use "AllTotalElim")
(cases)
;; 21-23
(assume "q")
(use "IntTotalVar")
;; 22
(use "IntTotalVar")
;; 23
(assume "q")
(use "IntTotalVar")
;; Proof finished.
(save-totality)

;; Rules for IntMin

(add-computation-rules
 "IntZero min IntZero" "IntZero"
 "IntZero min IntP p" "IntZero"
 "IntZero min IntN p" "IntN p"
 "IntP p min IntZero" "IntZero"
 "IntP p min IntP q" "IntP(p min q)"
 "IntP p min IntN q" "IntN q"
 "IntN p min IntZero" "IntN p"
 "IntN p min IntP q" "IntN p"
 "IntN p min IntN q" "IntN(p max q)")

;; IntMinTotal
(set-totality-goal "IntMin")
(use "AllTotalElim")
(cases)
;; 3-5
(assume "p")
(use "AllTotalElim")
(cases)
;; 8-10
(assume "q")
(use "IntTotalVar")
;; 9
(use "IntTotalVar")
;; 10
(assume "q")
(use "IntTotalVar")
;; 4
(use "AllTotalElim")
(cases)
;; 14-16
(assume "q")
(use "IntTotalVar")
;; 15
(use "IntTotalVar")
;; 16
(assume "q")
(use "IntTotalVar")
;; 5
(assume "p")
(use "AllTotalElim")
(cases)
;; 21-23
(assume "q")
(use "IntTotalVar")
;; 22
(use "IntTotalVar")
;; 23
(assume "q")
(use "IntTotalVar")
;; Proof finished.
(save-totality)

;; Rules for IntLt

(add-computation-rules
 "IntZero<IntZero" "False"
 "IntZero<IntP p" "True"
 "IntZero<IntN p" "False"
 "IntP p<IntZero" "False"
 "IntP p<IntP q" "p<q"
 "IntP p<IntN q" "False"
 "IntN p<IntZero" "True"
 "IntN p<IntP q" "True"
 "IntN p<IntN q" "q<p")

;; IntLtTotal
(set-totality-goal "IntLt")
(use "AllTotalElim")
(cases)
;; 3-5
(assume "p")
(use "AllTotalElim")
(cases)
;; 8-10
(assume "q")
(use "BooleTotalVar")
;; 9
(use "BooleTotalVar")
;; 10
(assume "q")
(use "BooleTotalVar")
;; 4
(use "AllTotalElim")
(cases)
;; 14-16
(assume "q")
(use "BooleTotalVar")
;; 15
(use "BooleTotalVar")
;; 16
(assume "q")
(use "BooleTotalVar")
;; 5
(assume "p")
(use "AllTotalElim")
(cases)
;; 21-23
(assume "q")
(use "BooleTotalVar")
;; 22
(use "BooleTotalVar")
;; 23
(assume "q")
(use "BooleTotalVar")
;; Proof finished.
(save-totality)

;; IntTimesCancelL
(set-goal "all k,j,i(0<abs k -> k*j=k*i -> j=i)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(cases)
;; 10-12
(assume "r" "Useless")
(ng)
(use "PosTimesCancelL")
;; 11
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 12
(assume "r")
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 7
(cases)
(ng)
(assume "r" "Useless" "Absurd")
(use "Absurd")
;; 21
(ng)
(strip)
(use "Truth")
;; 22
(ng)
(assume "q" "Useless" "Absurd")
(use "Absurd")
;; 8
(assume "q")
(cases)
;; 30-32
(ng)
(assume "r" "Useless" "Absurd")
(use "Absurd")
;; 31
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 32
(assume "r" "Useless")
(ng)
(use "PosTimesCancelL")
;; 3
(assume "j" "i" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 4
(ng)
(assume "p")
(cases)
;; 44-46
(assume "q")
(cases)
;; 48-50
(assume "r" "Useless")
(ng)
(use "PosTimesCancelL")
;; 49
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 50
(assume "r" "Useless")
(ng)
(assume "Absurd")
(use "Absurd")
;; 45
(cases)
;; 58-60
(ng)
(assume "r" "Useless" "Absurd")
(use "Absurd")
;; 59
(strip)
(use "Truth")
;; 60
(ng)
(assume "r" "Useless" "Absurd")
(use "Absurd")
;; 46
(assume "q")
(cases)
;; 67-69
(ng)
(assume "r" "Useless" "Absurd")
(use "Absurd")
;; 68
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 69
(ng)
(assume "r" "Useless")
(use "PosTimesCancelL")
;; Proof finished.
(save "IntTimesCancelL")

;; IntTimesCancelR
(set-goal "all k,j,i(0<abs i -> k*i=j*i -> k=j)")
(assume "k" "j" "i" "PosHyp" "ki=ji")
(use "IntTimesCancelL" (pt "i"))
(use "PosHyp")
(simp "IntTimesComm")
(simp "ki=ji")
(use "IntTimesComm")
;; Proof finished.
(save "IntTimesCancelR")

;; Rules for IntLe

(add-computation-rules
 "IntZero<=IntZero" "True"
 "IntZero<=IntP p" "True"
 "IntZero<=IntN p" "False"
 "IntP p<=IntZero" "False"
 "IntP p<=IntP q" "p<=q"
 "IntP p<=IntN q" "False"
 "IntN p<=IntZero" "True"
 "IntN p<=IntP q" "True"
 "IntN p<=IntN q" "q<=p")

;; IntLeTotal
(set-totality-goal "IntLe")
(use "AllTotalElim")
(cases)
;; 3-5
(assume "p")
(use "AllTotalElim")
(cases)
;; 8-10
(assume "q")
(use "BooleTotalVar")
;; 9
(use "BooleTotalVar")
;; 10
(assume "q")
(use "BooleTotalVar")
;; 4
(use "AllTotalElim")
(cases)
;; 14-16
(assume "q")
(use "BooleTotalVar")
;; 15
(use "BooleTotalVar")
;; 16
(assume "q")
(use "BooleTotalVar")
;; 5
(assume "p")
(use "AllTotalElim")
(cases)
;; 21-23
(assume "q")
(use "BooleTotalVar")
;; 22
(use "BooleTotalVar")
;; 23
(assume "q")
(use "BooleTotalVar")
;; Proof finished.
(save-totality)

;; IntLtToLe
(set-goal "all k,j(k<j -> k<=j)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(use "PosLtToLe")
;; 7
(ng)
(assume "Absurd")
(use "Absurd")
;; 8
(assume "q")
(ng)
(assume "Absurd")
(use "Absurd")
;; 3
(cases)
(assume "q")
(ng)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "q")
(ng)
(assume "Absurd")
(use "Absurd")
;; 4
(assume "p")
(cases)
(assume "q")
(ng)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
(assume "q")
(ng)
(use "PosLtToLe")
;; Proof finished.
(save "IntLtToLe")

(set-goal "all k (k<k)=False")
(cases)
;; 2-4
(assume "pos")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "pos")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k<k" "False")

(set-goal "all k,p k<k+p")
(cases)
;; 2-4
(assume "p" "q")
(use "Truth")
;; 3
(assume "p")
(use "Truth")
;; 4
(assume "p" "q")
(ng)
(cases (pt "p=q"))
(assume "p=q")
(ng)
(use "Truth")
(assume "p=q->F")
(ng)
(cases (pt "p<q"))
(assume "p<q")
(ng)
(use "Truth")
(assume "p<q->F")
(ng)
(assert "q<p")
 (use "PosNotLeToLt")
 (assume "p1<=p2") 
 (use "PosLeCases" (pt "p") (pt "q"))
 (use "p1<=p2")
 (use "p<q->F")
 (use "p=q->F")
(assume "q<p")
(inst-with-to "PosMinusPlusEq" (pt "p") (pt "q") "q<p"
	      "PosMinusPlusEqInst")
(simp "<-" "PosMinusPlusEqInst")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k<k+p" "True")

(set-goal "all k k<IntS k")
(assume "k")
(simp "<-" "IntPlusIdOne")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k<IntS k" "True") 

(set-goal "all k k<=k")
(cases)
;; 2-4
(assume "pos")
(use "Truth")
;; 3
(use "Truth")
(assume "pos")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k<=k" "True")

(set-goal "all k,p k<=k+p")
(assume "k" "p")
(use "IntLtToLe")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k<=k+p" "True")

(set-goal "all k k<=IntS k")
(assume "k")
(simp "<-" "IntPlusIdOne")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k<=IntS k" "True")

(set-goal "all p IntS IntN p<1")
(cases)
;; 2-4
(use "Truth")
;; 3
(assume "p")
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntS IntN p<1" "True")

(set-goal "all p IntS IntN p<=0")
(cases)
;; 2-4
(use "Truth")
;; 3
(assume "p")
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntS IntN p<=0" "True")

(set-goal "all p (0<IntS IntN p)=False")
(cases)
;; 2-4
(use "Truth")
;; 3
(assume "p")
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "0<IntS IntN p" "False")

(set-goal "all p (1<=IntS IntN p)=False")
(cases)
;; 2-4
(use "Truth")
;; 3
(assume "p")
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "1<=IntS IntN p" "False")

;; IntLtTrans
(set-goal "all k,j,i(k<j -> j<i -> k<i)")
(cases)
;; 2-4
(assume "p")
(cases)
(assume "q")
(cases)
(assume "r")
(use "PosLtTrans")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "r" "Useless" "Absurd")
(use "Absurd")
;; 7
(assume "int" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 8
(assume "q" "i" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 3
(cases)
(assume "q")
(cases)
(strip)
(use "Truth")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "r" "Useless" "Absurd")
(use "Absurd")
(assume "int" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "q" "int" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 4
(assume "p")
(cases)
(assume "q")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "q")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r")
(ng)
(assume "q<p" "r<q")
(use "PosLtTrans" (pt "q"))
(use "r<q")
(use "q<p")
;; Proof finished.
;; (cdp)
(save "IntLtTrans")

;; The following theorems can be proved similarly from the
;; corresponding ones for pos.

;; IntLeTrans
(set-goal "all k,j,i(k<=j -> j<=i -> k<=i)")
(cases)
;; 2-4
(assume "p")
(cases)
(assume "q")
(cases)
(assume "r")
(use "PosLeTrans")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "r" "Useless" "Absurd")
(use "Absurd")
;; 7
(assume "int" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 8
(assume "q" "i" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 3
(cases)
(assume "q")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r" "Useless" "Absurd")
(use "Absurd")
(assume "int" "Useless" "0<=int")
(use "0<=int")
(assume "q" "int" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 4
(assume "p")
(cases)
(assume "q")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "q")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r")
(ng)
(assume "q<=p" "r<=q")
(use "PosLeTrans" (pt "q"))
(use "r<=q")
(use "q<=p")
;; Proof finished.
;; (cdp)
(save "IntLeTrans")

;; IntLeLtTrans
(set-goal "all k,j,i(k<=j -> j<i -> k<i)")
(cases)
;; 2-4
(assume "p")
(cases)
(assume "q")
(cases)
(assume "r")
(use "PosLeLtTrans")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "r" "Useless" "Absurd")
(use "Absurd")
;; 7
(assume "int" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 8
(assume "q" "i" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 3
(cases)
(assume "q")
(cases)
(strip)
(use "Truth")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "r" "Useless" "Absurd")
(use "Absurd")
(assume "int" "Useless" "0<int")
(use "0<int")
(assume "q" "int" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 4
(assume "p")
(cases)
(assume "q")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "q")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r")
(ng)
(assume "q<=p" "r<q")
(use "PosLtLeTrans" (pt "q"))
(use "r<q")
(use "q<=p")
;; Proof finished.
;; (cdp)
(save "IntLeLtTrans")

;; IntLtLeTrans
(set-goal "all k,j,i(k<j -> j<=i -> k<i)")
(cases)
;; 2-4
(assume "p")
(cases)
(assume "q")
(cases)
(assume "r")
(use "PosLtLeTrans")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "r" "Useless" "Absurd")
(use "Absurd")
;; 7
(assume "int" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 8
(assume "q" "i" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 3
(cases)
(assume "q")
(cases)
(strip)
(use "Truth")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "r" "Useless" "Absurd")
(use "Absurd")
(assume "int" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "q" "int" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 4
(assume "p")
(cases)
(assume "q")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "q")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r")
(ng)
(assume "q<p" "r<=q")
(use "PosLeLtTrans" (pt "q"))
(use "r<=q")
(use "q<p")
;; Proof finished.
;; (cdp)
(save "IntLtLeTrans")

;; IntNotLeToLt
(set-goal "all k,j((k<=j -> F) -> j<k)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "pos")
(ng)
(use "PosNotLeToLt")
;; 7
(strip)
(use "Truth")
;; 8
(strip)
(use "Truth")
;; 3
(cases)
(assume "q" "Absurd")
(use "Absurd")
(use "Truth")
(assume "Absurd")
(use "Absurd")
(use "Truth")
(strip)
(use "Truth")
;; 4
(assume "p")
(cases)
;; 22-24
(assume "q" "Absurd")
(use "Absurd")
(use "Truth")
;; 23
(assume "Absurd")
(use "Absurd")
(use "Truth")
;; 24
(assume "q")
(ng)
(use "PosNotLeToLt")
;; Proof finished.
(save "IntNotLeToLt")

;; IntNotLtToLe
(set-goal "all k,j((k<j -> F) -> j<=k)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "pos")
(ng)
(use "PosNotLtToLe")
;; 7
(strip)
(use "Truth")
;; 8
(strip)
(use "Truth")
;; 3
(cases)
(assume "q" "Absurd")
(use "Absurd")
(use "Truth")
(assume "Useless")
(use "Truth")
(assume "q" "Useless")
(use "Truth")
;; 4
(assume "p")
(cases)
;; 21-23
(assume "q" "Absurd")
(use "Absurd")
(use "Truth")
;; 22
(assume "Absurd")
(use "Absurd")
(use "Truth")
;; 23
(assume "q")
(ng)
(use "PosNotLtToLe")
;; Proof finished.
(save "IntNotLtToLe")

;; IntLeAntiSym
(set-goal "all k,j(k<=j -> j<=k -> k=j)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(use "PosLeAntiSym")
;; 7
(ng)
(assume "Absurd" "Useless")
(use "Absurd")
;; 8
(assume "q")
(ng)
(assume "Absurd" "Useless")
(use "Absurd")
;; 3
(cases)
;; 15-17
(assume "q")
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 16
(strip)
(use "Truth")
;; 17
(assume "q")
(ng)
(assume "Absurd" "Useless")
(use "Absurd")
;; 4
(assume "p")
(cases)
;; 26-28
(assume "q")
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 27
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 28
(assume "q" "q<=p" "p1<=p2")
(use "PosLeAntiSym")
(use "p1<=p2")
(use "q<=p")
;; Proof finished.
(save "IntLeAntiSym")

;; Next relations of IntLt, IntLe with IntUMinus

;; IntLtUMinus
(set-goal "all k,j (~j< ~k)=(k<j)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(use "Truth")
;; 7
(ng)
(use "Truth")
;; 8
(assume "q")
(ng)
(use "Truth")
;; 3
(cases)
;; 14-16
(assume "p")
(ng)
(use "Truth")
;; 15
(ng)
(use "Truth")
;; 16
(assume "q")
(ng)
(use "Truth")
;; 4
(assume "p")
(cases)
;; 23025
(assume "q")
(ng)
(use "Truth")
;; 24
(ng)
(use "Truth")
;; 25
(assume "q")
(ng)
(use "Truth")
;; Proof finished.
(save "IntLtUMinus")
(add-rewrite-rule "~j< ~k" "k<j")

;; IntLeUMinus
(set-goal "all k,j (~j<= ~k)=(k<=j)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(use "Truth")
;; 7
(ng)
(use "Truth")
;; 8
(assume "q")
(ng)
(use "Truth")
;; 3
(cases)
;; 14-16
(assume "p")
(ng)
(use "Truth")
;; 15
(ng)
(use "Truth")
;; 16
(assume "q")
(ng)
(use "Truth")
;; 4
(assume "p")
(cases)
;; 23-25
(assume "q")
(ng)
(use "Truth")
;; 24
(ng)
(use "Truth")
;; 31
(assume "q")
(ng)
(use "Truth")
;; Proof finished.
(save "IntLeUMinus")
(add-rewrite-rule "~j<= ~k" "k<=j")

;; IntLtMonPredIntP
(set-goal "all p,q(p<q -> IntPred p<IntPred q)")
(assume "p" "q" "p<q")
(use "PosLeCases" (pt "One") (pt "p"))
(use "Truth")
(assume "1<p")
(assert "1<q")
(use "PosLtTrans" (pt "p"))
(use "1<p")
(use "p<q")
(assume "1<q")
(assert "PosS(PosPred p)=p")
 (use "PosSPosPredId")
 (use "1<p")
(assume "PosS(PosPred p)=p")
(simp "<-" "PosS(PosPred p)=p")
(drop "PosS(PosPred p)=p")
(assert "PosS(PosPred q)=q")
 (use "PosSPosPredId")
 (use "1<q")
(assume "PosS(PosPred q)=q")
(simp "<-" "PosS(PosPred q)=q")
(drop "PosS(PosPred q)=q")
(ng)
(use "PosLtMonPred")
(use "1<p")
(use "p<q")
;; 5
(assume "1=p")
(assert "1<q")
 (simp "1=p")
 (use "p<q")
(assume "1<q")
(simp "<-" "1=p")
(ng)
(assert "PosS(PosPred q)=q")
 (use "PosSPosPredId")
 (use "1<q")
(assume "PosS(PosPred q)=q")
(simp "<-" "PosS(PosPred q)=q")
(drop "PosS(PosPred q)=q")
(ng)
(use "Truth")
;; Proof finished.
(save "IntLtMonPredIntP")

;; IntLtMonIntS
(set-goal "all k,j(k<j -> IntS k<IntS j)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(assume "p<q")
(use "p<q")
;; 7
(ng)
(assume "Absurd")
(use "Absurd")
;; 8
(assume "q" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(cases)
(assume "q")
(ng)
(strip)
(use "Truth")
;; 17
(ng)
(assume "Absurd")
(use "Absurd")
;; 18
(assume "q" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 4
(assume "p")
(cases)
;; 27-29
(assume "q" "Useless")
(ng)
;; ?_31:IntS IntN p<PosS q
(use "IntLtLeTrans" (pt "IntP 1"))
(use "Truth")
(use "Truth")
;; 28
(ng)
(strip)
(use "Truth")
;; 29
(assume "q")
;; ?_36:IntN p<IntN q -> IntS IntN p<IntS IntN q
(ng)
;; ?_37:q<p -> IntS IntN p<IntS IntN q
(simp "<-" "IntUMinus1CompRule")
(simp "<-" "IntUMinus1CompRule")
(simp "<-" "IntUMinus3RewRule")
(simp "<-" "IntUMinus3RewRule")
(simp "IntLtUMinus")
;; ?_42:q<p -> IntPred q<IntPred p
(use "IntLtMonPredIntP")
;; Proof finished.
(save "IntLtMonIntS")

;; IntLtMonIntPred
(set-goal "all k,j(k<j -> IntPred k<IntPred j)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(use "IntLtMonPredIntP")
;; 7
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 8
(assume "q" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(cases)
; 15-17
(assume "q" "Useless")
(simp "<-" "IntLtUMinus")
(ng)
(use "Truth")
;; 16
(assume "Absurd")
(use "Absurd")
;; 17
(assume "q" "Absurd")
(use "Absurd")
;; 4
(assume "p")
(cases)
;; 24-25
(assume "q" "Useless")
(simp "<-" "IntLtUMinus")
(ng)
(use "IntLtTrans" (pt "IntP 1"))
(use "Truth")
(use "Truth")
;; 25
(ng)
(strip)
(use "Truth")
;; 26
(assume "q")
(ng)
(assume "q<p")
(use "q<p")
;; Proof finished.
(save "IntLtMonIntPred")

;; We turn these into rewrite rules for IntLt
(set-goal "all k,j (IntS k<IntS j)=(k<j)")
(assume "k" "j")
(use "BooleAeqToEq")
;; 3,4
(assume "IntS k<IntS j")
(simp "<-" (pf "IntPred(IntS k)=k"))
(simp "<-" (pf "IntPred(IntS j)=j"))
(use "IntLtMonIntPred")
(use "IntS k<IntS j")
(use "Truth")
(use "Truth")
;; 4
(use "IntLtMonIntS")
;; Proof finished.
(add-rewrite-rule "IntS k<IntS j" "k<j")

(set-goal "all k,j (IntPred k<IntPred j)=(k<j)")
(assume "k" "j")
(use "BooleAeqToEq")
;; 3,4
(assume "IntPred k<IntPred j")
(simp "<-" (pf "IntS(IntPred k)=k"))
(simp "<-" (pf "IntS(IntPred j)=j"))
(use "IntLtMonIntS")
(use "IntPred k<IntPred j")
(use "Truth")
(use "Truth")
;; 4
(use "IntLtMonIntPred")
;; Proof finished.
(add-rewrite-rule "IntPred k<IntPred j" "k<j")

;; Using IntNotLtToLe and IntNotLeToLt we obtain similar rules for IntLe
(set-goal "all k,j (IntS k<=IntS j)=(k<=j)")
(assume "k" "j")
(use "BooleAeqToEq")
;; 3,4
(assume "IntS k<=IntS j")
(use "IntNotLtToLe")
(assume "j<k")
(assert "IntS k<IntS k")
(use "IntLeLtTrans" (pt "IntS j"))
(use "IntS k<=IntS j")
(use "j<k")
(assume "Absurd")
(use "Absurd")
;; 4
(assume "k<=j")
(use "IntNotLtToLe")
(assume "IntS j<IntS k")
(assert "k<k")
(use "IntLeLtTrans" (pt "j"))
(use "k<=j")
(use "IntS j<IntS k")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
(add-rewrite-rule "IntS k<=IntS j" "k<=j")

(set-goal "all k,j (IntPred k<=IntPred j)=(k<=j)")
(assume "k" "j")
(use "BooleAeqToEq")
;; 3,4
(assume "IntPred k<=IntPred j")
(use "IntNotLtToLe")
(assume "j<k")
(assert "IntPred k<IntPred k")
(use "IntLeLtTrans" (pt "IntPred j"))
(use "IntPred k<=IntPred j")
(use "j<k")
(assume "Absurd")
(use "Absurd")
;; 4
(assume "k<=j")
(use "IntNotLtToLe")
(assume "IntPred j<IntPred k")
(assert "k<k")
(use "IntLeLtTrans" (pt "j"))
(use "k<=j")
(use "IntPred j<IntPred k")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
(add-rewrite-rule "IntPred k<=IntPred j" "k<=j")

;; IntLeTimesIntPCancelR
(set-goal "all k,j,p (k*p<=j*p)=(k<=j)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q" "r")
(use "Truth")
;; 7
(assume "q")
(use "Truth")
;; 8
(assume "q" "r")
(use "Truth")
;; 3
(cases)
;; 12-14
(strip)
(use "Truth")
;; 13
(strip)
(use "Truth")
;; 14
(strip)
(use "Truth")
;; 4
(assume "p")
(cases)
;; 19-21
(strip)
(use "Truth")
;; 20
(strip)
(use "Truth")
;; 21
(strip)
(use "Truth")
;; Proof finished
(add-rewrite-rule "k*p<=j*p" "k<=j")

;; IntLeTimesIntPCancelL
(set-goal "all p,k,j (p*k<=p*j)=(k<=j)")
(assume "p" "k" "j")
(simp "IntTimesComm")
(simp (pf "p*j=j*p"))
(use "Truth")
(use "IntTimesComm")
;; Proof finished
(add-rewrite-rule "p*k<=p*j" "k<=j")

;; Same for IntLt, using IntNotLeToLt

;; IntLtTimesIntPCancelR
(set-goal "all k,j,p (k*p<j*p)=(k<j)")
(assume "k" "j" "p")
(use "BooleAeqToEq")
;; 3,4
(assume "kp<jp")
(use "IntNotLeToLt")
(assume "j<=k")
(assert "j*p<=k*p")
 (use "j<=k")
(use-with "IntLtLeTrans" (pt "k*p") (pt "j*p") (pt "k*p") "kp<jp")
;; 4
(assume "k<j")
(use "IntNotLeToLt")
(assume "jp<=kp")
(assert "j<=k")
 (use "jp<=kp")
(use-with "IntLtLeTrans" (pt "k") (pt "j") (pt "k") "k<j")
;; Proof finished.
(add-rewrite-rule "k*p<j*p" "k<j")

;; IntLtTimesIntPCancelL
(set-goal "all p,k,j (p*k<p*j)=(k<j)")
(assume "p" "k" "j")
(simp "IntTimesComm")
(simp (pf "p*j=j*p"))
(use "Truth")
(use "IntTimesComm")
;; Proof finished.
(add-rewrite-rule "p*k<p*j" "k<j")

;; IntTimesIntNL (supersedes IntIntNOneTimes)
(set-goal "all p,k IntN p*k= ~(p*k)")
(assume "p")
(cases)
(assume "q")
(use "Truth")
(use "Truth")
(assume "q")
(use "Truth")
;; Proof finished.
(save "IntTimesIntNL")

;; IntTimesIntNR
(set-goal "all k,p k*IntN p= ~(k*p)")
(assume "k" "p")
(simp "IntTimesComm")
(simp (pf "k*p=p*k"))
(use "IntTimesIntNL")
(use "IntTimesComm")
;; Proof finished.
(save "IntTimesIntNR")

;; IntLeTimesIntNCancelL
(set-goal "all p,k,j (IntN p*k<=IntN p*j)=(j<=k)")
(assume "p" "k" "j")
(simp "IntTimesIntNL")
(simp "IntTimesIntNL")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntN p*k<=IntN p*j" "j<=k")

;; IntLeTimesIntNCancelR
(set-goal "all p,k,j (k*IntN p<=j*IntN p)=(j<=k)")
(assume "p" "k" "j")
(simp "IntTimesIntNR")
(simp "IntTimesIntNR")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k*IntN p<=j*IntN p" "j<=k")

;; IntLtTimesIntNCancelL
(set-goal "all p,k,j (IntN p*k<IntN p*j)=(j<k)")
(assume "p" "k" "j")
(use "BooleAeqToEq")
;; 3,4
(assume "-pk<-jp")
(use "IntNotLeToLt")
(assume "k<=j")
(assert "IntN p*j<=IntN p*k")
 (use "k<=j")
(assume "-pj<=~pk")
(use-with "IntLtLeTrans" (pt "IntN p*k") (pt "IntN p*j") (pt "IntN p*k")
	  "-pk<-jp" "-pj<=~pk")
;; 4
(assume "j<k")
(use "IntNotLeToLt")
(assume "-pj<=-pk")
(assert "k<=j")
 (use "-pj<=-pk")
(use-with "IntLtLeTrans" (pt "j") (pt "k") (pt "j") "j<k")
;; Proof finished.
(add-rewrite-rule "IntN p*k<IntN p*j" "j<k")

;; IntLtTimesIntNCancelR
(set-goal "all p,k,j (k*IntN p<j*IntN p)=(j<k)")
(assume "p" "k" "j")
(simp "IntTimesComm")
(simp (pf "j*IntN p=IntN p*j"))
(use "Truth")
(use "IntTimesComm")
;; Proof finished.
(add-rewrite-rule "k*IntN p<j*IntN p" "j<k")

;; IntLeTimesCancelL
(set-goal "all k,j,i(IntZero<k -> k*j<=k*i -> j<=i)")
(assert "all j,i,k(IntZero<k -> k*j<=k*i -> j<=i)")
(assume "j" "i")
(cases)
;; 5-7
(assume "p" "Useless" "pj<=pi")
(use "pj<=pi")
;; 6
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 7
(assume "p" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; Assertion proved.
(assume "Assertion" "k" "j" "i")
(use "Assertion")
;; Proof finished.
;; (cdp)
(save "IntLeTimesCancelL")

;; IntLeTimesCancelR
(set-goal "all k,j,i(IntZero<j -> k*j<=i*j -> k<=i)")
(assume "k" "j" "i")
(simp "IntTimesComm")
(simp (pf "i*j=j*i"))
(use "IntLeTimesCancelL")
(use "IntTimesComm")
;; Proof finished.
(save "IntLeTimesCancelR")

;; IntLtTimesCancelL
(set-goal "all k,j,i(IntZero<k -> k*j<k*i -> j<i)")
(assert "all j,i,k(IntZero<k -> k*j<k*i -> j<i)")
(assume "j" "i")
(cases)
;; 5-7
(assume "p" "Useless" "pj<pi")
(use "pj<pi")
;; 6
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 7
(assume "p" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; Assertion proved.
(assume "Assertion" "k" "j" "i")
(use "Assertion")
;; Proof finished.
(save "IntLtTimesCancelL")

;; IntLtTimesCancelR
(set-goal "all k,j,i(IntZero<j -> k*j<i*j -> k<i)")
(assume "k" "j" "i")
(simp "IntTimesComm")
(simp (pf "i*j=j*i"))
(use "IntLtTimesCancelL")
(use "IntTimesComm")
;; Proof finished.
(save "IntLtTimesCancelR")

;; IntLeLtCases
(set-goal "all k,j((k<=j -> Pvar) -> (j<k -> Pvar) -> Pvar)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(use "PosLeLtCases")
;; 7
(assume "Useless" "Hyp")
(use-with "Hyp" "Truth")
;; 8
(assume "q")
(ng)
(assume "Useless" "Hyp")
(use-with "Hyp" "Truth")
;; 3
(cases)
;; 15-17
(assume "p" "Hyp" "Useless")
(use-with "Hyp" "Truth")
;; 16
(assume "Hyp" "Useless")
(use-with "Hyp" "Truth")
;; 17
(assume "q")
(ng)
(assume "Useless" "Hyp")
(use-with "Hyp" "Truth")
; 4
(assume "p")
(cases)
;; 24-26
(assume "q")
(ng)
(assume "Hyp" "Useless")
(use-with "Hyp" "Truth")
;; 25
(ng)
(assume "Hyp" "Useless")
(use-with "Hyp" "Truth")
;; 26
(assume "q")
(ng)
(use "PosLeLtCases")
;; Proof finished.
(save "IntLeLtCases")

;; IntLeCases
(set-goal "all k,j(k<=j -> (k<j -> Pvar) -> (k=j -> Pvar) -> Pvar)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(use "PosLeCases")
;; 7
(assume "Absurd" "Useless" "Hyp")
(use-with "Hyp" "Absurd")
;; 8
(assume "q")
(ng)
(assume "Absurd" "Useless" "Hyp")
(use-with "Hyp" "Absurd")
;; 3
(cases)
;; 15-17
(assume "p" "Useless1" "Hyp" "Useless2")
(use-with "Hyp" "Truth")
;; 16
(assume "Useless1" "Useless2" "Hyp")
(use-with "Hyp" "Truth")
;; 17
(assume "q")
(ng)
(assume "Absurd" "Useless" "Hyp")
(use-with "Hyp" "Absurd")
; 4
(assume "p")
(cases)
;; 24-26
(assume "q")
(ng)
(assume "Useless1" "Hyp" "Useless2")
(use-with "Hyp" "Truth")
;; 25
(ng)
(assume "Useless1" "Hyp" "Useless2")
(use-with "Hyp" "Truth")
;; 26
(assume "q")
(ng)
(assume "q<=p" "<Hyp" "=Hyp")
(use "PosLeCases" (pt "q") (pt "p"))
(use "q<=p")
(use "<Hyp")
(assume "q=p")
(use "=Hyp")
(simp "q=p")
(use "Truth")
;; Proof finished.
(save "IntLeCases")

;; IntLeMonTimes
(set-goal "all k,j,i(0<=k -> j<=i -> j*k<=i*k)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(cases)
;; 10-12
(assume "r" "Useless" "p2<=p3")
(ng)
(use "p2<=p3")
;; 11
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 12
(assume "r" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 7
(cases)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
(assume "r" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 8
(assume "q")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r" "Useless")
(ng)
(assume "r<=q")
(use "r<=q")
;; 3
(strip)
(use "Truth")
;; 4
(assume "p" "j" "i" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "IntLeMonTimes")

;; (search-about "IntS" "Mon")
;; For IntLeMonPlus : k<=j -> i<=int4 -> k+i<=j+int4
;; it suffices to prove k<=j -> k+i<=j+i

;; Plan for not saving some theorems immediate from IntLeMonPlus:
;; IntLtPlusIntN int+IntN pos<int  
;; IntLePlusIntN int+IntN pos<=int uses IntLtPlusIntN

;; IntLtPlusIntP int<int+pos  uses IntLtPlusIntN
;; IntLePlusIntP int<=int+pos  uses IntLePlusIntN

;; IntLeMonPlusIntN r<=q -> k+IntN q<=k+IntN r
;; IntLeMonPlusIntP q<=r -> k+q<=k+r uses IntLeMonPlusIntN

;; IntLeMonPlusAux j<=i -> k+j<=k+i uses
;;   IntLePlusIntN IntLeMonPlusIntN IntLeMonPlusIntP IntLePlusIntP

;; IntLeMonPlus k<=j -> i<=int4 -> k+i<=j+int4
;; uses IntLeMonPlusAux

;; IntLeMonPlus
(set-goal "all k,j,i,i0(k<=j -> i<=i0 -> k+i<=j+i0)")

;; We will need (in this order) theorems we do not want to save:
;; IntLtPlusIntN
;; IntLePlusIntN
;; IntLePlusIntP
;; IntLeMonPlusIntN
;; IntLeMonPlusIntP 
;; IntLeMonPlusAux

;; IntLtPlusIntN
(assert "all k,p k+IntN p<k")
(cases)
;; 2-4
(assume "p" "q")
(ng)
(cases (pt "p=q"))
(assume "p=q")
(ng)
(use "Truth")
(assume "p=q->F")
(ng)
(cases (pt "p<q"))
(assume "p<q")
(ng)
(use "Truth")
(assume "p<q->F")
(ng)
(assert "q<p")
 (use "PosNotLeToLt")
 (assume "p<=q") 
 (use "PosLeCases" (pt "p") (pt "q"))
 (use "p<=q")
 (use "p<q->F")
 (use "p=q->F")
(assume "q<p")
(inst-with-to "PosMinusPlusEq" (pt "p") (pt "q") "q<p"
	      "PosMinusPlusEqInst")
(simp "<-" "PosMinusPlusEqInst")
(ng)
(use "Truth")
;; 3
(ng)
(strip)
(use "Truth")
;; 4
(ng)
(strip)
(use "Truth")
;; Subproof finished.
(assume  "IntLtPlusIntN")

;; IntLePlusIntN
(assert "all k,p k+IntN p<=k")
(assume "k" "p")
(use "IntLtToLe")
(use "IntLtPlusIntN")
;; Subproof finished.
(assume "IntLePlusIntN")

;; IntLtPlusIntP
(assert "all k,p k<k+p")
(assume "k" "p")
(simp "<-" "IntLtUMinus")
(ng)
(use "IntLtPlusIntN")
;; Subproof finished.
(assume "IntLtPlusIntP")

;; IntLePlusIntP
(assert "all k,p k<=k+p")
(assume "k" "p")
(simp "<-" "IntLeUMinus")
(ng)
(use "IntLePlusIntN")
;; Subproof finished.
(assume "IntLePlusIntP")

;; IntLeMonPlusIntN
(assert "all k,q,r(r<=q -> k+IntN q<=k+IntN r)")
(cases)
;; 2-4
(assume "p" "q" "r" "r<=q")
(ng)
(cases (pt "p=q"))
(assume "p=q")
(ng)
(simp "p=q")
(cases (pt "q=r"))
(strip)
(ng)
(use "Truth")
(assume "q=r -> F")
(ng)
(assert "q<r -> F")
 (assume "q<r")
 (assert "q<q")
  (use "PosLtLeTrans" (pt "r"))
  (use "q<r")
  (use "r<=q")
 (assume "q<q")
 (use "q<q")
(assume "q<r -> F")
(simp "q<r -> F")
(use "Truth")
;; 8
(assume "p=q -> F")
(ng)
(cases (pt "p<q"))
;; 30,31
(assume "p<q")
(ng)
(cases (pt "p=r"))
(assume "p=r")
(ng)
(use "Truth")
(assume "p=r -> F")
(ng)
(cases (pt "p<r"))
(assume "p<r")
(ng)
(use "PosLeCases" (pt "r") (pt "q"))
(use "r<=q")
(assume "r<q")
(use "PosLtToLe")
(use "PosLtMonMinusLeft")
(use "r<q")
(use "p<r")
(assume "r=q")
(simp "r=q")
(use "Truth")
;; 41
(assume "p<r -> F")
(ng)
(use "Truth")
;; 31
(assume "p<q -> F")
(ng)
(assert "p=r -> F")
 (assume "p=r")
 (use "PosLeCases" (pt "q") (pt "p"))
 (use "PosNotLtToLe")
 (use "p<q -> F")
 (assume "q<p")
 (assert "r<r")
  (use "PosLeLtTrans" (pt "q"))
  (use "r<=q")
  (simp "<-" "p=r")
  (use "q<p")
 (assume "r<r")
 (use "r<r")
 (assume "q=p")
 (use "p=q -> F")
 (simp "q=p")
 (use "Truth")
(assume "p=r -> F")
(simp "p=r -> F")
(ng)
(assert "p<r -> F")
 (assume "p<r")
 (use "p<q -> F")
 (use "PosLtLeTrans" (pt "r"))
 (use "p<r")
 (use "r<=q")
(assume "p<r -> F")
(simp "p<r -> F")
(ng)
(assert "NatToPos(PosToNat(p--q))<=NatToPos(PosToNat(p--r))") 
 (simp "NatToPosLe")
 (simp "PosToNatMinus")
 (simp "PosToNatMinus")
 (use "NatLeMonMinus")
 (use "Truth")
 (simp "PosToNatLe")
 (use "r<=q")

 (use "PosLeCases" (pt "r") (pt "p"))
 (use "PosNotLtToLe")
 (use "p<r -> F")
 (assume "r<p")
 (use "r<p")
 (assume "r=p")
 (simp "r=p")
 (use "p=r -> F")
 (simp "r=p")
 (use "Truth")
 
 (use "PosLeCases" (pt "q") (pt "p"))
 (use "PosNotLtToLe")
 (use "p<q -> F")
 (assume "q<p")
 (use "q<p")
 (assume "q=p")
 (simp "q=p")
 (use "p=q -> F")
 (simp "q=p")
 (use "Truth")

 (use "NatLt0Pos")
 (use "NatLt0Pos")
;; Assertion proved.
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(assume "Hyp")
(use "Hyp")
;; 3
(ng)
(assume "q" "r" "r<=q")
(use "r<=q")
;; 4
(ng)
(assume "p" "q" "r" "r<=q")
;; (use "PosLeMonPlus")
;; (use "Truth")
(use "r<=q")
;; Subproof finished.
(assume "IntLeMonPlusIntN")

;; IntLeMonPlusIntP
(assert "all k,q,r(q<=r -> k+q<=k+r)")
(assume "k" "q" "r" "q<=r")
(simp "<-" "IntLeUMinus")
(ng)
(use "IntLeMonPlusIntN")
(use "q<=r")
;; Subproof finished
(assume "IntLeMonPlusIntP")

;; IntLeMonPlusAux
(assert "all k,j,i(j<=i -> k+j<=k+i)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(cases)
;; 10-12
(assume "r" "q<=r")
;; (use "PosLeMonPlus")
;; (use "Truth")
(use "q<=r")
;; 11
(ng)
(assume "Absurd")
(use "Absurd")
;; 12
(assume "r" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 7
(cases)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
(assume "r" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 8
(assume "q")
(cases)
(assume "r" "Useless")
(use "IntLeTrans" (pt "IntP p"))
;; ?_33:p+IntN q<=p
(use "IntLePlusIntN")
(ng)
(use "Truth")
(assume "Useless")
(use "IntLeTrans" (pt "IntP p"))
(use "IntLePlusIntN")
(use "Truth")
;; 31
(assume "r")
;; ?_39:IntN q<=IntN r -> p+IntN q<=p+IntN r
(assume "r<=q")
(ng "r<=q")
(use "IntLeMonPlusIntN")
(use "r<=q")
;; 3
(assume "j" "i" "j<=i")
(use "j<=i")
;; 4
(assume "p")
(cases)
;; 45-47
(assume "q")
(cases)
;; 49-51
(assume "r" "q<=r")
(ng "q<=r")
(use "IntLeMonPlusIntP")
(use "q<=r")
;; 50
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 51
(assume "r" "Absurd")
(use "EfAtom")
(use "Absurd")
; 46
(cases)
;; 59-61
(assume "r" "Useless")
;; ?_62:IntN p+0<=IntN p+r
(assert "IntN p+0=IntN p")
 (use "Truth")
(assume "IntN p+0=IntN p")
(simp "IntN p+0=IntN p")
(drop "IntN p+0=IntN p")
(use "IntLePlusIntP")
;; 60
(strip)
(use "Truth")
;; 61
(assume "r" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 47
(assume "q")
(cases)
;; 72-74
(assume "r" "Useless")
(use "IntLeTrans" (pt "IntN p"))
(use "IntLePlusIntN")
(use "IntLePlusIntP")
;; 73
(assume "Useless")
(assert "IntN p+0=IntN p")
 (use "Truth")
(assume "IntN p+0=IntN p")
(simp "IntN p+0=IntN p")
(drop "IntN p+0=IntN p")
(use "IntLePlusIntN")
;; 74
(assume "r" "r<=q")
(ng "r<=q")
(use "IntLeMonPlusIntN")
(use "r<=q")
;; Subproof finished.
(assume "IntLeMonPlusAux")

;; Now for the main goal.
(assume "k" "j" "i" "i0" "k<=j" "i<=i0")
(use "IntLeTrans" (pt "k+i0"))
(use "IntLeMonPlusAux")
(use "i<=i0")
(simp "IntPlusComm")
(use "IntLeTrans" (pt "i0+j"))
(use "IntLeMonPlusAux")
(use "k<=j")
(simp "IntPlusComm")
(use "Truth")
;; Proof finished.
(save "IntLeMonPlus")

;; IntLtIntS
(set-goal "all k,j (k<IntS j)=(k<=j)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(ng)
(simp "PosLtPosS")
(use "Truth")
;; 7
(ng)
(use "Truth")
;; 8
(assume "q")
(ng)
(use "BooleAeqToEq")
(assume "p<S~p")
(assert "0<IntS IntN q")
 (use "IntLtTrans" (pt "IntP p"))
 (use "Truth")
 (use "p<S~p")
(ng)
(assume "Absurd")
(use "Absurd")
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(cases)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
;; 4
(assume "p")
(cases)
;; 33-35
(assume "q")
(ng)
(use "Truth")
(ng)
(use "Truth")
(assume "q")
(ng)
;; ?_40:(IntN p<IntS IntN q)=(q<=p)
(simp "<-" "IntUMinus1CompRule")
(simp "<-" "IntUMinus1CompRule")
(simp "<-" "IntUMinus3RewRule")
(simp "IntLtUMinus")
;; ?_44:(IntPred q<p)=(q<=p)
(use "PosLeCases" (pt "1") (pt "q"))
(use "Truth")
(assume "1<q")
(assert "all pos(1<pos -> IntP(PosPred pos)=IntPred pos)")
 (assume "pos" "1<p")
 (assert "PosS(PosPred pos)=pos")
  (use "PosSPosPredId")
  (use "1<p")
 (assume "PosS(PosPred pos)=pos")
 (simp "<-" "PosS(PosPred pos)=pos")
 (drop "PosS(PosPred pos)=pos")
 (ng)
 (use "Truth")
(assume "PosPredIntPredId")
(inst-with-to "PosPredIntPredId" (pt "q") "1<q" "PosPredIntPredIdInst")
(simp "<-" "PosPredIntPredIdInst")
(ng)
(simp "<-" "PosLtPosS")
(assert "PosS(PosPred q)=q")
 (use "PosSPosPredId")
 (use "1<q")
(assume "PosS(PosPred q)=q")
(simp "<-" "PosS(PosPred q)=q")
(drop "PosS(PosPred q)=q")
(ng)
(use "Truth")
;; 47
(assume "1=q")
(simp "<-" "1=q")
(ng)
(use "Truth")
;; Proof finished.
(save "IntLtIntS")

;; IntLeIntS
(set-goal "all k,j (IntS k<=j)=(k<j)")
(assume "k" "j")
(inst-with-to "IntLtIntS" (pt "IntS k") (pt "j") "IntLtIntSInst")
(ng "IntLtIntSInst")
(simp "IntLtIntSInst")
(use "Truth")
;; Proof finished.
(save "IntLeIntS")

;; IntLeAbs
(set-goal "all k k<=abs k")
(cases)
(assume "p")
(use "Truth")
(use "Truth")
(assume "p")
(use "Truth")
;; Proof finished.
;; (save "IntLeAbs")
(add-rewrite-rule "k<=abs k" "True")

(set-goal "all k 0<=abs k")
(cases)
(assume "p")
(use "Truth")
(use "Truth")
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "0<=abs k" "True")

(set-goal "all k ~abs k<=0")
(cases)
(assume "p")
(use "Truth")
(use "Truth")
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~abs k<=0" "True")

;; IntLeAbsPlus
(set-goal "all k,j abs(k+j)<=abs k+abs j")
(assert "all p,q abs(p+IntN q)<=abs p+abs IntN q")
(assume "p" "q")
(use "PosLeLtCases" (pt "p") (pt "q"))
(assume "p<=q")
(use "PosLeCases" (pt "p") (pt "q"))
(use "p<=q")
(assume "p<q")
(simp "IntPlusPNN")
(ng)
(use "PosLeTrans" (pt "q"))
(use "Truth")
(use "Truth")
(use "p<q")
(assume "p=q")
(simp "p=q")
(ng)
(use "Truth")
(assume "q<p")
(simp "IntPlusPNP")
(ng)
(use "PosLeTrans" (pt "p"))
(use "Truth")
(use "Truth")
(use "q<p")
;; Assertion proved.
(assume "Assertion")
(cases)
;; 27-29
(assume "p")
(cases)
;; 31-33
(assume "q")
(use "Truth")
;; 32
(use "Truth")
;; 33
(use "Assertion")
;; 28
(ng)
(strip)
(use "Truth")
;; 29
(assume "p")
(cases)
(assume "q")
(simp "IntPlusComm")
(assert "abs IntN p+abs q=abs q+abs IntN p")
 (use "IntPlusComm")
(assume "abs IntN p+abs q=abs q+abs IntN p")
(simp "abs IntN p+abs q=abs q+abs IntN p")
(use "Assertion")
;; 39
(ng)
(use "Truth")
;; 40
(assume "q")
(ng)
(use "Truth")
;; Proof finished.
(save "IntLeAbsPlus")
(add-rewrite-rule "abs(k+j)<=abs k+abs j" "True")

;; IntLeMinusAbs
(set-goal "all k,j(abs k+ ~abs j<=abs(k+ ~j))")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(use "Truth")
;; 7
(use "Truth")
;; 8
(assume "q")
(ng)
(cases 'auto)
(assume "Useless")
(use "Truth")
(assume "Useless")
(ng)
(cases 'auto)
(assume "Useless1")
(use "Truth")
(assume "Useless1")
(ng)
(use "PosLeTrans" (pt "p"))
(use "Truth")
(use "Truth")
;; 3
(assume "j")
(ng)
(use "IntLeTrans" (pt "0"))
(use "Truth")
(use "Truth")
;; 4
(assume "p")
(cases)
;; 29-31
(assume "q")
(ng)
(cases 'auto)
(assume "Useless")
(use "Truth")
(assume "Useless")
(ng)
(cases 'auto)
(assume "Useless1")
(use "Truth")
(assume "Useless1")
(ng)
(use "PosLeTrans" (pt "p"))
(use "Truth")
(use "Truth")
;; 30
(use "Truth")
;; 31
(assume "q")
(ng)
(cases 'auto)
(assume "Useless")
(use "Truth")
(assume "Useless")
(ng)
(cases 'auto)
(assume "Useless1")
(use "Truth")
(assume "Useless1")
(use "Truth")
;; Proof finished.
(save "IntLeMinusAbs")

;; IntLeAbs
(set-goal "all k,j(k<=j -> ~k<=j -> abs k<=j)")
(cases)
(cases)
(assume "j" "1<=j" "Useless")
(use "1<=j")
(assume "p" "j" "2p<=j" "Useless")
(ng)
(use "2p<=j")
(assume "p" "j" "2p+1<=j" "Useless")
(ng)
(use "2p+1<=j")
(assume "j" "0<=j" "Useless")
(use "0<=j")
(assume "p" "j" "Useless" "p<=j")
(ng)
(use "p<=j")
;; Proof finished.
(save "IntLeAbs")

;; IntLeMonMinus
(set-goal "all k,j,i,i0(k<=j -> i0<=i -> k-i<=j-i0)")
(assume "k" "j" "i" "i0" "k<=j" "i0<=i")
(ng)
(use "IntLeMonPlus")
(use "k<=j")
(simp "IntLeUMinus")
(use "i0<=i")
;; Proof finished.
(save "IntLeMonMinus")

(set-goal "all k k-k=0")
(cases)
;; 2-4
(assume "p")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k-k" "0")

(set-goal "all k k+ ~k=0")
(cases)
;; 2-4
(assume "p")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k+ ~k" "0")

(set-goal "all k ~k+k=0")
(cases)
;; 2-4
(assume "p")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~k+k" "0")

;; IntMinusPlusEq
(set-goal "all k,j k-j+j=k")
(assume "k" "j")
(ng)
(simp "<-" "IntPlusAssoc")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "k-j+j" "k")

;; IntLeAbsMinus
(set-goal "all k,i,j abs(k+ ~i)<=abs(k+ ~j)+abs(j+ ~i)")
(assume "k" "i" "j")
(assert "k+ ~i=(k+ ~j)+(j+ ~i)")
 (simp "<-" "IntPlusAssoc")
 (ng)
 (use "Truth")
(assume "Assertion")
(simp "Assertion")
(use "IntLeAbsPlus")
;; Proof finished.
(save "IntLeAbsMinus")
(add-rewrite-rule "abs(k+ ~i)<=abs(k+ ~j)+abs(j+ ~i)" "True")

;; IntAbsId
(set-goal "all k(0<=k -> abs k=k)")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "p" "Absurd")
(use "Absurd")
;; Proof finished.
(save "IntAbsId")

;; IntLtMonPlus1
(set-goal "all k,j,i,i0(k<j -> i<=i0 -> k+i<j+i0)")
(assume "k" "j" "i" "i1" "k<j" "i<=i1")
(simp "<-" "IntLeIntS")
(use-with "IntLeMonPlus" (pt "IntS k") (pt "j") (pt "i") (pt "i1") "?" "?")
(simp "IntLeIntS")
(use "k<j")
(use "i<=i1")
;; Proof finished.
(save "IntLtMonPlus1")

;; IntLtMonPlus2
(set-goal "all k,j,i,i0(k<=j -> i<i0 -> k+i<j+i0)")
(assume "k" "j" "i" "i1" "k<=j" "i<i1")
(simp "<-" "IntLeIntS")
(use-with "IntLeMonPlus" (pt "k") (pt "j") (pt "IntS i") (pt "i1") "?" "?")
(use "k<=j")
(simp "IntLeIntS")
(use "i<i1")
;; Proof finished.
(save "IntLtMonPlus2")

;; IntPlusOneIntS
(set-goal "all k k+1=IntS k")
(cases)
(assume "p")
(use "Truth")
(use "Truth")
(cases)
(use "Truth")
(assume "p")
(use "Truth")
(assume "p")
(use "Truth")
;; Proof finished.
(save "IntPlusOneIntS")

;; IntPlusIntNOneIntPred
(set-goal "all k k+IntN 1=IntPred k")
(cases)
(cases)
(use "Truth")
(assume "p")
(use "Truth")
(assume "p")
(use "Truth")
(use "Truth")
(cases)
(use "Truth")
(assume "p")
(use "Truth")
(assume "p")
(use "Truth")
;; Proof finished.
(save "IntPlusIntNOneIntPred")

;; Code discarded 2017-04-17.  Suberseded by IntTimesIntNL IntTimesIntNR
;; ;; IntTimesIntNOne
;; (set-goal "all k k*IntN 1= ~k")
;; (cases)
;; (assume "p")
;; (use "Truth")
;; (use "Truth")
;; (assume "p")
;; (use "Truth")
;; ;; Proof finished.
;; (save "IntTimesIntNOne")

;; ;; IntIntNOneTimes
;; (set-goal "all k IntN 1*k= ~k")
;; (cases)
;; (assume "p")
;; (use "Truth")
;; (use "Truth")
;; (assume "p")
;; (use "Truth")
;; ;; Proof finished.
;; (save "IntIntNOneTimes")

;; IntPlusCancelR
(set-goal "all k,j,i(k+j=i+j -> k=i)")
(assert "all j,k,i(k+j=i+j -> k=i)")
(cases)
;; 4-6
(ind)
(assume "k" "i")
(simp "IntPlusOneIntS")
(simp "IntPlusOneIntS")
(use "IntSInj")
;; 8
(assume "p" "IH" "k" "i")
(simp "IntPlusIdIntPSZero")
;; (pp "IntPlusIntPSZeroId") ;not saved
(simp "IntPlusIdIntPSZero")
(assume "EqHyp")
(use "IH")
(use "IH")
(use "EqHyp")
;; 9
(assume "p" "IH" "k" "i")
(simp "IntPlusIdIntPSOne")
(simp "IntPlusIdIntPSOne")
(simp "IntPlusIdIntPSZero")
(simp "IntPlusIdIntPSZero")
(assume "EqHyp")
(use "IH")
(use "IH")
(use "IntSInj")
(use "EqHyp")
;; 5
(assume "k" "i" "EqHyp")
(use "EqHyp")
;; 6
(ind)
(assume "k" "i")
(simp "IntPlusIntNOneIntPred")
(simp "IntPlusIntNOneIntPred")
(use "IntPredInj")
;; 30
(assume "p" "IH" "k" "i")
(simp "IntPlusIdIntNSZero")
(simp "IntPlusIdIntNSZero")
(assume "EqHyp")
(use "IH")
(use "IH")
(use "EqHyp")
;; 31
(assume "p" "IH" "k" "i")
(simp "IntPlusIdIntNSOne")
(simp "IntPlusIdIntNSOne")
(simp "IntPlusIdIntNSZero")
(simp "IntPlusIdIntNSZero")
(assume "EqHyp")
(use "IH")
(use "IH")
(use "IntPredInj")
(use "EqHyp")
;; Assertion proved.
(assume "Assertion"  "k" "j")
(use "Assertion")
;; Proof finished.
(save "IntPlusCancelR")

;; IntPlusCancelL
(set-goal "all k,j,i(k+j=k+i -> j=i)")
(assume "k" "j" "i")
(simp "IntPlusComm")
(simp (pf "k+i=i+k"))
(use "IntPlusCancelR")
(use "IntPlusComm")
;; Proof finished.
(save "IntPlusCancelL")

;; BooleEqTrans
(set-goal
 "all boole1,boole2,boole3(boole1=boole2 -> boole2=boole3 -> boole1=boole3)")
(assume "boole1" "boole2" "boole3" "=Hyp")
(simp "<-" "=Hyp")
(assume "b1=b3")
(use "b1=b3")
;; Proof finished.
(save "BooleEqTrans")

;; IntLePlusCancelR
(set-goal "all k,j,i (k+j<=i+j)=(k<=i)")
(assert "all j,k,i (k+j<=i+j)=(k<=i)")
(cases)
;; 4-6
(ind)
(assume "k" "i")
(simp "IntPlusOneIntS")
(simp "IntPlusOneIntS")
(use "Truth")
;; 8
(assume "p" "IH" "k" "i")
(simp "IntPlusIdIntPSZero")
(simp "IntPlusIdIntPSZero")
(use "BooleEqTrans" (pt "k+p<=i+p"))
(use "IH")
(use "IH")
;; 9
(assume "p" "IH" "k" "i")
(simp "IntPlusIdIntPSOne")
(simp "IntPlusIdIntPSOne")
(simp "IntPlusIdIntPSZero")
(simp "IntPlusIdIntPSZero")
(use "BooleEqTrans" (pt "k+p+p<=i+p+p"))
(use "Truth")
(use "BooleEqTrans" (pt "k+p<=i+p"))
(use "IH")
(use "IH")
;; 5
(assume "k" "i")
(use "Truth")
;; 6
(ind)
(assume "k" "i")
(simp "IntPlusIntNOneIntPred")
(simp "IntPlusIntNOneIntPred")
(simp "<-" "IntPlusIntNOneIntPred")
(simp "<-" "IntPlusIntNOneIntPred")
;; ?_35:(k+IntN 1<=i+IntN 1)=(k<=i)
(simp "IntPlusIntNOneIntPred")
(simp "IntPlusIntNOneIntPred")
(use "Truth")
;; 29
(assume "p" "IH" "k" "i")
(simp "IntPlusIdIntNSZero")
(simp "IntPlusIdIntNSZero")
(simp "IH")
(use "IH")
;; 30
(assume "p" "IH" "k" "i")
(simp "IntPlusIdIntNSOne")
(simp "IntPlusIdIntNSOne")
(ng)
(simp "IntPlusIdIntNSZero")
(simp "IntPlusIdIntNSZero")
(simp "IH")
(use "IH")
;; Assertion proved.
(assume "Assertion" "k" "j" "i")
(use "Assertion")
;; Proof finished.
(add-rewrite-rule "k+j<=i+j" "k<=i")

;; IntLePlusCancelL
(set-goal "all k,j,i (k+j<=k+i)=(j<=i)")
(assume "k" "j" "i")
(simp "IntPlusComm")
(simp (pf "k+i=i+k"))
(use "Truth")
(use "IntPlusComm")
;; Proof finished.
(add-rewrite-rule "k+j<=k+i" "j<=i")

;; IntLtPlusCancelR
(set-goal "all k,j,i (k+j<i+j)=(k<i)") ;as rewrite rule
(assume "k" "j" "i")
(use "BooleAeqToEq")
;; 3,4
(assume "k+j<i+j")
(use "IntNotLeToLt")
(assume "i<=k")
(assert "i+j<=k+j")
 (use "i<=k")
(assume "i+j<=k+j")
(assert "k+j<k+j")
(use "IntLtLeTrans" (pt "i+j"))
(use "k+j<i+j")
(use "i+j<=k+j")
(assume "Absurd")
(use "Absurd")
;; 4
(assume "k<i")
(use "IntNotLeToLt")
(ng)
(assume "i<=k")
(use-with "IntLtLeTrans" (pt "k") (pt "i") (pt "k") "k<i" "i<=k")
;; Proof finished.
(add-rewrite-rule "k+j<i+j" "k<i")

;; IntLtPlusCancelL
(set-goal "all k,j,i (k+j<k+i)=(j<i)") ;as rewrite rule
(assume "k" "j" "i")
(simp "IntPlusComm")
(simp (pf "k+i=i+k"))
(use "Truth")
(use "IntPlusComm")
;; Proof finished.
(add-rewrite-rule "k+j<k+i" "j<i")

;; Inserted 2021-02-24

;; IntLePlusL
(set-goal "all k,j,i(j<= ~k+i -> k+j<=i)")
(assume "k" "j" "i" "j<= ~k+i")
(simp "<-" "IntLe18RewRule" (pt "~k"))
(use "j<= ~k+i")
;; Proof finished.
;; (cdp)
(save "IntLePlusL")

;; IntLePlusLInv
(set-goal "all k,j,i(k+j<=i -> j<= ~k+i)")
(assume "k" "j" "i" "k+j<=i")
(simp "<-" "IntLe18RewRule" (pt "k"))
(use "k+j<=i")
;; Proof finished.
;; (cdp)
(save "IntLePlusLInv")

;; IntLePlusR
(set-goal "all k,j,i(~j+k<=i -> k<=j+i)")
(assume "k" "j" "i" "~j+k<=i")
(simp "<-" "IntLe18RewRule" (pt "~j"))
(use "~j+k<=i")
;; Proof finished.
;; (cdp)
(save "IntLePlusR")

;; IntLePlusRInv
(set-goal "all k,j,i(k<=j+i -> ~j+k<=i)")
(assume "k" "j" "i" "k<=j+i")
(simp "<-" "IntLe18RewRule" (pt "j"))
(use "k<=j+i")
;; Proof finished.
;; (cdp)
(save "IntLePlusRInv")

;; IntLeAbsMinus1
(set-goal "all k,j,i(abs(k+ ~j)<=i -> k<=j+i)")
(assume "k" "j" "i" "LeHyp")
(use "IntLePlusR")
(simp "IntPlusComm")
(use "IntLeTrans" (pt "abs(k+ ~j)"))
(use "Truth")
(use "LeHyp")
;; Proof finished.
;; (cdp)
(save "IntLeAbsMinus1")

;; IntAbsPlusUMinus
(set-goal "all k,j abs(k+ ~j)=abs(j+ ~k)")
(assume "k" "j")
(simp "<-" "IntAbs0RewRule")
(ng #t)
(simp "IntPlusComm")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "IntAbsPlusUMinus")

;; IntLeAbsMinus2
(set-goal "all k,j,i(abs(k+ ~j)<=i -> j<=k+i)")
(assume "k" "j" "i" "LeHyp")
(use "IntLePlusR")
(use "IntLeTrans" (pt "abs(~k+j)"))
(use "Truth")
(simp "IntPlusComm")
(simp "IntAbsPlusUMinus")
(use "LeHyp")
;; Proof finished.
;; (cdp)
(save "IntLeAbsMinus2")

;; End of insertion 2021-02-24

;; NatLeToIntLe
(set-goal "all n,m(n<=m -> IntLe n m)")
(assume "n")
(use "NatLeCases" (pt "Zero") (pt "n"))
;; 3-5
(use "Truth")
;; 4
(assume "0<n" "m")
(use "NatLeCases" (pt "Zero") (pt "m"))
;; 7-9
(use "Truth")
;; 8
(assume "0<m")
(simp "<-" "NatToPosLe")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "IntLe4CompRule")
(assume "LeHyp")
(use "LeHyp")
(use "0<m")
(use "0<n")
(use "0<m")
(use "0<n")
;; 9
(assume "0=m")
(simp "<-" "0=m")
(ng)
(assume "n=0")
(simp "n=0")
(use "Truth")
;; 5
(assume "0=n" "m")
(simp "<-" "0=n")
(assume "Useless")
(use "NatLeCases" (pt "Zero") (pt "m"))
(use "Truth")
(assume "0<m")
(ng)
(simp "<-" "IntPNatToPosEqNatToInt")
(use "Truth")
(use "0<m")
;; 30
(assume "0=m")
(simp "<-" "0=m")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLeToIntLe")

;; Added 2021-10-19

;; Properties of IntMax

(set-goal "all k k max k=k")
(ind)
;; 2-4
(assume "p")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "k max k" "k")

;; IntMaxUB1
(set-goal "all k,j k<=k max j")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(use "PosMaxUB1")
;; 7
(use "Truth")
;; 8
(assume "q")
(use "Truth")
;; 3
(cases)
;; 11-13
(assume "q")
(use "Truth")
;; 12
(use "Truth")
;; 13
(assume "q")
(use "Truth")
;; 4
(assume "p")
(cases)
;; 17-19
(assume "q")
(use "Truth")
;; 18
(use "Truth")
;; 19
(assume "q")
(use "PosMinLB1")
;; Proof finished.
;; (cdp)
(save "IntMaxUB1")

;; IntMaxUB2
(set-goal "all k,j j<=k max j")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(use "PosMaxUB2")
;; 7
(use "Truth")
;; 8
(assume "q")
(use "Truth")
;; 3
(cases)
;; 11-13
(assume "q")
(use "Truth")
;; 12
(use "Truth")
;; 13
(assume "q")
(use "Truth")
;; 4
(assume "p")
(cases)
;; 17-19
(assume "q")
(use "Truth")
;; 18
(use "Truth")
;; 19
(assume "q")
(use "PosMinLB2")
;; Proof finished.
;; (cdp)
(save "IntMaxUB2")

;; IntMaxLUB
(set-goal "all k,j,i(k<=i -> j<=i -> k max j<=i)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(cases)
;; 10-12
(use "PosMaxLUB")
;; 11
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 12
(assume "r" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 7
(assume "i" "p<=i" "Useless")
(use "p<=i")
;; 8
(assume "q" "i" "p<=i" "Useless")
(use "p<=i")
;; 3
(cases)
;; 19-21
(assume "p" "i" "Useless" "p<=i")
(use "p<=i")
;; 20
(assume "i" "0<=i" "Useless")
(use "0<=i")
;; 21
(assume "q" "i" "0<=i" "Useless")
(use "0<=i")
;; 4
(assume "p")
(cases)
;; 26-28
(assume "q" "i" "Useless" "q<=i")
(use "q<=i")
;; 27
(assume "i" "Useless" "0<=i")
(use "0<=i")
;; 28
(assume "q")
(cases)
;; 32-34
(assume "r" "Useless1" "Useless2")
(use "Truth")
;; 33
(assume "Useless1" "Useless2")
(use "Truth")
;; 34
(use "PosMinGLB")
;; Proof finished.
;; (cdp)
(save "IntMaxLUB")

;; IntLeMonMax
(set-goal "all k,j,i,i1(k<=j -> i<=i1 -> k max i<=j max i1)")
(assert "all k,j,i(k<=j -> k max i<=j max i)")
 (assume "k" "j" "i" "k<=j")
 (use "IntMaxLUB")
 (use "IntLeTrans" (pt "j"))
 (use "k<=j")
 (use "IntMaxUB1")
 (use "IntMaxUB2")
;; Assertion proved
(assume "Assertion1")
(assert "all k,j,i(j<=i -> k max j<=k max i)")
 (assume "k" "j" "i" "j<=i")
 (use "IntMaxLUB")
 (use "IntMaxUB1")
 (use "IntLeTrans" (pt "i"))
 (use "j<=i")
 (use "IntMaxUB2")
;; Assertion proved
(assume "Assertion2" "k" "j" "i" "i1" "k<=j" "i<=i1")
(use "IntLeTrans" (pt "j max i"))
(use "Assertion1")
(use "k<=j")
(use "Assertion2")
(use "i<=i1")
;; Proof finished.
;; (cdp)
(save "IntLeMonMax")

;; IntMaxComm
(set-goal "all k,j k max j=j max k")
(assume "k" "j")
(use "IntLeAntiSym")
(use "IntMaxLUB")
(use "IntMaxUB2")
(use "IntMaxUB1")
(use "IntMaxLUB")
(use "IntMaxUB2")
(use "IntMaxUB1")
;; Proof finished.
;; (cdp)
(save "IntMaxComm")

;; IntMaxAssoc
(set-goal "all k,j,i k max(j max i)=k max j max i")
(assume "k" "j" "i")
(use "IntLeAntiSym")
;; 3,4
(use "IntMaxLUB")
(use "IntLeTrans" (pt "k max j"))
(use "IntMaxUB1")
(use "IntMaxUB1")
(use "IntLeMonMax")
(use "IntMaxUB2")
(use "Truth")
;; 4
(use "IntMaxLUB")
(use "IntLeMonMax")
(use "Truth")
(use "IntMaxUB1")
(use "IntLeTrans" (pt "j max i"))
(use "IntMaxUB2")
(use "IntMaxUB2")
;; Proof finished.
;; (cdp)
(save "IntMaxAssoc")
(add-rewrite-rule "k max(j max i)" "k max j max i")

;; IntMaxEq1
(set-goal "all k,j(j<=k -> k max j=k)")
(assume "k" "j" "j<=k")
(use "IntLeAntiSym")
(use "IntMaxLUB")
(use "Truth")
(use "j<=k")
(use "IntMaxUB1")
;; Proof finished.
;; (cdp)
(save "IntMaxEq1")

;; IntMaxEq2
(set-goal "all k,j(k<=j -> k max j=j)")
(assume "k" "j" "k<=j")
(use "IntLeAntiSym")
(use "IntMaxLUB")
(use "k<=j")
(use "Truth")
(use "IntMaxUB2")
;; Proof finished.
;; (cdp)
(save "IntMaxEq2")

;; IntMaxEq1Rev
(set-goal "all k,j(k max j=k -> j<=k)")
(assume "k" "j" "EqH")
(simp "<-" "EqH")
(use "IntMaxUB2")
;; Proof finished.
;; (cdp)
(save "IntMaxEq1Rev")

;; IntMaxEq2Rev
(set-goal "all k,j(k max j=j -> k<=j)")
(assume "k" "j" "EqH")
(simp "<-" "EqH")
(use "IntMaxUB1")
;; Proof finished.
;; (cdp)
(save "IntMaxEq2Rev")

;; Properties of IntMin

(set-goal "all k k min k=k")
(ind)
;; 2-4
(assume "p")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "k min k" "k")

;; IntMinLB1
(set-goal "all k,j k min j<=k")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(use "PosMinLB1")
;; 7
(use "Truth")
;; 8
(assume "q")
(use "Truth")
;; 3
(cases)
;; 11-13
(assume "q")
(use "Truth")
;; 12
(use "Truth")
;; 13
(assume "q")
(use "Truth")
;; 4
(assume "p")
(cases)
;; 17-19
(assume "q")
(use "Truth")
;; 18
(use "Truth")
;; 19
(assume "q")
(use "PosMaxUB1")
;; Proof finished.
;; (cdp)
(save "IntMinLB1")

;; IntMinLB2
(set-goal "all k,j k min j<=j")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(use "PosMinLB2")
;; 7
(use "Truth")
;; 8
(assume "q")
(use "Truth")
;; 3
(cases)
;; 11-13
(assume "q")
(use "Truth")
;; 12
(use "Truth")
;; 13
(assume "q")
(use "Truth")
;; 4
(assume "p")
(cases)
;; 17-19
(assume "q")
(use "Truth")
;; 18
(use "Truth")
;; 19
(assume "q")
(use "PosMaxUB2")
;; Proof finished.
;; (cdp)
(save "IntMinLB2")

;; IntMinGLB
(set-goal "all k,j,i(i<=k -> i<=j -> i<=k min j)")
(cases)
;; 2-4
(assume "p")
(cases)
;; 6-8
(assume "q")
(cases)
;; 10-12
(ng)
(use "PosMinGLB")
;; 11
(ng)
(assume "Useless1" "Useless2")
(use "Truth")
;; 12
(ng)
(assume "r" "Useless1" "Useless2")
(use "Truth")
;; 7
(ng)
(assume "i" "Useless" "i<=0")
(use "i<=0")
;; 8
(ng)
(assume "q" "i" "Useless" "i<=Nq")
(use "i<=Nq")
;; 3
(cases)
;; 22-24
(ng)
(assume "p" "i" "i<=0" "Useless")
(use "i<=0")
;; 23
(ng)
(assume "i" "Useless" "i<=0")
(use "i<=0")
;; 24
(ng)
(assume "p" "i" "Useless" "i<=Np")
(use "i<=Np")
;; 4
(assume "p")
(cases)
;; 32-34
(ng)
(assume "q" "i" "i<=Np" "Useless")
(use "i<=Np")
;; 33
(ng)
(assume "i" "i<=Np" "Useless")
(use "i<=Np")
;; 34
(assume "q")
(cases)
;; 40-42
(ng)
(assume "r" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 41
(ng)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 42
(ng)
(use "PosMaxLUB")
;; Proof finished.
;; (cdp)
(save "IntMinGLB")

;; IntLeMonMin
(set-goal "all k,j,i,i1(k<=j -> i<=i1 -> k min i<=j min i1)")
(assert "all k,j,i(k<=j -> k min i<=j min i)")
 (assume "k" "j" "i" "k<=j")
 (use "IntMinGLB")
(use "IntLeTrans" (pt "k"))
(use "IntMinLB1")
(use "k<=j")
(use "IntMinLB2")
;; Assertion proved
(assume "Assertion1")
(assert "all k,j,i(j<=i -> k min j<=k min i)")
(assume "k" "j" "i" "j<=i")
(use "IntMinGLB")
(use "IntMinLB1")
(use "IntLeTrans" (pt "j"))
(use "IntMinLB2")
(use "j<=i")
;; Assertion proved
(assume "Assertion2" "k" "j" "i" "i1" "k<=j" "i<=i1")
(use "IntLeTrans" (pt "j min i"))
(use "Assertion1")
(use "k<=j")
(use "Assertion2")
(use "i<=i1")
;; Proof finished.
;; (cdp)
(save "IntLeMonMin")

;; IntMinComm
(set-goal "all k,j k min j=j min k")
(assume "k" "j")
(use "IntLeAntiSym")
(use "IntMinGLB")
(use "IntMinLB2")
(use "IntMinLB1")
(use "IntMinGLB")
(use "IntMinLB2")
(use "IntMinLB1")
;; Proof finished.
;; (cdp)
(save "IntMinComm")

(set-goal "all k k min k=k")
(assume "k")
(use "IntLeAntiSym")
(use "Truth")
(use "IntMinGLB")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "k min k" "k")

;; IntMinAssoc
(set-goal "all k,j,i k min(j min i)=k min j min i")
(assume "k" "j" "i")
(use "IntLeAntiSym")
;; 3,4
(use "IntMinGLB")
(use "IntLeMonMin")
(use "Truth")
(use "IntMinLB1")
(use "IntLeTrans" (pt "j min i"))
(use "IntMinLB2")
(use "IntMinLB2")
;; 4
(use "IntMinGLB")
(use "IntLeTrans" (pt "k min j"))
(use "IntMinLB1")
(use "IntMinLB1")
(use "IntLeMonMin")
(use "IntMinLB2")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "IntMinAssoc")
(add-rewrite-rule "k min(j min i)" "k min j min i")

;; IntMinEq1
(set-goal "all k,j(k<=j -> k min j=k)")
(assume "k" "j" "k<=j")
(use "IntLeAntiSym")
(use "IntMinLB1")
(use "IntMinGLB")
(use "Truth")
(use "k<=j")
;; Proof finished.
;; (cdp)
(save "IntMinEq1")

;; IntMinEq2
(set-goal "all k,j(j<=k -> k min j=j)")
(assume "k" "j" "j<=k")
(use "IntLeAntiSym")
(use "IntMinLB2")
(use "IntMinGLB")
(use "j<=k")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "IntMinEq2")

;; IntMinEq1Rev
(set-goal "all k,j(k min j=k -> k<=j)")
(assume "k" "j" "EqH")
(simp "<-" "EqH")
(use "IntMinLB2")
;; Proof finished.
;; (cdp)
(save "IntMinEq1Rev")

;; IntMinEq2Rev
(set-goal "all k,j(k min j=j -> j<=k)")
(assume "k" "j" "EqH")
(simp "<-" "EqH")
(use "IntMinLB1")
;; Proof finished.
;; (cdp)
(save "IntMinEq2Rev")

;; IntTimesMaxDistr
(set-goal "all k,j,i(0<=k -> k*(j max i)=k*j max(k*i))")
(cases)
;; 2-4
(assert "all p,j,i p*(j max i)=p*j max(p*i)")
(ind)
;; 7-9
(assume "j" "i")
(use "Truth")
;; 8
(assume "p" "IH" "j" "i")
(use "IntLeLtCases" (pt "j") (pt "i"))
;; 12,13
(assume "j<=i")
(simp (pf "j max i=i"))
(simp (pf "SZero p*j max(SZero p*i)=SZero p*i"))
(use "Truth")
(use "IntMaxEq2")
(use "j<=i")
(use "IntMaxEq2")
(use "j<=i")
;; 13
(assume "i<j")
(inst-with-to "IntLtToLe" (pt "i") (pt "j") "i<j" "i<=j")
(simp (pf "j max i=j"))
(simp (pf "SZero p*j max(SZero p*i)=SZero p*j"))
(use "Truth")
(use "IntMaxEq1")
(use "i<=j")
(use "IntMaxEq1")
(use "i<=j")
;; 9
(assume "p" "IH" "j" "i")
(use "IntLeLtCases" (pt "j") (pt "i"))
;; 31,32
(assume "j<=i")
(simp (pf "j max i=i"))
(simp (pf "SOne p*j max(SOne p*i)=SOne p*i"))
(use "Truth")
(use "IntMaxEq2")
(use "j<=i")
(use "IntMaxEq2")
(use "j<=i")
;; 32
(assume "i<j")
(inst-with-to "IntLtToLe" (pt "i") (pt "j") "i<j" "i<=j")
(simp (pf "j max i=j"))
(simp (pf "SOne p*j max(SOne p*i)=SOne p*j"))
(use "Truth")
(use "IntMaxEq1")
(use "i<=j")
(use "IntMaxEq1")
(use "i<=j")
;; Assertion proved.
(assume "Assertion" "p" "j" "i" "Useless")
(use "Assertion")
;; 3
(assume "j" "i" "Useless")
(use "Truth")
;; 4
(assume "p" "j" "i" "Absurd")
(use "EfAtom")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "IntTimesMaxDistr")

(add-program-constant "PosQR" (py "pos=>pos=>int yprod int"))
;; (remove-program-constant "PosQR")

(add-computation-rules
 "PosQR 1 1" "IntP 1 pair 0"
 "PosQR 1(SZero q)" "0 pair IntP 1"
 "PosQR 1(SOne q)" "0 pair IntP 1"

 "PosQR(SZero p)q"
 "[if (PosQR p q)
      ([k,j] [if (2*j<q) (2*k pair 2*j) (2*k+1 pair 2*j-q)])]"

 "PosQR(SOne p)q"
 "[if (PosQR p q)
      ([k,j] [if (2*j+1<q) (2*k pair 2*j+1) (2*k+1 pair 2*j+1-q)])]")

;; Tests

;; (pp (nt (pt "PosQR 1 2")))
;; (pp (nt (pt "PosQR 1 3")))
;; (pp (nt (pt "PosQR 1 7")))

;; (pp (nt (pt "PosQR 2 1")))
;; (pp (nt (pt "PosQR 2 2")))
;; (pp (nt (pt "PosQR 2 3")))
;; (pp (nt (pt "PosQR 2 7")))

;; (pp (nt (pt "PosQR 3 1")))
;; (pp (nt (pt "PosQR 3 2")))
;; (pp (nt (pt "PosQR 3 3")))
;; (pp (nt (pt "PosQR 3 4")))
;; (pp (nt (pt "PosQR 3 7")))

;; (pp (nt (pt "PosQR 456 63"))) ;7 pair 15
;; (pp (nt (pt "7*63+15"))) ;456

;; (time (pp (nt (pt "PosQR 123456 123"))))
;; ;; 1003 pair 87
;; ;; 39 ms
;; (pp (nt (pt "1003*123+87")))
;; 123456

(set-totality-goal "PosQR")
(use "AllTotalElim")
(ind)
;; 3-5
(use "AllTotalElim")
(cases)
;; 7-9
(use "YprodTotalVar")
;; 8
(assume "q")
(use "YprodTotalVar")
;; 9
(assume "q")
(use "YprodTotalVar")
;; 4
(assume "p" "IH")
(use "AllTotalElim")
(assume "q")
(ng #t)
(use "YprodIfTotal")
;; 16,17
(use "IH")
(use "PosTotalVar")
;; 17
(use "AllTotalElim")
(assume "k")
(use "AllTotalElim")
(assume "j")
(use "BooleIfTotal")
;; 23-25
(use "BooleTotalVar")
;; 24
(use "YprodTotalVar")
;; 25
(use "YprodTotalVar")
;; 5
(assume "p" "IH")
(use "AllTotalElim")
(assume "q")
(ng #t)
(use "YprodIfTotal")
;; 30,31
(use "IH")
(use "PosTotalVar")
;; 31
(use "AllTotalElim")
(assume "k")
(use "AllTotalElim")
(assume "j")
(use "BooleIfTotal")
;; 37-39
(use "BooleTotalVar")
;; 38
(use "YprodTotalVar")
;; 39
(use "YprodTotalVar")
;; Proof finished.
(save-totality)

(add-var-name "kj" (py "int yprod int"))

;; YprodIntIntEqToEqD
(set-goal "all kj1,kj2(kj1=kj2 -> kj1 eqd kj2)")
(cases)
(assume "k1" "j1")
(cases)
(assume "k2" "j2" "k1j1=k2j2")
(ng "k1j1=k2j2")
(assert "k1 eqd k2")
 (use "IntEqToEqD")
 (use "k1j1=k2j2")
(assume "k1 eqd k2")
(assert "j1 eqd j2")
 (use "IntEqToEqD")
 (use "k1j1=k2j2")
(assume "j1 eqd j2")
(drop "k1j1=k2j2")
(elim "k1 eqd k2")
(assume "k^")
(elim "j1 eqd j2")
(assume "j^")
(use "InitEqD")
;; Proof finished.
(save "YprodIntIntEqToEqD")

;; The next proof is taken from libintqr.scm.  Renamed
;; PosQRCorr into PosQRCorrAux, 
;; PosQuotRemCorr into PosQRCorr

;; PosQRCorrAux
(set-goal "all p,q,k,j(PosQR p q=(k pair j) -> p=k*q+j andnc 0<=j andnc j<q)")
;; For the induction steps it will be helpful to have IHAux
(assert "all p,q(p=lft(PosQR p q)*q+rht(PosQR p q) ->
                 SZero p=2*lft(PosQR p q)*q+2*rht(PosQR p q))")
 (assume "p" "q" "EqHyp")
 (simp "<-" "IntTimesAssoc")
 (simp "<-" "IntTimesPlusDistr")
 (simp "<-" "EqHyp")
 (use "Truth")
(assume "IHAux")
(ind)
;; 9-11
(cases)
;; 12-13
(assume "k" "j")
(ng #t)
(simp "<-" "IfAndb")
(cases (pt "1=k"))
(ng #t)
(assume "1=k")
(simp "<-" "1=k")
(assume "0=j")
(simp "<-" "0=j")
(ng #t)
(split)
(use "Truth")
(split)
(use "Truth")
(use "Truth")
;; 19
(ng #t)
(assume "Useless" "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(use "EfAtom")
(use "Absurd")
;; 13
(assume "p" "k" "j")
(ng #t)
(simp "<-" "IfAndb")
(cases (pt "0=k"))
;; 35,36
(ng #t)
(assume "0=k")
(simp "<-" "0=k")
(assume "1=j")
(simp "<-" "1=j")
(ng #t)
(split)
(use "Truth")
(split)
(use "Truth")
(use "Truth")
;; 29
(ng #t)
(assume "Useless" "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(use "EfAtom")
(use "Absurd")
;; 14
(assume "p" "k" "j")
(ng #t)
(simp "<-" "IfAndb")
(cases (pt "0=k"))
;; 52,53
(ng #t)
(assume "0=k")
(simp "<-" "0=k")
(assume "1=j")
(simp "<-" "1=j")
(ng #t)
(split)
(use "Truth")
(split)
(use "Truth")
(use "Truth")
;; 53
(ng #t)
(assume "Useless" "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(use "EfAtom")
(use "Absurd")
;; 10
(assume "p" "IH" "q" "k" "j")
(ng #t)
(assert "all kj kj=(lft kj pair rht kj)") ;Use PairConstrOneTwo instead
 (cases)
 (ng #t)
 (strip)
 (use "Truth")
(assume "Assertion")
(inst-with-to "Assertion" (pt "PosQR p q") "InstAssertion")
(simp "InstAssertion")
(ng #t)
(cases (pt "(2*rht(PosQR p q)<q)"))
;; 78,79
(ng #t)
(inst-with-to "IH" (pt "q") (pt "lft(PosQR p q)") (pt "rht(PosQR p q)")
	      "InstAssertion" "InstIH")
(assume "2*rht(PosQR p q)<q")
(simp "<-" "IfAndb")
(cases (pt "2*lft(PosQR p q)=k"))
;; 85,86
(assume "2*lft(PosQR p q)=k")
(ng #t)
(simp "<-" "2*lft(PosQR p q)=k")
(assume "2*rht(PosQR p q)=j")
(simp "<-" "2*rht(PosQR p q)=j")
(split)
(use "IHAux")
(use "InstIH")
;; 93
(split)
(simp "IntTimesComm")
(simp (pf "0=0*2"))
(use "IntLeMonTimes")
(use "Truth")
(use "InstIH")
(use "Truth")
(use "2*rht(PosQR p q)<q")
;; 86
(assume "2*lft(PosQR p q)=k -> F")
(ng #t)
(assume "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(use "EfAtom")
(use "Absurd")
;; 100
(ng #t)
(assume "2*rht(PosQR p q)<q -> F")
(assert "q<=2*rht(PosQR p q)")
 (use "IntNotLtToLe")
 (use "2*rht(PosQR p q)<q -> F")
(assume "q<=2*rht(PosQR p q)")
(simp "<-" "IfAndb")
(cases (pt "(2*lft(PosQR p q)+1=k)"))
;; 140,141
(ng #t)
(assume "2*lft(PosQR p q)+1=k")
(simp "<-" "2*lft(PosQR p q)+1=k")
(assume "2*rht(PosQR p q)+IntN q=j")
(simp "<-" "2*rht(PosQR p q)+IntN q=j")
(split)
(ng #t)
(simp "<-" "IntPlusAssoc")
(simp "<-" "IntPlusAssoc")
(inst-with-to "IntPlusComm" (pt "2*rht(PosQR p q)") (pt "IntN q") "InstComm")
(simp "InstComm")
(ng #t)
;; ?^155:SZero p=2*lft(PosQR p q)*q+2*rht(PosQR p q)
(use "IHAux")
(inst-with-to "IH" (pt "q") (pt "lft(PosQR p q)") (pt "rht(PosQR p q)")
	      "InstAssertion" "InstIH")
(use "InstIH")
;; 148
(split)
(simp (pf "0=0+q+IntN q"))
(use "IntLeMonPlus")
(use "q<=2*rht(PosQR p q)")
(use "Truth")
(ng #t)
(use "Truth")
(inst-with-to "IH" (pt "q") (pt "lft(PosQR p q)") (pt "rht(PosQR p q)")
	      "InstAssertion" "InstIH")
(assert "2*rht(PosQR p q)=rht(PosQR p q)+rht(PosQR p q)")
 (simp (pf "2=IntP 1+IntP 1"))
 (simp "IntTimesPlusDistrLeft")
 (ng #t)
 (use "Truth")
 (use "Truth")
(assume "Assertion1")
(simp "Assertion1")
(simp "<-" "IntPlusAssoc")
(use "IntLtLeTrans" (pt "rht(PosQR p q)+(q+IntN q)"))
;;   InstIH:p=lft(PosQR p q)*q+rht(PosQR p q) andnc 
;;          0<=rht(PosQR p q) andnc rht(PosQR p q)<q
;; -----------------------------------------------------------------------------
;; ?^177:rht(PosQR p q)+(rht(PosQR p q)+IntN q)<rht(PosQR p q)+(q+IntN q)

;; (pp "IntLtMonPlus1")
;; all k,j,i,i0(k<j -> i<=i0 -> k+i<j+i0)

(use "IntLtMonPlus2")
(use "Truth")
(use "IntLtMonPlus1")
(use "InstIH")
(use "Truth")
(ng #t)
(use "IntLtToLe")
(use "InstIH")
;; 141
(ng #t)
(assume "Useless" "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(use "EfAtom")
(use "Absurd")
;; 11
;; 2016-10-24.  Done up to this point.  provide InstIH early
(assume "p" "IH" "q" "k" "j")
(ng #t)
(assert "all kj kj=(lft kj pair rht kj)")
 (cases)
 (ng #t)
 (strip)
 (use "Truth")
(assume "Assertion")
(inst-with-to "Assertion" (pt "PosQR p q") "InstAssertion")
(simp "InstAssertion")
(ng #t)
(inst-with-to "IH" (pt "q") (pt "lft(PosQR p q)") (pt "rht(PosQR p q)")
	      "InstAssertion" "InstIH")
(simp "IntPlusOneIntS")
(cases (pt "IntS(2*rht(PosQR p q))<q"))
;; 209,210
(ng #t)
(assume "IntS(2*rht(PosQR p q))<q")
(simp "<-" "IfAndb")
(cases (pt "(2*lft(PosQR p q)=k)"))
;; 214,215
(assume "2*lft(PosQR p q)=k")
(ng #t)
(assume "IntS(2*rht(PosQR p q))=j")
(simp "<-" "IntS(2*rht(PosQR p q))=j")
(split)
(ng #t)
;;   IHAux:all p,q(
;;          p=lft(PosQR p q)*q+rht(PosQR p q) -> 
;;          SZero p=2*lft(PosQR p q)*q+2*rht(PosQR p q))
;;   p16822  p  IH:all q,k,j(PosQR p q=(k pair j) -> p=k*q+j andnc 0<=j andnc j<q)
;;   q  k  j  Assertion:all kj kj=(lft kj pair rht kj)
;;   InstAssertion:PosQR p q=(lft(PosQR p q)pair rht(PosQR p q))
;;   InstIH:p=lft(PosQR p q)*q+rht(PosQR p q) andnc 
;;          0<=rht(PosQR p q) andnc rht(PosQR p q)<q
;;   IntS(2*rht(PosQR p q))<q:
;;     IntS(2*rht(PosQR p q))<q
;;   2*lft(PosQR p q)=k:2*lft(PosQR p q)=k
;;   IntS(2*rht(PosQR p q))=j:
;;     IntS(2*rht(PosQR p q))=j
;; -----------------------------------------------------------------------------
;; ?^222:SOne p=IntS(k*q+2*rht(PosQR p q))

(simp (pf "SOne p=IntS(SZero p)")) ;normalizes to T
(simp (pf "SZero p=k*q+2*rht(PosQR p q)"))
 (use "Truth")
(simp "<-" "2*lft(PosQR p q)=k")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesPlusDistr")
(simp "<-" "InstIH")
(ng #t)
(use "Truth")
(use "Truth")
;; 221
(split)
(use "IntLeTrans" (pt "2*rht(PosQR p q)"))
(simp "IntTimesComm")
(simp (pf "0=0*2"))
(use "IntLeMonTimes")
(use "Truth")
(use "InstIH")
(use "Truth")
(use "Truth")
(use "IntS(2*rht(PosQR p q))<q")
;; 215
(assume "2*lft(PosQR p q)=k -> F")
(ng #t)
(assume "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(use "EfAtom")
(use "Absurd")
;; 210
(ng #t)
(assume "IntS(2*rht(PosQR p q))<q -> F")
(assert "q<=IntS(2*rht(PosQR p q))")
 (use "IntNotLtToLe")
 (use "IntS(2*rht(PosQR p q))<q -> F")
(assume "q<=IntS(2*rht(PosQR p q))")
;; New from here onwards
(simp "<-" "IfAndb")
(cases (pt "2*lft(PosQR p q)+1=k"))
;; 258,259
(assume "2*lft(PosQR p q)+1=k")
(ng #t)
(assume "IntS(2*rht(PosQR p q)+IntN q)=j")
(simp "<-" "IntS(2*rht(PosQR p q)+IntN q)=j")
(split)
(simp "<-" "2*lft(PosQR p q)+1=k")
(ng #t)
(simp "<-" "IntPlusAssoc")
(simp "<-" "IntPlusAssoc")
(assert "all i q+(i+IntN q)=i")
 (assume "i")
 (simp (pf "i+IntN q=IntN q+i"))
 (simp "IntPlusAssoc")
 (ng #t)
 (use "Truth")
 (use "IntPlusComm")
(assume "AllEqHyp")
(simp "AllEqHyp")
(simp (pf "SOne p=IntS(SZero p)"))
(simp "IHAux" (pt "q"))
(use "Truth")
(use "InstIH")
(use "Truth")
(split)
;; ?^283:0<=IntS(2*rht(PosQR p q)+IntN q)
(assert "q+ ~q<=IntS(2*rht(PosQR p q))+ ~q")
 (use "IntLeMonPlus")
 (use "q<=IntS(2*rht(PosQR p q))")
 (use "Truth")
(assume "q+ ~q<=IntS(2*rht(PosQR p q))+ ~q")
(use "q+ ~q<=IntS(2*rht(PosQR p q))+ ~q")
;; ?^284:IntS(2*rht(PosQR p q)+IntN q)<q
(assert "all i 2*i=i+i") ;should go into int.scm, as IntTimesTwoPlusId
 (assume "i")
 (simp-with (pf "2=IntP 1+IntP 1"))
 (simp "IntTimes7RewRule")
 (use "Truth")
 (use "Truth")
(assume "IntTimesTwoPlusId")
(simp "IntTimesTwoPlusId")
(simp "<-" "IntPlusAssoc")
(simp "<-" "IntPlus2RewRule")
(use "IntLeLtTrans" (pt "q+(rht(PosQR p q)+IntN q)"))
(use "IntLeMonPlus")
(simp "IntLeIntS")
(use "InstIH")
(use "Truth")
(ng #t)
(simp "IntPlusComm")
(ng #t)
(use "InstIH")
;; 259
(ng #t)
(assume "Useless" "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(use "EfAtom")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "PosQRCorrAux")

;; PosQRCorr
(set-goal "all p,q(
     p=lft(PosQR p q)*q+rht(PosQR p q) andnc 
     0<=rht(PosQR p q) andnc rht(PosQR p q)<q)")
(assume "p" "q")
(use "PosQRCorrAux")
(simp "PairConstrOneTwo")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosQRCorr")

;; Added 2020-08-28

;; NatToIntPlus
(set-goal "all n,m IntPlus n m=n+m")
(cases)
(assume "m")
(use "Truth")
(assume "n")
(cases)
(use "Truth")
(assume "m")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "IntPlus2CompRule")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "NatToPosPlus")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "NatToIntPlus")

;; NatToIntSuccPos
(set-goal "all n exl p NatToInt(Succ n)=IntPos p")
(ind)
(intro 0 (pt "1"))
(use "Truth")
;; 3
(ng)
(assume "n" "IH")
(by-assume "IH" "p" "pProp")
(simp "pProp")
(intro 0 (pt "PosS p"))
(use "Truth")
;; Proof finished.
(save "NatToIntSuccPos")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [n](Rec nat=>pos)n 1([n0]PosS)

(set-goal "all n 0<=NatToInt n")
(cases)
(use "Truth")
(assume "n")
(inst-with-to "NatToIntSuccPos" (pt "n") "pEx")
(by-assume "pEx" "p" "pProp")
(simp "pProp")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "0<=NatToInt n" "True")

(set-goal "all n (IntS n<=0)=False")
(cases)
(use "Truth")
(assume "n")
(inst-with-to "NatToIntSuccPos" (pt "n") "pEx")
(by-assume "pEx" "p" "pProp")
(simp "pProp")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntS n<=0" "False")

;; IntSNat
(set-goal "all n IntS(NatToInt n)=Succ n")
(cases)
(use "Truth")
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "IntSNat")

;; NatToIntLe
(set-goal "all n,m (NatToInt n<=NatToInt m)=(n<=m)")
(ind)
(assume "m")
(use "Truth")
(assume "n" "IH")
(cases)
(use "Truth")
(assume "m")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatToIntLe")

;; IntPosTimes
(set-goal "all k,j(0<k*j -> 0<=k -> 0<j)")
(cases)
(assume "p")
(cases)
(strip)
(use "Truth")
(assume "Absurd" "Useless")
(use "Absurd")
(assume "q" "Absurd" "Useless")
(use "Absurd")
;; 3
(assume "j" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 4
(assume "p")
(cases)
(strip)
(use "Truth")
(assume "Absurd" "Useless")
(use "Absurd")
(assume "q" "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "IntPosTimes")

(set-goal "all k 0<=k*k")
(cases)
;; 2-4
(assume "p")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "0<=k*k" "True")

;; IntExpTimes
(set-goal "all k,j,n (k*j)**n=k**n*j**n")
(assume "k" "j")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(simp "IH")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" (pf "k*(j**n*j)=(j**n*(k*j))"))
(use "Truth")
(simp "IntTimesComm")
(simp (pf "k*j=j*k"))
(use "Truth")
(use "IntTimesComm")
;; Proof finished.
;; (cdp)
(save "IntExpTimes")

;; IntExpTimesPos
(set-goal "all k,p,n (k*p)**n=k**n*p**n")
(assume "k" "p")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(simp "IH")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" (pf "k*(p**n*p)=(p**n*(k*p))"))
(use "Truth")
(simp "IntTimesComm")
(simp (pf "k*p=p*k"))
(use "Truth")
(use "IntTimesComm")
;; Proof finished.
;; (cdp)
(save "IntExpTimesPos")

