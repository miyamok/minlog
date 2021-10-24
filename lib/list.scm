;; 2021-10-20.  list.scm.

;; (load "~/git/minlog/init.scm")
;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")"))

(display "loading list.scm ...") (newline)

(add-algs "list" 'prefix-typeop
	  '("list" "Nil")
	  '("alpha=>list=>list" "Cons"))

(add-var-name "x" (py "alpha"))
(add-var-name "xs" (py "list alpha"))
(add-var-name "xf" (py "nat=>alpha"))

;; Infix notation allowed (and type parameters omitted) for binary
;; constructors, as follows.  This would also work for prefix notation.
;; Example: :: for Cons.  x::y::z:
;; Here : is postfix for z

;; The line below is commented out.
;; (add-infix-display-string "Cons" "::" 'pair-op) ;right associative
;; Instead add-token and add-display are specially done for ::

(add-token
 "::" 'pair-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form
     (let* ((const (constr-name-to-constr "Cons"))
	    (uninst-type (const-to-uninst-type const))
	    (patterns (arrow-form-to-arg-types uninst-type 2)) ;al, list al
	    (instances (map term-to-type (list x y))) ;e.g.  nat, list int
	    (type1 (car instances)) ;nat
	    (type2 (car (alg-form-to-types (cadr instances)))) ;int
	    (tsubst (cond ((type-le? type1 type2)
			   (make-subst (car patterns) type2))
			  ((type-le? type2 type1)
			   (make-subst (car patterns) type1))
			  (else (myerror "comparable types expected"
					 type1 type2)))))
       (const-substitute const tsubst #f)))
    x y)))

(add-display
 (py "list alpha")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if
	  (and (term-in-const-form? op)
	       (string=? "Cons"
			 (const-to-name (term-in-const-form-to-const op)))
	       (= 2 (length args)))
	  (list 'pair-op  "::"
		(term-to-token-tree (car args))
		(term-to-token-tree (cadr args)))
	  #f))
       #f)))

;; The postfix-op ":" with "x:" for "x::(Nil rho)" needs a special
;; treatment with explicit uses of add-token and add-display.

(add-token
 ":" 'postfix-op
 (lambda (x)
   (mk-term-in-app-form
    (make-term-in-const-form
     (let* ((constr (constr-name-to-constr "Cons"))
	    (tvars (const-to-tvars constr))
	    (subst (make-substitution tvars (list (term-to-type x)))))
       (const-substitute constr subst #f)))
    x
    (make-term-in-const-form
     (let* ((constr (constr-name-to-constr "Nil"))
	    (tvars (const-to-tvars constr))
	    (subst (make-substitution tvars (list (term-to-type x)))))
       (const-substitute constr subst #f))))))

(add-display
 (py "list alpha")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "Cons" (const-to-name
				    (term-in-const-form-to-const op)))
		  (= 2 (length args))
		  (term-in-const-form? (cadr args))
		  (string=? "Nil" (const-to-name
				   (term-in-const-form-to-const (cadr args)))))
	     (list 'postfix-op ":" (term-to-token-tree (car args)))
	     #f))
       #f)))

;; We collect definitions and properties of TotalList and EqPList,
;; including the Nc, Co and MR variants.  In the present file we only
;; give the definitions.  The (somewhat lengthy) properties are in a
;; separate extension file listext.scm.

;; 1.  Totality
;; 1-1.  Total and CoTotal

;; 1-1-1.  Total
;; 1-1-1-1.  Definitions
;; 1-1-1-1-1.  Definitions of predicates with cterms
;; 1-1-1-1-2.  Definitions of predicates without cterms
;; 1-1-1-2.  Properties
;; 1-1-1-2-1.  Ex falso
;; 1-1-1-2-2.  Monotonicity
;; 1-1-1-2-3.  Connections

;; 1-1-2.  CoTotal
;; 1-1-2-1.  Definitions
;; 1-1-2-2.  Properties
;; 1-1-2-2-1.  Monotonicity
;; 1-1-2-2-2.  Total implies CoTotal
;; 1-1-2-2-3.  Ex falso

;; 1-2.  TotalMR and CoTotalMR

;; 1-2-1.  TotalMR
;; 1-2-1-1.  Definitions
;; 1-2-1-2.  Properties
;; 1-2-1-2-1.  Ex falso
;; 1-2-1-2-2.  Monotonicity
;; 1-2-1-2-3.  Connections

;; 1-2-2.  CoTotalMR
;; 1-2-2-1.  Definitions
;; 1-2-2-2.  Properties
;; 1-2-2-2-1.  Ex falso
;; 1-2-2-2-2.  Monotonicity
;; 1-2-2-2-3.  Total implies CoTotal

;; 2.  Pointwise equality (similar)
;; 2-1.  EqP and CoEqP

;; 2-1-1.  EqP
;; 2-1-1-1.  Definitions
;; 2-1-1-1-1.  Definitions of predicates with cterms
;; 2-1-1-1-2.  Definitions of predicates without cterms
;; 2-1-1-2.  Properties
;; 2-1-1-2-1.  Ex falso
;; 2-1-1-2-2.  Monotonicity
;; 2-1-1-2-3.  EqP implies EqD
;; 2-1-1-2-4.  Symmetry
;; 2-1-1-2-5.  Connections
;; 2-1-1-2-6.  Relations between Total and EqP

;; 2-1-2.  CoEqP
;; 2-1-2-1.  Definitions
;; 2-1-2-2.  Properties
;; 2-1-2-2-1.  Monotonicity
;; 2-1-2-2-2.  Symmetry
;; 2-1-2-2-3.  EqPList implies CoEqPList, Ex falso
;; 2-1-2-2-4.  Relations between CoTotal and CoEqP

;; 2-2.  EqPMR and CoEqPMR

;; 2-2-1.  EqPMR
;; 2-2-1-1.  Definitions
;; 2-2-1-2.  Properties
;; 2-2-1-2-1.  Ex falso
;; 2-2-1-2-2.  Monotonicity
;; 2-2-1-2-3.  Connections

;; 2-2-2.  CoEqPMR
;; 2-2-2-1.  Definitions
;; 2-2-2-2.  Properties
;; 2-2-2-2-1.  Ex falso
;; 2-2-2-2-2.  Monotonicity
;; 2-2-2-2-3.  Total implies CoTotal

;; 3.  ListNat, ListBoole

;; 1.  Totality
;; ============

;; 1-1.  Total and CoTotal
;; =======================

;; 1-1-1.  Total
;; =============

;; 1-1-1-1.  Definitions
;; =====================

;; 1-1-1-1-1.  Definitions of predicates with cterms
;; =================================================

;; RTotalList (R: c.r.)      \typeL{\alpha}
;; NTotalList (N: n.c.)      \typeN
;; RTotalListNc              --

(add-ids
 (list (list "RTotalList" (make-arity (py "list alpha")) "list"))
 '("RTotalList (Nil alpha)" "RTotalListNil")
 '("allnc x^((Pvar alpha)x^ -> allnc xs^(RTotalList xs^ ->
    RTotalList(x^ ::xs^)))"
   "RTotalListCons"))

(pp "RTotalListNil")
;; (RTotalList (cterm (x^) (Pvar alpha)x^))(Nil alpha)

(pp "RTotalListCons")

;; allnc x^(
;;  (Pvar alpha)x^ -> 
;;  allnc xs^(
;;   (RTotalList (cterm (x^0) (Pvar alpha)x^0))xs^ -> 
;;   (RTotalList (cterm (x^0) (Pvar alpha)x^0))(x^ ::xs^)))

(add-ids
 (list (list "NTotalList" (make-arity (py "list alpha")) "nat"))
 '("NTotalList (Nil alpha)" "NTotalListNil")
 '("allnc x^((Pvar alpha)^ x^ -> allnc xs^(NTotalList xs^ ->
    NTotalList (x^ ::xs^)))"
   "NTotalListCons"))

(pp "NTotalListNil")
;; (NTotalList (cterm (x^) (Pvar alpha)^ x^))(Nil alpha)

(pp "NTotalListCons")

;; allnc x^(
;;  (Pvar alpha)^ x^ -> 
;;  allnc xs^(
;;   (NTotalList (cterm (x^0) (Pvar alpha)^ x^0))xs^ -> 
;;   (NTotalList (cterm (x^0) (Pvar alpha)^ x^0))(x^ ::xs^)))

(add-ids
 (list (list "RTotalListNc" (make-arity (py "list alpha"))))
 '("RTotalListNc (Nil alpha)" "RTotalListNcNil")
 '("allnc x^((Pvar alpha)^ x^ -> allnc xs^(RTotalListNc xs^ ->
    RTotalListNc(x^ ::xs^)))"
  "RTotalListNcCons"))
 
(pp "RTotalListNcNil")
;; (RTotalListNc (cterm (x^) (Pvar alpha)^ x^))(Nil alpha)

(pp "RTotalListNcCons")

;; allnc x^(
;;  (Pvar alpha)^ x^ -> 
;;  allnc xs^(
;;   (RTotalListNc (cterm (x^0) (Pvar alpha)^ x^0))xs^ -> 
;;   (RTotalListNc (cterm (x^0) (Pvar alpha)^ x^0))(x^ ::xs^)))

;; 1-1-1-1-2.  Definitions of predicates without cterms
;; ====================================================

;; TotalList                 \typeL{\alpha} (Y^c  -> Total predconst)
;; ANTotalList (A: absolute) \typeN         (Y^nc -> TotalNc predconst)
;; STotalList                \typeN         (Y^nc -> {x|T})
;; TotalListNc               --             (Y^nc -> TotalNc predconst)
;; STotalListNc              --             (Y^nc -> {x|T})

(add-totality "list")

(pp "TotalListNil")
;; TotalList(Nil alpha)

(pp "TotalListCons")
;; allnc x^(Total x^ -> allnc xs^(TotalList xs^ -> TotalList(x^ ::xs^)))

(add-ids
 (list (list "ANTotalList" (make-arity (py "list alpha")) "nat"))
 '("ANTotalList(Nil alpha)" "ANTotalListNil")
 '("allnc x^(TotalNc x^ -> allnc xs^(ANTotalList xs^ ->
    ANTotalList(x^ ::xs^)))"
   "ANTotalListCons"))

(pp "ANTotalListNil")
;; ANTotalList(Nil alpha)

(pp "ANTotalListCons")
;; allnc x^(TotalNc x^ -> allnc xs^(ANTotalList xs^ -> ANTotalList(x^ ::xs^)))

(add-ids (list (list "STotalList" (make-arity (py "list alpha")) "nat"))
	 '("STotalList(Nil alpha)" "STotalListNil")
	 '("allnc x^,xs^(
             STotalList xs^ -> STotalList(x^ ::xs^))" "STotalListCons"))

(pp "STotalListNil")
;; STotalList(Nil alpha)

(pp "STotalListCons")
;; allnc x^,xs^(STotalList xs^ -> STotalList(x^ ::xs^))

;; We could use (RTotalList (cterm (x^) T))xs^ for STotalList xs^.
;; However, STotalList is just convenient.

(add-totalnc "list")

(pp "TotalListNcNil")
;; TotalListNc(Nil alpha)

(pp "TotalListNcCons")
;; allnc x^(TotalNc x^ -> allnc xs^(TotalListNc xs^ -> TotalListNc(x^ ::xs^)))

(add-ids (list (list "STotalListNc" (make-arity (py "list alpha"))))
	 '("STotalListNc(Nil alpha)" "STotalListNcNil")
	 '("allnc x^,xs^(STotalListNc xs^ -> STotalListNc(x^ ::xs^))"
	   "STotalListNcCons"))

(pp "STotalListNcNil")
;; STotalListNc(Nil alpha)

(pp "STotalListNcCons")
;; allnc x^,xs^(STotalListNc xs^ -> STotalListNc(x^ ::xs^))

;; 1-1-2-1.  Definitions
;; =====================

;; For the 8 variants of TotalList defined in 1-1-1-1 we define their duals

(add-co "RTotalList")
(add-co "NTotalList")
(add-co "RTotalListNc")
(add-co "TotalList")
(add-co "ANTotalList")
(add-co "STotalList")
(add-co "TotalListNc")
(add-co "STotalListNc")

(for-each pp (list
"CoRTotalListClause"
"CoNTotalListClause"
"CoRTotalListNcClause"
"CoTotalListClause"
"CoANTotalListClause"
"CoSTotalListClause"
"CoTotalListNcClause"
"CoSTotalListNcClause"))

;; allnc xs^(
;;  (CoRTotalList (cterm (x^) (Pvar alpha)x^))xs^ -> 
;;  xs^ eqd(Nil alpha) orr 
;;  exr x^(
;;   (Pvar alpha)x^ andd 
;;   exr xs^0(
;;    (CoRTotalList (cterm (x^0) (Pvar alpha)x^0))xs^0 andl
;;    xs^ eqd(x^ ::xs^0))))

;; allnc xs^(
;;  (CoNTotalList (cterm (x^) (Pvar alpha)^ x^))xs^ -> 
;;  xs^ eqd(Nil alpha) orr 
;;  exr x^(
;;   (Pvar alpha)^ x^ andr 
;;   exr xs^0(
;;    (CoNTotalList (cterm (x^0) (Pvar alpha)^ x^0))xs^0 andl
;;    xs^ eqd(x^ ::xs^0))))

;; allnc xs^(
;;  (CoRTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^ -> 
;;  xs^ eqd(Nil alpha) ornc 
;;  exnc x^(
;;   (Pvar alpha)^ x^ andnc 
;;   exnc xs^0(
;;    (CoRTotalListNc (cterm (x^0) (Pvar alpha)^ x^0))xs^0 andnc 
;;    xs^ eqd(x^ ::xs^0))))

;; allnc xs^(
;;  CoTotalList xs^ -> 
;;  xs^ eqd(Nil alpha) orr 
;;  exr x^(Total x^ andd exr xs^0(CoTotalList xs^0 andl xs^ eqd(x^ ::xs^0))))

;; allnc xs^(
;;  CoANTotalList xs^ -> 
;;  xs^ eqd(Nil alpha) orr 
;;  exr x^(
;;   TotalNc x^ andr exr xs^0(CoANTotalList xs^0 andl xs^ eqd(x^ ::xs^0))))

;; allnc xs^(
;;  CoSTotalList xs^ -> 
;;  xs^ eqd(Nil alpha) orr 
;;  exr x^,xs^0(CoSTotalList xs^0 andl xs^ eqd(x^ ::xs^0)))

;; allnc xs^(
;;  CoTotalListNc xs^ -> 
;;  xs^ eqd(Nil alpha) ornc 
;;  exnc x^(
;;   TotalNc x^ andnc exnc xs^0(CoTotalListNc xs^0 andnc xs^ eqd(x^ ::xs^0))))

;; allnc xs^(
;;  CoSTotalListNc xs^ -> 
;;  xs^ eqd(Nil alpha) ornc 
;;  exnc x^,xs^0(CoSTotalListNc xs^0 andnc xs^ eqd(x^ ::xs^0)))

;; 1-2-1-1.  Definitions
;; =====================

;; RTotalListMR
;; NTotalListMR
;; TotalListMR
;; ANTotalListMR
;; STotalListMR

(add-mr-ids "RTotalList")

(pp "RTotalListNilMR")
;; (RTotalListMR (cterm (x^,gamma^) (Pvar alpha gamma)^ x^ gamma^))(Nil alpha)
;; (Nil gamma)

(pp "RTotalListConsMR")

;; allnc x^,gamma^(
;;  (Pvar alpha gamma)^ x^ gamma^ -> 
;;  allnc xs^,(list gamma)^0(
;;   (RTotalListMR (cterm (x^0,gamma^1) (Pvar alpha gamma)^ x^0 gamma^1))xs^
;;   (list gamma)^0 -> 
;;   (RTotalListMR (cterm (x^0,gamma^1) (Pvar alpha gamma)^ x^0 gamma^1))
;;   (x^ ::xs^)
;;   (gamma^ ::(list gamma)^0)))

(add-mr-ids "NTotalList")

(pp "NTotalListNilMR")
;; (NTotalListMR (cterm (x^) (Pvar alpha)^ x^))(Nil alpha)0

(pp "NTotalListConsMR")

;; allnc x^(
;;  (Pvar alpha)^ x^ -> 
;;  allnc xs^,n^(
;;   (NTotalListMR (cterm (x^0) (Pvar alpha)^ x^0))xs^ n^ -> 
;;   (NTotalListMR (cterm (x^0) (Pvar alpha)^ x^0))(x^ ::xs^)(Succ n^)))

(add-mr-ids "TotalList")

(pp "TotalListNilMR")
;; TotalListMR(Nil alpha)(Nil alpha)

(pp "TotalListConsMR")

;; allnc x^,x^0(
;;  TotalMR x^ x^0 -> 
;;  allnc xs^,xs^0(TotalListMR xs^ xs^0 -> TotalListMR(x^ ::xs^)(x^0::xs^0)))

(add-mr-ids "ANTotalList")

(pp "ANTotalListNilMR")
;; ANTotalListMR(Nil alpha)0

(pp "ANTotalListConsMR")
;; allnc x^(
;;  TotalNc x^ -> 
;;  allnc xs^,n^(ANTotalListMR xs^ n^ -> ANTotalListMR(x^ ::xs^)(Succ n^)))

(add-mr-ids "STotalList")

(pp "STotalListNilMR")
;; STotalListMR(Nil alpha)0

(pp "STotalListConsMR")
;; allnc x^,xs^,n^(STotalListMR xs^ n^ -> STotalListMR(x^ ::xs^)(Succ n^))

;; 1-2-2-1.  Definitions
;; =====================

;; CoRTotalListMR
;; CoNTotalListMR
;; CoTotalListMR
;; CoANTotalListMR
;; CoSTotalListMR

(add-co "RTotalListMR")

(pp "CoRTotalListMRClause")

;; allnc xs^,(list gamma)^(
;;  (CoRTotalListMR (cterm (x^,gamma^0) (Pvar alpha gamma)^ x^ gamma^0))xs^
;;  (list gamma)^ -> 
;;  xs^ eqd(Nil alpha) andnc (list gamma)^ eqd(Nil gamma) ornc 
;;  exnc x^,gamma^0(
;;   (Pvar alpha gamma)^ x^ gamma^0 andnc 
;;   exnc xs^0,(list gamma)^1(
;;    (CoRTotalListMR (cterm (x^0,gamma^2) (Pvar alpha gamma)^ x^0 gamma^2))xs^0
;;    (list gamma)^1 andnc 
;;    xs^ eqd(x^ ::xs^0) andnc (list gamma)^ eqd(gamma^0::(list gamma)^1))))

(add-co "NTotalListMR")

(pp "CoNTotalListMRClause")

;; allnc xs^,n^(
;;  (CoNTotalListMR (cterm (x^) (Pvar alpha)^ x^))xs^ n^ -> 
;;  xs^ eqd(Nil alpha) andnc n^ eqd 0 ornc 
;;  exnc x^(
;;   (Pvar alpha)^ x^ andnc 
;;   exnc xs^0,n^0(
;;    (CoNTotalListMR (cterm (x^0) (Pvar alpha)^ x^0))xs^0 n^0 andnc 
;;    xs^ eqd(x^ ::xs^0) andnc n^ eqd Succ n^0)))

(add-co "TotalListMR")

(pp "CoTotalListMRClause")

;; allnc xs^,xs^0(
;;  CoTotalListMR xs^ xs^0 -> 
;;  xs^ eqd(Nil alpha) andnc xs^0 eqd(Nil alpha) ornc 
;;  exnc x^,x^0(
;;   TotalMR x^ x^0 andnc 
;;   exnc xs^1,xs^2(
;;    CoTotalListMR xs^1 xs^2 andnc 
;;    xs^ eqd(x^ ::xs^1) andnc xs^0 eqd(x^0::xs^2))))

(add-co "ANTotalListMR")

(pp "CoANTotalListMRClause")

;; allnc xs^,n^(
;;  CoANTotalListMR xs^ n^ -> 
;;  xs^ eqd(Nil alpha) andnc n^ eqd 0 ornc 
;;  exnc x^(
;;   TotalNc x^ andnc 
;;   exnc xs^0,n^0(
;;    CoANTotalListMR xs^0 n^0 andnc xs^ eqd(x^ ::xs^0) andnc n^ eqd Succ n^0)))

(add-co "STotalListMR")

(pp "CoSTotalListMRClause")

;; allnc xs^,n^(
;;  CoSTotalListMR xs^ n^ -> 
;;  xs^ eqd(Nil alpha) andnc n^ eqd 0 ornc 
;;  exnc x^,xs^0,n^0(
;;   CoSTotalListMR xs^0 n^0 andnc xs^ eqd(x^ ::xs^0) andnc n^ eqd Succ n^0))

;; 2-1-1-1.  Definitions
;; =====================

;; 2-1-1-1-1.  Definitions of predicates with cterms
;; =================================================

;; REqPList (R: c.r.)      \typeL{\alpha}
;; NEqPList (N: n.c.)      \typeN
;; REqPListNc              --

(add-ids
 (list
  (list "REqPList" (make-arity (py "list alpha") (py "list alpha")) "list"))
 '("REqPList(Nil alpha)(Nil alpha)" "REqPListNil")
 '("allnc x^1,x^2((Pvar alpha alpha)x^1 x^2 ->
    allnc xs^1,xs^2(REqPList xs^1 xs^2 -> REqPList(x^1 ::xs^1)(x^2 ::xs^2)))"
   "REqPListCons"))

(pp "REqPListNil")
;; (REqPList (cterm (x^,x^0) (Pvar alpha alpha)x^ x^0))(Nil alpha)(Nil alpha)

(pp "REqPListCons")

;; allnc x^,x^0(
;;  (Pvar alpha alpha)x^ x^0 -> 
;;  allnc xs^,xs^0(
;;   (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^ xs^0 -> 
;;   (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))
;;    (x^ ::xs^)(x^0::xs^0)))

(add-ids
 (list
  (list "NEqPList" (make-arity (py "list alpha") (py "list alpha")) "nat"))
 '("NEqPList(Nil alpha)(Nil alpha)" "NEqPListNil")
 '("allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 ->
    allnc xs^1,xs^2(NEqPList xs^1 xs^2 -> NEqPList(x^1 ::xs^1)(x^2 ::xs^2)))"
   "NEqPListCons"))

(pp "NEqPListNil")
;; (NEqPList (cterm (x^,x^0) (Pvar alpha alpha)^ x^ x^0))(Nil alpha)(Nil alpha)

(pp "NEqPListCons")

;; allnc x^,x^0(
;;  (Pvar alpha alpha)^ x^ x^0 -> 
;;  allnc xs^,xs^0(
;;   (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^ xs^0 -> 
;;   (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))(x^ ::xs^)
;;   (x^0::xs^0)))

(add-ids
 (list
  (list "REqPListNc" (make-arity (py "list alpha") (py "list alpha"))))
 '("REqPListNc(Nil alpha)(Nil alpha)" "REqPListNcNil")
 '("allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 ->
    allnc xs^1,xs^2(REqPListNc xs^1 xs^2 ->
                    REqPListNc(x^1 ::xs^1)(x^2 ::xs^2)))"
   "REqPListNcCons"))

(pp "REqPListNcNil")

;; (REqPListNc (cterm (x^,x^0) (Pvar alpha alpha)^ x^ x^0))(Nil alpha)
;; (Nil alpha)

(pp "REqPListNcCons")

;; allnc x^,x^0(
;;  (Pvar alpha alpha)^ x^ x^0 -> 
;;  allnc xs^,xs^0(
;;   (REqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^ xs^0 -> 
;;   (REqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))(x^ ::xs^)
;;   (x^0::xs^0)))

;; 2-1-1-1-2.  Definitions of predicates without cterms
;; ====================================================

;; EqPList                 \typeL{\alpha} (Y^c  -> EqP predconst)
;; ANEqPList (A: absolute) \typeN         (Y^nc -> EqPNc predconst)
;; SEqPList                \typeN         (Y^nc -> {x,y|T})
;; EqPListNc               --             (Y^nc -> EqPNc predconst)
;; SEqPListNc              --             (Y^nc -> {x,y|T})

(add-eqp "list")

(pp "EqPListNil")
;; EqPList(Nil alpha)(Nil alpha)

(pp "EqPListCons")

;; allnc x^,x^0(
;;  EqP x^ x^0 -> 
;;  allnc xs^,xs^0(EqPList xs^ xs^0 -> EqPList(x^ ::xs^)(x^0::xs^0)))

(add-ids
 (list
  (list "ANEqPList" (make-arity (py "list alpha") (py "list alpha")) "nat"))
 '("ANEqPList(Nil alpha)(Nil alpha)" "ANEqPListNil")
 '("allnc x^1,x^2(EqPNc x^1 x^2 -> allnc xs^1,xs^2(ANEqPList xs^1 xs^2 ->
    ANEqPList(x^1 ::xs^1)(x^2 ::xs^2)))"
   "ANEqPListCons"))

(pp "ANEqPListNil")
;; ANEqPList(Nil alpha)(Nil alpha)

(pp "ANEqPListCons")

;; allnc x^,x^0(
;;  EqPNc x^ x^0 -> 
;;  allnc xs^,xs^0(ANEqPList xs^ xs^0 -> ANEqPList(x^ ::xs^)(x^0::xs^0)))

(add-ids
 (list
  (list "SEqPList" (make-arity (py "list alpha") (py "list alpha")) "nat"))
 '("SEqPList(Nil alpha)(Nil alpha)" "SEqPListNil")
 '("allnc x^1,x^2,xs^1,xs^2(
     SEqPList xs^1 xs^2 -> SEqPList(x^1 ::xs^1)(x^2 ::xs^2))" "SEqPListCons"))

(pp "SEqPListNil")
;; SEqPList(Nil alpha)(Nil alpha)

(pp "SEqPListCons")
;; allnc x^,x^0,xs^,xs^0(SEqPList xs^ xs^0 -> SEqPList(x^ ::xs^)(x^0::xs^0))

;; We could use (REqPList (cterm (x^1,x^2) T))xs^1 xs^2 for
;;  SEqPList xs^.1 xs^2 

(add-eqpnc "list")

(pp "EqPListNcNil")
;; EqPListNc(Nil alpha)(Nil alpha)

(pp "EqPListNcCons")

;; allnc x^,x^0(
;;  EqPNc x^ x^0 -> 
;;  allnc xs^,xs^0(EqPListNc xs^ xs^0 -> EqPListNc(x^ ::xs^)(x^0::xs^0)))


(add-ids
 (list
  (list "SEqPListNc" (make-arity (py "list alpha") (py "list alpha"))))
 '("SEqPListNc(Nil alpha)(Nil alpha)" "SEqPListNcNil")
 '("allnc x^1,x^2,xs^1,xs^2(
    SEqPListNc xs^1 xs^2 -> SEqPListNc(x^1 ::xs^1)(x^2 ::xs^2))"
   "SEqPListNcCons"))

(pp "SEqPListNcNil")
;; SEqPListNc(Nil alpha)(Nil alpha)

(pp "SEqPListNcCons")

;; allnc x^,x^0,xs^,xs^0(
;;  SEqPListNc xs^ xs^0 -> SEqPListNc(x^ ::xs^)(x^0::xs^0))

;; 2-1-2-1.  Definitions
;; =====================

;; For the 8 variants of EqPList defined in 2-1-1-1 we define their duals

(add-co "REqPList")
(add-co "NEqPList")
(add-co "REqPListNc")
(add-co "EqPList")
(add-co "ANEqPList")
(add-co "SEqPList")
(add-co "EqPListNc")
(add-co "SEqPListNc")

(for-each pp (list
"CoREqPListClause"
"CoNEqPListClause"
"CoREqPListNcClause"
"CoEqPListClause"
"CoANEqPListClause"
"CoSEqPListClause"
"CoEqPListNcClause"
"CoSEqPListNcClause"))

;; 2-2-1-1.  Definitions
;; =====================

;; For simplicity we only consider MR-variants of idpcs without cterms

(add-mr-ids "REqPList")

(pp "REqPListNilMR")

;; (REqPListMR (cterm (x^,x^0,alpha700^) 
;;               (Pvar alpha alpha alpha700)^403 x^ x^0 alpha700^))
;; (Nil alpha)
;; (Nil alpha)
;; (Nil alpha700)

(pp "REqPListConsMR")

;; allnc x^,x^0,alpha700^(
;;  (Pvar alpha alpha alpha700)^403 x^ x^0 alpha700^ -> 
;;  allnc xs^,xs^0,(list alpha700)^0(
;;   (REqPListMR (cterm (x^1,x^2,alpha700^1) 
;;                 (Pvar alpha alpha alpha700)^403 x^1 x^2 alpha700^1))
;;   xs^ 
;;   xs^0
;;   (list alpha700)^0 -> 
;;   (REqPListMR (cterm (x^1,x^2,alpha700^1) 
;;                 (Pvar alpha alpha alpha700)^403 x^1 x^2 alpha700^1))
;;   (x^ ::xs^)
;;   (x^0::xs^0)
;;   (alpha700^ ::(list alpha700)^0)))

(add-mr-ids "NEqPList")

(pp "NEqPListNilMR")

;; (NEqPListMR (cterm (x^,x^0) (Pvar alpha alpha)^ x^ x^0))(Nil alpha)
;; (Nil alpha)
;; 0

(pp "NEqPListConsMR")

;; allnc x^,x^0(
;;  (Pvar alpha alpha)^ x^ x^0 -> 
;;  allnc xs^,xs^0,n^(
;;   (NEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^ xs^0 n^ -> 
;;   (NEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))(x^ ::xs^)
;;   (x^0::xs^0)
;;   (Succ n^)))

(add-mr-ids "EqPList")

(pp "EqPListNilMR")
;; EqPListMR(Nil alpha)(Nil alpha)(Nil alpha)

(pp "EqPListConsMR")

;; allnc x^,x^0,x^1(
;;  EqPMR x^ x^0 x^1 -> 
;;  allnc xs^,xs^0,xs^1(
;;   EqPListMR xs^ xs^0 xs^1 -> EqPListMR(x^ ::xs^)(x^0::xs^0)(x^1::xs^1)))

(add-mr-ids "ANEqPList")

(pp "ANEqPListNilMR")
;; ANEqPListMR(Nil alpha)(Nil alpha)0

(pp "ANEqPListConsMR")

;; allnc x^,x^0(
;;  EqPNc x^ x^0 -> 
;;  allnc xs^,xs^0,n^(
;;   ANEqPListMR xs^ xs^0 n^ -> ANEqPListMR(x^ ::xs^)(x^0::xs^0)(Succ n^)))

(add-mr-ids "SEqPList")

(pp "SEqPListNilMR")
;; SEqPListMR(Nil alpha)(Nil alpha)0

(pp "SEqPListConsMR")

;; allnc x^,x^0,xs^,xs^0,n^(
;;  SEqPListMR xs^ xs^0 n^ -> SEqPListMR(x^ ::xs^)(x^0::xs^0)(Succ n^))

;; 2-2-2-1.  Definitions
;; =====================

;; CoREqPListMR
;; CoNEqPListMR
;; CoEqPListMR
;; CoANEqPListMR
;; CoSEqPListMR

(add-co "REqPListMR")

(pp "CoREqPListMRClause")

;; allnc xs^,xs^0,(list alpha768)^(
;;  (CoREqPListMR (cterm (x^,x^0,alpha768^0) 
;;                  (Pvar alpha alpha alpha768)^404 x^ x^0 alpha768^0))
;;  xs^ 
;;  xs^0
;;  (list alpha768)^ -> 
;;  xs^ eqd(Nil alpha) andnc 
;;  xs^0 eqd(Nil alpha) andnc (list alpha768)^ eqd(Nil alpha768) ornc 
;;  exnc x^,x^0,alpha768^0(
;;   (Pvar alpha alpha alpha768)^404 x^ x^0 alpha768^0 andnc 
;;   exnc xs^1,xs^2,(list alpha768)^1(
;;    (CoREqPListMR (cterm (x^1,x^2,alpha768^2) 
;;                    (Pvar alpha alpha alpha768)^404 x^1 x^2 alpha768^2))
;;    xs^1 
;;    xs^2
;;    (list alpha768)^1 andnc 
;;    xs^ eqd(x^ ::xs^1) andnc 
;;    xs^0 eqd(x^0::xs^2) andnc 
;;    (list alpha768)^ eqd(alpha768^0::(list alpha768)^1))))

(add-co "NEqPListMR")

(pp "CoNEqPListMRClause")

;; allnc xs^,xs^0,n^(
;;  (CoNEqPListMR (cterm (x^,x^0) (Pvar alpha alpha)^ x^ x^0))xs^ xs^0 n^ -> 
;;  xs^ eqd(Nil alpha) andnc xs^0 eqd(Nil alpha) andnc n^ eqd 0 ornc 
;;  exnc x^,x^0(
;;   (Pvar alpha alpha)^ x^ x^0 andnc 
;;   exnc xs^1,xs^2,n^0(
;;    (CoNEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2 n^0
;;  andnc 
;;    xs^ eqd(x^ ::xs^1) andnc xs^0 eqd(x^0::xs^2) andnc n^ eqd Succ n^0)))

(add-co "EqPListMR")

(pp "CoEqPListMRClause")

;; allnc xs^,xs^0,xs^1(
;;  CoEqPListMR xs^ xs^0 xs^1 -> 
;;  xs^ eqd(Nil alpha) andnc xs^0 eqd(Nil alpha) andnc xs^1 eqd(Nil alpha) ornc 
;;  exnc x^,x^0,x^1(
;;   EqPMR x^ x^0 x^1 andnc 
;;   exnc xs^2,xs^3,xs^4(
;;    CoEqPListMR xs^2 xs^3 xs^4 andnc 
;;    xs^ eqd(x^ ::xs^2) andnc xs^0 eqd(x^0::xs^3) andnc xs^1 eqd(x^1::xs^4))))

(add-co "ANEqPListMR")

(pp "CoANEqPListMRClause")

;; allnc xs^,xs^0,n^(
;;  CoANEqPListMR xs^ xs^0 n^ -> 
;;  xs^ eqd(Nil alpha) andnc xs^0 eqd(Nil alpha) andnc n^ eqd 0 ornc 
;;  exnc x^,x^0(
;;   EqPNc x^ x^0 andnc 
;;   exnc xs^1,xs^2,n^0(
;;    CoANEqPListMR xs^1 xs^2 n^0 andnc 
;;    xs^ eqd(x^ ::xs^1) andnc xs^0 eqd(x^0::xs^2) andnc n^ eqd Succ n^0)))

(add-co "SEqPListMR")

(pp "CoSEqPListMRClause")

;; allnc xs^,xs^0,n^(
;;  CoSEqPListMR xs^ xs^0 n^ -> 
;;  xs^ eqd(Nil alpha) andnc xs^0 eqd(Nil alpha) andnc n^ eqd 0 ornc 
;;  exnc x^,x^0,xs^1,xs^2,n^0(
;;   CoSEqPListMR xs^1 xs^2 n^0 andnc 
;;   xs^ eqd(x^ ::xs^1) andnc xs^0 eqd(x^0::xs^2) andnc n^ eqd Succ n^0))

;; 3.  ListNat, ListBoole
;; ======================

(add-var-name "ns" (py "list nat"))

;; ListNatEqToEqD
(set-goal "all ns1,ns2(ns1=ns2 -> ns1 eqd ns2)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "n1" "ns1" "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n1" "ns1" "IH")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n2" "ns2" "n1::ns1=n2::ns2")
(ng)
(inst-with-to "n1::ns1=n2::ns2" 'right "ns1=ns2")
(inst-with-to "n1::ns1=n2::ns2" 'left "n1=n2")
(drop "n1::ns1=n2::ns2")
(assert "ns1 eqd ns2")
 (use "IH")
 (use "ns1=ns2")
(assume "ns1 eqd ns2")
(assert "n1 eqd n2")
 (use "NatEqToEqD")
 (use "n1=n2")
(assume "n1 eqd n2")
(elim "ns1 eqd ns2")
(assume "ns^3")
(elim "n1 eqd n2")
(assume "n^3")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListNatEqToEqD")

;; ListNatEqTotal
(set-goal "allnc ns^1(TotalList ns^1 -> allnc ns^2(TotalList ns^2 ->
 TotalBoole(ns^1 =ns^2)))")
(assume "ns^1" "Tns1")
(elim "Tns1")
(assume "ns^2" "Tns2")
(elim "Tns2")
(use "TotalBooleTrue")
(strip)
(use "TotalBooleFalse")
(assume "n^3" "Tn3" "ns^3" "Tns3" "IHns3" "ns^4" "Tns4")
(elim "Tns4")
(use "TotalBooleFalse")
(assume "n^5" "Tn5" "ns^5" "Tns5" "Useless")
(ng #t)
(use "AndConstTotal")
(use "NatEqTotal")
(use "Tn3")
(use "Tn5")
(use "IHns3")
(use "Tns5")
;; Proof finished.
;; (cdp)
(save "ListNatEqTotal")

(add-var-name "p" (py "boole"))
(add-var-name "ps" (py "list boole"))

;; ListBooleEqToEqD
(set-goal "all ps1,ps2(ps1=ps2 -> ps1 eqd ps2)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "p1" "ps1" "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "p1" "ps1" "IH")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "p2" "ps2" "p1::ps1=p2::ps2")
(ng)
(inst-with-to "p1::ps1=p2::ps2" 'right "ps1=ps2")
(inst-with-to "p1::ps1=p2::ps2" 'left "p1=p2")
(drop "p1::ps1=p2::ps2")
(assert "ps1 eqd ps2")
 (use "IH")
 (use "ps1=ps2")
(assume "ps1 eqd ps2")
(assert "p1 eqd p2")
 (use "BooleEqToEqD")
 (use "p1=p2")
(assume "p1 eqd p2")
(elim "ps1 eqd ps2")
(assume "ps^3")
(elim "p1 eqd p2")
(assume "p^3")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListBooleEqToEqD")

;; ListBooleEqTotal
(set-goal "allnc ps^1(TotalList ps^1 -> allnc ps^2(TotalList ps^2 ->
 TotalBoole(ps^1 =ps^2)))")
(assume "ps^1" "Tps1")
(elim "Tps1")
(assume "ps^2" "Tps2")
(elim "Tps2")
(use "TotalBooleTrue")
(strip)
(use "TotalBooleFalse")
(assume "boole^3" "Tp3" "ps^3" "Tps3" "IHps3" "ps^4" "Tps4")
(elim "Tps4")
(use "TotalBooleFalse")
(assume "boole^5" "Tp5" "ps^5" "Tps5" "Useless")
(ng #t)
(use "AndConstTotal")
(use "BooleEqTotal")
(use "Tp3")
(use "Tp5")
(use "IHps3")
(use "Tps5")
;; Proof finished.
;; (cdp)
(save "ListBooleEqTotal")

;; This concludes the collection of properties of TotalList and
;; EqPList.  For faster loading: only keep the definitions and move
;; the rest into a lib file called listeqp.scm.

;; ListTotalVar
(set-goal "all xs TotalList xs")
(use "AllTotalIntro")
(assume "xs^" "Txs")
(use "Txs")
;; Proof finished.
;; (cdp)
(save "ListTotalVar")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [xs]xs

;; ListSTotalVar
(set-goal "all xs STotalList xs")
(use "AllTotalIntro")
(assume "xs^" "Txs")
(elim "Txs")
(use "STotalListNil")
(assume "x^" "Tx" "xs^0" "Txs0" "STxs0")
(use "STotalListCons")
(use "STxs0")
;; Proof finished.
;; (cdp)
(save "ListSTotalVar")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [xs](Rec list alpha=>nat)xs 0([x,xs0]Succ)

;; ListTotalToSTotal
(set-goal "allnc xs^(TotalList xs^ -> STotalList xs^)")
(assume "xs^" "Txs")
(elim "Txs")
;; 3,4
(use "STotalListNil")
;; 4
(assume "x^" "Tx" "xs^1" "Txs1" "STxs1")
(use "STotalListCons")
(use "STxs1")
;; Proof finished.
;; (cdp)
(save "ListTotalToSTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [xs](Rec list alpha=>nat)xs 0([x,xs0]Succ)

(add-program-constant
 "ListAppend" (py "list alpha=>list alpha=>list alpha") t-deg-zero 'const 1)

(add-infix-display-string "ListAppend" ":+:" 'mul-op)

(add-computation-rules
 "(ListAppend alpha)(Nil alpha)" "[xs]xs"
 "(ListAppend alpha)(x::xs1)" "[xs2](x::xs1:+:xs2)")

(set-totality-goal "ListAppend")
(assume "xs^1" "Txs1" "xs^2" "Txs2")
(elim "Txs1")
(ng #t)
(use "Txs2")
(assume "x^" "Tx" "xs^3" "Txs3" "IH")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

;; 2017-04-01.  Code preliminarily discarded.
;; ;; ListAppendTotalReal
;; (set-goal (real-and-formula-to-mr-formula
;; 	   (pt "(ListAppend alpha)")
;; 	   (proof-to-formula (theorem-name-to-proof "ListAppendTotal"))))
;; (assume "xs^1" "xs^10" "TMRxs10xs1" "xs^2" "xs^20" "TMRxs20xs2")
;; (elim "TMRxs10xs1")
;; (use "TMRxs20xs2")
;; (assume "x^" "x^0" "TMRx0x" "xs^" "xs^0" "TMRxs0xs" "IH")
;; (ng #t)
;; (use "TotalListConsMR")
;; (use "TMRx0x")
;; (use "IH")
;; ;; Proof finished.
;; (save "ListAppendTotalReal")

;; (pp (rename-variables (term-to-stotality-formula (pt "(ListAppend alpha)"))))

;; allnc xs^(
;;  STotalList xs^ -> allnc xs^0(STotalList xs^0 -> STotalList(xs^ :+:xs^0)))

;; ListAppendSTotal
(set-goal
 (rename-variables (term-to-stotality-formula (pt "(ListAppend alpha)"))))
(assume "xs^1" "STxs1" "xs^2" "STxs2")
(elim "STxs1")
(ng #t)
(use "STxs2")
(assume "x^" "xs^3" "STxs3" "IH")
(ng #t)
(use "STotalListCons")
(use "IH")
;; Proof finished.
;; (cdp)
(save "ListAppendSTotal")

;; (pp (rename-variables (proof-to-extracted-term "ListAppendSTotal")))
;; [n,n0](Rec nat=>nat)n n0([n1,n2]Succ n2)

;; ListAppendNil
(set-goal "all xs xs:+:(Nil alpha)eqd xs")
(ind)
(use "InitEqD")
(assume "x" "xs" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListAppendNil")

;; ListAppendNilPartial
(set-goal "allnc xs^(STotalList xs^ -> xs^ :+:(Nil alpha)eqd xs^)")
(assume "xs^" "STxs")
(elim "STxs")
(use "InitEqD")
(assume "x^" "xs^1" "STxs1" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListAppendNilPartial")

;; This is not added as a rewrite rule, because ListAppend is defined
;; by recursion over the first argument and expects rules of arity 1.

;; We also provide a variant ListAppd of ListAppend (with display ++),
;; which allows rewrite rules with two arguments.

(add-program-constant
 "ListAppd" (py "list alpha=>list alpha=>list alpha") t-deg-zero)

(add-infix-display-string "ListAppd" "++" 'mul-op)

(add-computation-rules
 "(Nil alpha)++xs2" "xs2"
 "(x1::xs1)++xs2" "x1::xs1++xs2")

(set-totality-goal "ListAppd")
(assume "xs^1" "Txs1" "xs^2" "Txs2")
(elim "Txs1")
(ng #t)
(use "Txs2")
(assume "x^" "Tx" "xs^3" "Txs3" "IH")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

;; (pp (rename-variables (term-to-stotality-formula (pt "(ListAppd alpha)"))))

;; allnc xs^(
;;  STotalList xs^ -> allnc xs^0(STotalList xs^0 -> STotalList(xs^ ++xs^0)))

;; ListAppdSTotal
(set-goal (rename-variables
	   (term-to-stotality-formula (pt "(ListAppd alpha)"))))
(assume "xs^1" "STxs1" "xs^2" "STxs2")
(elim "STxs1")
(ng #t)
(use "STxs2")
(assume "x^" "xs^3" "STxs3" "IH")
(ng #t)
(use "STotalListCons")
(use "IH")
;; Proof finished.
;; (cdp)
(save "ListAppdSTotal")

;; x: ++xs converts into x::xs.  However, xs1++x2: ++xs2 does not rewrite,
;; because ++ associates to the left.  But we can add the corresponding
;; rule:

(set-goal "all xs1 allnc x^2,xs^2 xs1++x^2: ++xs^2 eqd xs1++(x^2::xs^2)")
(ind)
(assume "x^2" "xs^2")
(use "InitEqD")
(assume "x" "xs1" "IHxs1" "x^2" "xs^2")
(ng)
(simp "IHxs1")
(use "InitEqD")
;; Proof finished.
;; (cdp)

(add-rewrite-rule "xs1++x^2: ++xs^2" "xs1++(x^2::xs^2)")

;; In the other direction this rule would lead to non-termination, if
;; we also had associativity as a rewrite rule.  x2: is x2::(Nil par),
;; and this again is a redex for associativity.

(set-goal "all xs xs++(Nil alpha)eqd xs")
(ind)
(use "InitEqD")
(assume "x" "xs" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "xs++(Nil alpha)" "xs")

;; ListAppdNilPartial
(set-goal "allnc xs^(STotalList xs^ -> xs^ ++(Nil alpha)eqd xs^)")
(assume "xs^" "STxs")
(elim "STxs")
(use "InitEqD")
(assume "x^" "xs^1" "STxs1" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListAppdNilPartial")

;; ListAppdAssoc
(set-goal "all xs1,xs2,xs3 xs1++(xs2++xs3)eqd xs1++xs2++xs3")
(ind)
(assume "xs2" "xs3")
(use "InitEqD")
(assume "x1" "xs1" "IH")
(ng)
(assume "xs2" "xs3")
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListAppdAssoc")

;; ListAppdAssocPartial
(set-goal "allnc xs^1(STotalList xs^1 ->
  allnc xs^2,xs^3 xs^1++(xs^2++xs^3)eqd xs^1++xs^2++xs^3)")
(assume "xs^1" "STxs1")
(elim "STxs1")
(assume "xs^2" "xs^3")
(use "InitEqD")
(assume "x^" "xs^" "STxs" "IH")
(ng #t)
(assume "xs^2" "xs^3")
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListAppdAssocPartial")

;; We could add associativity as a rewrite rule by executing
;; (add-rewrite-rule "xs1++(xs2++xs3)" "xs1++xs2++xs3")

;; However, this will block other rewriting rules in long appends.
;; Example: consider (pt "s++(L::t++R:)") and (pt "s++(L::t)++R:").
;; Both are normal, since rewriting (pt "(L::t)++R:") into (pt
;; "L::t++R:") is blocked by the leading s++ and the fact that ++
;; associates to the left.

(add-program-constant "ListLength" (py "list alpha=>nat") t-deg-zero)
;; (add-prefix-display-string "ListLength" "Lh")
(add-token
 "Lh" 'prefix-op
 (lambda (x)
   (make-term-in-app-form
    (make-term-in-const-form
     (let* ((const (pconst-name-to-pconst "ListLength"))
	    (uninst-type (const-to-uninst-type const))
	    (pattern (arrow-form-to-arg-type uninst-type))
	    (instance (term-to-type x))
	    (tsubst (type-match pattern instance)))
       (if tsubst
	   (const-substitute const tsubst #f)
	   (myerror "types do not match" pattern instance))))
    x)))

(add-display (py "nat") (make-display-creator1 "ListLength" "Lh" 'prefix-op))

;; (add-display
;;  (py "nat")
;;  (lambda (x)
;;    (if (term-in-app-form? x)
;;        (let ((op (term-in-app-form-to-final-op x)))
;; 	 (if
;; 	  (and (term-in-const-form? op)
;; 	       (string=? "ListLength"
;; 			 (const-to-name (term-in-const-form-to-const op))))
;; 	  (list 'prefix-op "Lh"
;; 		(term-to-token-tree (term-in-app-form-to-arg x)))
;; 	  #f))
;;        #f)))

;; (make-display-creator1 "ListLength" "Lh" 'prefix-op)

(add-computation-rules
 "Lh(Nil alpha)" "Zero"
 "Lh(x::xs)" "Succ Lh xs")

(set-totality-goal "ListLength")
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "TotalNatZero")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

;; ListLengthSTotal
(set-goal (rename-variables
	   (term-to-stotality-formula (pt "(ListLength alpha)"))))
(assume "xs^" "STxs")
(elim "STxs")
(ng #t)
(use "TotalNatZero")
(assume "x^" "xs^1" "STxs1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cdp)
(save "ListLengthSTotal")

(pp (rename-variables (proof-to-extracted-term "ListLengthSTotal")))
;; [n](Rec nat=>nat)n 0([n0,n1]Succ n1)

;; ListLhZeroToEqNil
(set-goal "all xs(Lh xs=0 -> xs eqd(Nil alpha))")
(cases)
(assume "Useless")
(use "InitEqD")
(assume "x" "xs" "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "ListLhZeroToEqNil")

;; ListLhZeroToEqNilPartial
(set-goal "allnc xs^(STotalList xs^ -> Lh xs^ =0 -> xs^ eqd(Nil alpha))")
(assume "xs^" "STxs")
(elim "STxs")
(assume "Useless")
(use "InitEqD")
(assume "x^" "xs^1" "STxs1" "IH" "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "ListLhZeroToEqNilPartial")

;; ListLhAppend
(set-goal "all xs1,xs2 Lh(xs1:+:xs2)=Lh xs1+Lh xs2")
(ind)
(assume "xs2")
(use "Truth")
(assume "x" "xs1" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(save "ListLhAppend")

(add-rewrite-rule "Lh(xs1:+:xs2)" "Lh xs1+Lh xs2")

;; ListLhAppd
(set-goal "all xs1,xs2 Lh(xs1++xs2)=Lh xs1+Lh xs2")
(ind)
(assume "xs2")
(use "Truth")
(assume "x" "xs1" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(save "ListLhAppd")

(add-rewrite-rule "Lh(xs1++xs2)" "Lh xs1+Lh xs2")

;; Now for projection ListProj.  We use the rule (n thof (Nil alpha)) ->
;; (Inhab alpha)

(add-program-constant "ListProj" (py "nat=>list alpha=>alpha") t-deg-zero)

(add-infix-display-string "ListProj" "thof" 'pair-op) ;right associative

(add-token
 "__" 'mul-op ;hence left associative
 (lambda (xs y)
   (mk-term-in-app-form
    (make-term-in-const-form
     (let* ((const (pconst-name-to-pconst "ListProj"))
	    (tvars (const-to-tvars const))
	    (listtype (term-to-type xs))
	    (type (car (alg-form-to-types listtype)))
	    (subst (make-substitution tvars (list type))))
       (const-substitute const subst #f)))
    y xs)))

;; Not used (reason: occurrences of "thof" examples/tait)
;; (add-display
;;  (py "alpha")
;;  (lambda (x)
;;    (if (term-in-app-form? x)
;;        (let ((op (term-in-app-form-to-final-op x))
;; 	     (args (term-in-app-form-to-args x)))
;; 	 (if (and (term-in-const-form? op)
;; 		  (string=? "ListProj"
;; 			    (const-to-name (term-in-const-form-to-const op)))
;; 		  (= 2 (length args)))
;; 	     (list 'mul-op "__"
;; 		   (term-to-token-tree (car args))
;; 		   (term-to-token-tree (cadr args)))
;; 	     #f))
;;        #f)))

(add-computation-rules
 "nat thof(Nil alpha)" "(Inhab alpha)"
 "0 thof x::xs1" "x"
 "Succ nat1 thof x::xs1" "nat1 thof xs1")

;; (pp (nt (pt "0 thof 3::2::1::0:")))
;; 3
;; (pp (nt (pt "1 thof 3::2::1::0:")))
;; 2
;; (pp (nt (pt "3 thof 3::2::1::0:")))
;; 0
;; (pp (nt (pt "4 thof 3::2::1::0:")))
;; (Inhab nat)
;; (pp (nt (pt "(3::2::1::0:)__1")))
;; 2
;; (pp (nt (pt "(3::2::1::0:)__4")))
;; (Inhab nat)

(set-totality-goal "ListProj")
(assume "n^" "Tn")
(elim "Tn")
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "InhabTotal")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "Tx")
(assume "n^1" "Tn1" "IHn1" "xs^1" "Txs1")
(elim "Txs1")
(ng #t)
(use "InhabTotal")
(assume "x^" "Tx" "xs^2" "Txs2" "IHxs2")
(ng #t)
(use "IHn1")
(use "Txs2")
;; Proof finished.
;; (cdp)
(save-totality)

;; Since InhabTotal was used, totality of (ListProj tau) requires that
;; tau is a closed type with a total inhabitant (e.g. streams of booleans
;; are not allowed).  This remark also applies to ListBar ListHead ListLast

;; ListProjExtNc
(set-goal
 (make-imp
  (pf "EqPNc(Inhab alpha)(Inhab alpha)")
  (rename-variables (term-to-pure-extnc-formula (pt "(ListProj alpha)")))))

;; EqPNc(Inhab alpha)(Inhab alpha) -> allnc n^,n^0(
;;      EqPNatNc n^ n^0 -> 
;;      allnc xs^,xs^0(
;;       (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))xs^ xs^0 -> 
;;       EqPNc(n^ thof xs^)(n^0 thof xs^0)))

(assume "InhabExtNc")
(assert "allnc xs^,xs^0(
     (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))xs^ xs^0 -> 
     allnc n^,n^0(EqPNatNc n^ n^0 -> EqPNc(n^ thof xs^)(n^0 thof xs^0)))")
(assume "xs^1" "xs^2" "xs1=xs2")
(elim "xs1=xs2")
;; 6,7
(assume "n^1" "n^2" "n1=n2")
(ng #t)
(use "InhabExtNc")
;; 7
(assume "x^1" "x^2" "x1=x2" "xs^3" "xs^4" "xs3=xs4" "IH" "n^1" "n^2" "n1=n2")
(elim "n1=n2")
;; 11,12
(ng #t)
(use "x1=x2")
;; 12
(assume "n^3" "n^4" "n3=n4" "IHn")
(ng #t)
(use "IH")
(use "n3=n4")
;; Assertion proved.
(assume "Assertion" "n^1" "n^2" "n1=n2" "xs^1" "xs^2" "xs1=xs2")
(use "Assertion")
(use "xs1=xs2")
(use "n1=n2")
;; Proof finished.
;; (cdp)
(save "ListProjExtNc")	

;; ListProjAppdLeft
(set-goal "all xs1,n,xs2(n<Lh xs1 -> (n thof(xs1++xs2))eqd(n thof xs1))")
(ind)
(assume "n" "xs2" "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "x1" "xs1" "IHxs1")
(ng)
(cases)
(ng)
(strip)
(use "InitEqD")
(ng)
(use "IHxs1")
;; Proof finished.
;; (cdp)
(save "ListProjAppdLeft")

;; ListProjAppdRight
(set-goal "all xs1,xs2,n(n<Lh xs2 -> (Lh xs1+n thof(xs1++xs2))eqd(n thof xs2))")
(ind)
(ng)
(strip)
(use "InitEqD")
(assume "x1" "xs1" "IHxs1")
(ng)
(use "IHxs1")
;; Proof finished.
;; (cdp)
(save "ListProjAppdRight")

;; Usage of InhabTotal in the proof of totality of (ListProj tau) can be
;; avoided if tau is a closed type with a total inhabitant.  Example:

(add-program-constant "ListNatProj" (py "nat=>list nat=>nat") t-deg-zero)

(add-computation-rules
 "ListNatProj n(Nil nat)" "0"
 "ListNatProj 0 (n::ns)" "n"
 "ListNatProj(Succ n)(n0::ns)" "ListNatProj n ns")

(set-totality-goal "ListNatProj")
(assert "allnc ns^(TotalList ns^ -> allnc n^(TotalNat n^ -> 
         TotalNat(ListNatProj n^ ns^)))")
(assume "ns^" "Tns")
(elim "Tns")
;; 5,6
(ng)
(assume "n^" "Tn")
(intro 0)
;; 6
(assume "n^" "Tn" "ns^1" "Tns1" "IH" "n^1" "Tn1")
(elim "Tn1")
;; 10,11
(ng)
(use "Tn")
;; 11
(assume "n^2" "Tn2" "Useless")
(ng)
(use "IH")
(use "Tn2")
;; Assertion proved.
(search)
;; Proof finished.
;; (cdp)
(save-totality)

(add-program-constant
 "ListFBar" (py "(nat=>alpha)=>nat=>list alpha") t-deg-zero)

(add-infix-display-string "ListFBar" "fbar" 'pair-op) ;right associative

(add-computation-rules
 "xf fbar 0" "(Nil alpha)"
 "xf fbar Succ n" "xf 0::([n1]xf(Succ n1))fbar n")

;; (pp (nt (pt "Succ fbar 4")))
;; 1::2::3::4:
;; (pp (nt (pt "([n]n+3)fbar 4")))
;; 3::4::5::6:

;; ListFBarTotal
(set-goal (rename-variables (term-to-totality-formula (pt "(ListFBar alpha)"))))

;; allnc xf^(
;;      allnc n^(TotalNat n^ -> Total(xf^ n^)) -> 
;;      allnc n^(TotalNat n^ -> TotalList(xf^ fbar n^)))

(assert "allnc n^(
     TotalNat n^ -> 
     allnc xf^(
      allnc n^0(TotalNat n^0 -> Total(xf^ n^0)) -> TotalList(xf^ fbar n^)))")
(assume "n^" "Tn")
(elim "Tn")
;; 5,6
(assume "xf^" "Txf")
(ng #t)
(use "TotalListNil")
;; 6
(assume "n^1" "Tn1" "IH" "xf^" "Txf")
(ng #t)
(use "TotalListCons")
(use "Txf")
(use "TotalNatZero")
(use "IH")
(ng #t)
(assume "n^2" "Tn2")
(use "Txf")
(use "TotalNatSucc")
(use "Tn2")
;; Assertion proved.
(assume "Assertion" "xf^" "Txf" "n^" "Tn")
(use "Assertion")
(use "Tn")
(use "Txf")
;; Proof finished.
;; (cdp)
(save-totality)

;; ok, ListFBarTotal has been added as a new theorem.
;; ok, computation rule xf fbar 0 -> (Nil alpha) added
;; ok, computation rule xf fbar Succ n -> xf 0::([n1]xf(Succ n1))fbar n added

;; (term-to-t-deg (pt "(ListFBar alpha)"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [xf,n]
;;  (Rec nat=>(nat=>alpha)=>list alpha)n([xf0](Nil alpha))
;;  ([n0,((nat=>alpha)=>list alpha),xf0]
;;    xf0 0::((nat=>alpha)=>list alpha)([n1]xf0(Succ n1)))
;;  xf

;; Moreover we have extensionality of ListFBar:

;; ListFBarExtNc
(set-goal
 (rename-variables (term-to-pure-extnc-formula (pt "(ListFBar alpha)"))))

;; allnc xf^,xf^0(
;;      allnc n^,n^0(EqPNatNc n^ n^0 -> EqPNc(xf^ n^)(xf^0 n^0)) -> 
;;      allnc n^,n^0(
;;       EqPNatNc n^ n^0 -> 
;;       (REqPListNc (cterm (alpha^,alpha^0) EqPNc alpha^ alpha^0))(xf^ fbar n^)
;;       (xf^0 fbar n^0)))

(assert "allnc n^,n^0(
     EqPNatNc n^ n^0 -> 
     allnc xf^,xf^0(
      allnc n^1,n^2(EqPNatNc n^1 n^2 -> EqPNc(xf^ n^1)(xf^0 n^2)) -> 
      (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))(xf^ fbar n^)
      (xf^0 fbar n^0)))")
(assume "n^1" "n^2" "n1=n2")
(elim "n1=n2")
;; 5,6
(assume "xf^1" "xf^2" "EqPHyp")
(ng #t)
(intro 0)
;; 6
(assume "n^3" "n^4" "n3=n4" "IH" "xf^1" "xf^2" "EqPHyp")
(ng #t)
(use-with
 "REqPListNcCons"
 (py "alpha") (make-cterm (pv "x^1")  (pv "x^2") (pf "EqPNc x^1 x^2"))
 (pt "xf^1 0") (pt "xf^2 0") "?"
 (pt "([n]xf^1(Succ n))fbar n^3") (pt "([n]xf^2(Succ n))fbar n^4") "?")
(use "EqPHyp")
(intro 0)
(use "IH")
(ng #t)
(assume "n^5" "n^6" "n5=n6")
(use "EqPHyp")
(intro 1)
(use "n5=n6")
;; Assertion proved.
(assume "Assertion" "xf^1" "xf^2" "EqPHyp" "n^1" "n^2" "n1=n2")
(use "Assertion")
(use "n1=n2")
(use "EqPHyp")
;; Proof finished.
;; (cdp)
(save "ListFBarExtNc")

(set-goal "all n allnc xf^ Lh(xf^ fbar n)=n")
(ind)
(assume "xf^")
(ng #t)
(use "Truth")
(assume "n" "IHn")
(assume "xf^")
(ng #t)
(use "IHn")
;; Proof finished.
;; (cdp)

(add-rewrite-rule "Lh(xf^ fbar n)" "n")

(add-program-constant "ListBar" (py "list alpha=>nat=>list alpha") t-deg-zero)

(add-infix-display-string "ListBar" "bar" 'add-op) ;left associative

(add-computation-rules
 "xs bar 0" "(Nil alpha)"
 "(Nil alpha)bar(Succ n)" "(Inhab alpha)::(Nil alpha) bar n"
 "(x::xs)bar Succ n" "x::xs bar n")

;; (pp (nt (pt "(0::1::2::3::4:)bar 2")))
;; 0::1:
;; (pp (nt (pt "(0::1::2::3::4:)bar 7")))
;; 0::1::2::3::4::(Inhab nat)::(Inhab nat):

;; (add-computation-rule "(Inhab nat)" "0")

;; (pp (nt (pt "(0::1::2::3::4:)bar 7")))
;; 0::1::2::3::4::0::0:

(set-totality-goal "ListBar")
(assume "xs^" "Txs")
(elim "Txs")
(assume "n^" "Tn")
(elim "Tn")
(ng #t)
(use "TotalListNil")
(assume "n^0" "Tn0" "IHn0")
(ng #t)
(use "TotalListCons")
(use "InhabTotal")
(use "IHn0")
;; Step
(assume "x^" "Tx" "xs^1" "Txs1" "IH" "n^1" "Tn1")
(elim "Tn1")
(ng #t)
(use "TotalListNil")
(assume "n^2" "Tn2" "Useless")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IH")
(use "Tn2")
;; Proof finished.
;; (cdp)
(save-totality)

;; ListBarExtNc
(set-goal
 (make-imp
  (pf "EqPNc(Inhab alpha)(Inhab alpha)")
  (rename-variables (term-to-pure-extnc-formula (pt "(ListBar alpha)")))))

;; EqPNc(Inhab alpha)(Inhab alpha) -> 
;;     allnc xs^,xs^0(
;;      (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))xs^ xs^0 -> 
;;      allnc n^,n^0(
;;       EqPNatNc n^ n^0 -> 
;;       (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))(xs^ bar n^)(xs^0 bar n^0)))

(assume "InhabExtNc" "xs^1" "xs^2" "xs1=xs2")
(elim "xs1=xs2")
;; 3,4
(assume "n^1" "n^2" "n1=n2")
(elim "n1=n2")
(ng #t)
(intro 0)
;; 7
(assume "n^3" "n^4" "n3=n4" "IH")
(ng #t)
(intro 1)
(use "InhabExtNc")
(use "IH")
;; 4
(assume "x^1" "x^2" "x1=x2" "xs^3" "xs^4" "xs3=xs4" "IH" "n^1" "n^2" "n1=n2")
(elim "n1=n2")
;; 14,15
(ng #t)
(intro 0)
;; 15
(assume "n^3" "n^4" "n3=n4" "IHn")
(ng #t)
(intro 1)
(use "x1=x2")
(use "IH")
(use "n3=n4")
;; Proof finished.
;; (cdp)
(save "ListBarExtNc")

(set-goal "all xs,n Lh(xs bar n)=n")
(ind)
(ind)
(ng #t)
(use "Truth")
(assume "n" "IHn")
(ng #t)
(use "IHn")
(assume "x" "xs" "IHxs")
(cases)
(ng #t)
(use "Truth")
(assume "n")
(ng #t)
(use "IHxs")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Lh(xs bar n)" "n")

;; A list of length n+1 can be seen as the result of appending to its
;; initial segment of length n its final element.

;; ListBarAppdLast
(set-goal "all n,xs(Lh xs=Succ n -> (xs bar n)++(n thof xs):eqd xs)")
(ind)
;; Base
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "x" "xs" "Lh xs=0")
(ng #t)
(assert "xs eqd(Nil alpha)")
 (use "ListLhZeroToEqNil")
 (use "Lh xs=0")
(assume "xs=Nil")
(simp "xs=Nil")
(use "InitEqD")
;; Step
(assume "n" "IHn")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "x" "xs" "Lh xs=Succ n")
(ng #t)
(simp "IHn")
(use "InitEqD")
(use "Lh xs=Succ n")
;; Proof finished.
;; (cdp)
(save "ListBarAppdLast")

;; ListFBarAppdLast
(set-goal "all n allnc xf^ (xf^ fbar Succ n)eqd(xf^ fbar n)++(xf^ n):")
(ind)
(assume "xf^")
(ng #t)
(use "InitEqD")
;; Step
(assume "n" "IHn" "xf^")
(assert "(xf^ fbar Succ(Succ n))eqd(xf^ 0::([n]xf^ (Succ n))fbar Succ n)")
 (ng #t)
 (use "InitEqD")
(assume "Equality")
(simp "Equality")
(simp "IHn")
(ng #t)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListFBarAppdLast")

;; Now the relation between ListBar and ListFBar

;; ListBarFBar
(set-goal "all n,xs xs bar n eqd(([m]m thof xs)fbar n)")
(ind)
(assume "xs")
(ng #t)
(use "InitEqD")
(assume "n" "IHn")
(cases)
(ng #t)
(simp "IHn")
(ng #t)
(use "InitEqD")
(assume "x" "xs")
(ng #t)
(simp "IHn")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListBarFBar")

;; ListBarFBarPlus
(set-goal "all n allnc m,xf^((xf^ fbar(n+m))bar n eqd(xf^ fbar n))")
(ind)
(assume "m" "xf^")
(ng)
(use "InitEqD")
(assume "n" "IH"  "m" "xf^")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListBarFBarPlus")

;; ListProjFBar
(set-goal "all l,n allnc xf^(n<l -> (n thof xf^ fbar l)eqd xf^ n)")
(ind)
;; 2,3
(assume "n" "xf^" "Absurd")
(use "EfEqD")
(use "Absurd")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(strip)
(use "InitEqD")
(assume "m" "xf^" "m<n")
(ng #t)
(use "IH")
(use "m<n")
;; Proof finished.
;; (cdp)
(save "ListProjFBar")

(add-var-name "nf" (py "nat=>nat"))

;; ListNatProjFBar
(set-goal "all l,n allnc nf^(n<l -> (ListNatProj n(nf^ fbar l))eqd nf^ n)")
(ind)
;; 2,3
(assume "n" "nf^" "Absurd")
(use "EfEqD")
(use "Absurd")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(strip)
(use "InitEqD")
(assume "m" "nf^" "m<n")
(ng #t)
(use "IH")
(use "m<n")
;; Proof finished.
;; (cdp)
(save "ListNatProjFBar")

(add-var-name "psi" (py "alpha1=>list alpha1=>alpha2"))
(add-var-name "y" (py "alpha1"))
(add-var-name "ys" (py "list alpha1"))
(add-var-name "z" (py "alpha2"))
(add-var-name "zs" (py "list alpha2"))

;; ListIfTotal
(set-goal "allnc ys^(TotalList ys^ ->
 allnc z^,psi^(Total z^ ->
 allnc y^,ys^(Total y^ -> TotalList ys^ -> Total(psi^ y^ ys^)) ->
 Total[if ys^ z^ psi^]))")
(assume "ys^" "Tys" "z^" "psi^" "Tz" "Tpsi")
(elim "Tys")
(use "Tz")
(assume "y^1" "Ty1" "ys^1" "Tys1" "Useless")
(ng #t)
(use "Tpsi")
(use "Ty1")
(use "Tys1")
;; Proof finished.
;; (cdp)
(save "ListIfTotal")

;; ListIfSTotal
(set-goal "allnc ys^(STotalList ys^ ->
 allnc z^,psi^(Total z^ ->
 allnc y^,ys^(STotalList ys^ -> Total(psi^ y^ ys^)) ->
 Total[if ys^ z^ psi^]))")
(assume "ys^" "STys" "z^" "psi^" "Tz" "STpsi")
(elim "STys")
(use "Tz")
(assume "y^1" "ys^1" "STys1" "Useless")
(ng #t)
(use "STpsi")
(use "STys1")
;; Proof finished.
;; (cdp)
(save "ListIfSTotal")

(add-program-constant
 "ListMap" (py "(alpha1=>alpha2)=>list alpha1=>list alpha2") t-deg-zero)

(add-infix-display-string "ListMap" "map" 'pair-op) ;right associative

(add-var-name "phi" (py "alpha1=>alpha2"))

(add-computation-rules
 "phi map(Nil alpha1)" "(Nil alpha2)"
 "phi map y::ys" "phi y::phi map ys")

;; (pp (nt (pt "Pred map 2::3::4:")))
;; 1::2::3:

;; ListMapTotal
(set-goal
 (rename-variables (term-to-totality-formula (pt "(ListMap alpha1 alpha2)"))))

;; allnc phi^(
;;      allnc y^(Total y^ -> Total(phi^ y^)) -> 
;;      allnc ys^(TotalList ys^ -> TotalList(phi^ map ys^)))

(assume "phi^" "Tphi" "ys^" "Tys^")
(elim "Tys^")
;; 3,4
(ng #t)
(use "TotalListNil")
;; 4
(assume "y^" "Ty" "ys^1" "Tys1" "IH")
(ng #t)
(use "TotalListCons")
(use "Tphi")
(use "Ty")
(use "IH")
;; Proof finished.
;; (cdp)
;; (save "ListMapTotal")
(save-totality)

;; ok, ListMapTotal has been added as a new theorem.
;; ok, computation rule phi map(Nil alpha1) -> (Nil alpha2) added
;; ok, computation rule phi map y::ys -> phi y::phi map ys added

;; (term-to-t-deg (pt "(ListMap alpha1 alpha2)"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [phi,ys]
;;  (Rec list alpha1=>list alpha2)ys(Nil alpha2)([y,ys0](Cons alpha2)(phi y))

;; Moreover we have extensionality of ListMap:

;; ListMapExt
(set-goal
 (rename-variables (terms-to-eqp-formula (pt "(ListMap alpha1 alpha2)")
					 (pt "(ListMap alpha1 alpha2)"))))

;; allnc phi^,phi^0(
;;      allnc y^,y^0(EqP y^ y^0 -> EqP(phi^ y^)(phi^0 y^0)) -> 
;;      allnc ys^,ys^0(
;;       (REqPList (cterm (y^,y^0) EqP y^ y^0))ys^ ys^0 -> 
;;       (REqPList (cterm (z^,z^0) EqP z^ z^0))(phi^ map ys^)(phi^0 map ys^0)))

(assume "phi^1" "phi^2" "EqPphi1phi2" "ys^1" "ys^2" "EqPys1ys2")
(elim "EqPys1ys2")
;; 3,4
(ng #t)
(use "REqPListNil")
;; 4
(assume "y^1" "y^2" "EqPy1y2" "ys^3" "ys^4" "EqPys3ys4" "IH")
(ng #t)
(use-with
 "REqPListCons"
 (py "alpha2") (make-cterm (pv "z^1")  (pv "z^2") (pf "EqP z^1 z^2"))
 (pt "phi^1 y^1") (pt "phi^2 y^2") "?"
 (pt "phi^1 map ys^3") (pt "phi^2 map ys^4") "?")
(use "EqPphi1phi2")
(use "EqPy1y2")
(use "IH")
;; Proof finished.
;; (cdp)
(save "ListMapExt")

;; ListMapSTotal
(set-goal (rename-variables
	   (term-to-stotality-formula (pt "(ListMap alpha1 alpha2)"))))
(assume "phi^" "Tphi" "ys^" "STys")
(elim "STys")
(ng #t)
(use "STotalListNil")
(assume "y^1" "ys^1" "STys1" "IH")
(ng #t)
(use "STotalListCons")
(use "IH")
;; Proof finished.
;; (cdp)
(save "ListMapSTotal")

;; ListLhMap
(set-goal "all phi,ys Lh(phi map ys)=Lh ys")
(assume "phi")
(ind)
(use "Truth")
(assume "y" "ys" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(save "ListLhMap")

;; ListLhMapPartial
(set-goal "allnc phi^,ys^(STotalList ys^ -> Lh(phi^ map ys^)=Lh ys^)")
(assume "phi^" "ys^" "STys")
(elim "STys")
(ng #t)
(use "Truth")
(assume "y^" "ys^1" "STys1" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "ListLhMapPartial")

;; ListMapAppend
(set-goal "all phi,ys2,ys1 (phi map ys1:+:ys2)eqd(phi map ys1):+:(phi map ys2)")
(assume "phi" "ys2")
(ind)
(ng)
(use "InitEqD")
(assume "y" "ys" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListMapAppend")

;; ListMapAppendPartial
(set-goal "allnc phi^,ys^2,ys^1(
       STotalList ys^1 ->
       (phi^ map ys^1:+:ys^2)eqd(phi^ map ys^1):+:(phi^ map ys^2))")
(assume "phi^" "ys^2" "ys^1" "STys1")
(elim "STys1")
(ng #t)
(use "InitEqD")
(assume "y^" "ys^" "STys" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListMapAppendPartial")

;; ListMapAppd
(set-goal "all phi,ys2,ys1 (phi map ys1++ys2)eqd(phi map ys1)++(phi map ys2)")
(assume "phi" "ys2")
(ind)
(ng)
(use "InitEqD")
(assume "y" "ys" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListMapAppd")

;; ListMapAppdPartial
(set-goal "allnc phi^,ys^2,ys^1(
       STotalList ys^1 ->
       (phi^ map ys^1++ys^2)eqd(phi^ map ys^1)++(phi^ map ys^2))")
(assume "phi^" "ys^2" "ys^1" "STys1")
(elim "STys1")
(ng #t)
(use "InitEqD")
(assume "y^" "ys^" "STys" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListMapAppdPartial")

;; ListProjMap
(set-goal "allnc phi^ all ys,n(n<Lh ys ->
 (n thof phi^ map ys)eqd phi^(n thof ys))")
(assume "phi^")
(ind)
(assume "n" "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "y" "ys" "IH")
(cases)
(assume "Useless")
(ng #t)
(use "InitEqD")
(assume "n" "n<Lh ys")
(ng #t)
(use "IH")
(use "n<Lh ys")
;; Proof finished.
;; (cdp)
(save "ListProjMap")

(add-var-name "yf" (py "nat=>alpha1"))

;; ListMapFbar
(set-goal "allnc phi^ all n allnc yf^(
       phi^ map yf^ fbar n)eqd(([n]phi^(yf^ n))fbar n)")
(assume "phi^")
(ind)
(assume "yf^")
(ng #t)
(use "InitEqD")
(assume "n" "IHn" "yf^")
(ng #t)
(simp "IHn")
(ng #t)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListMapFbar")

(add-rewrite-rule
 "phi^ map yf^ fbar n" "([n]phi^(yf^ n))fbar n")

(add-program-constant
 "Consn" (py "alpha=>nat=>list alpha=>list alpha") t-deg-zero)

(add-computation-rules
 "(Consn alpha)x 0 xs" "xs"
 "(Consn alpha)x(Succ n)(Nil alpha)" "x::(Consn alpha)x n(Nil alpha)"
 "(Consn alpha)x(Succ n)(x1::xs)" "x1::(Consn alpha)x n(xs)")

;; (pp (nt (pt "(Consn nat)n 7(0::1::2:)")))
;; => 0::1::2::n::n::n::n:

(set-totality-goal "Consn")
(assume "x^" "Tx" "n^" "Tn")
(elim "Tn")
;; Base
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "TotalListNil")
(assume "x^1" "Tx1" "xs^1" "Txs1" "Useless")
(ng #t)
(use "TotalListCons")
(use "Tx1")
(use "Txs1")
;; Step
(assume "n^1" "Tn1" "IHn1" "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IHn1")
(use "TotalListNil")
(assume "x^1" "Tx1" "xs^1" "Txs1" "Useless")
(ng #t)
(use "TotalListCons")
(use "Tx1")
(use "IHn1")
(use "Txs1")
;; Proof finished.
;; (cdp)
(save-totality)

;; (pp (rename-variables (term-to-stotality-formula (pt "(Consn alpha)"))))

;; allnc x^(
;;  Total x^ ->
;;  allnc n^(
;;   TotalNat n^ ->
;;   allnc xs^(STotalList xs^ -> STotalList((Consn alpha)x^ n^ xs^))))

;; ConsnSTotal
(set-goal (rename-variables (term-to-stotality-formula (pt "(Consn alpha)"))))
(assume "x^" "Tx" "n^" "Tn")
(elim "Tn")
;; Base
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "STotalListNil")
(assume "x^1" "xs^1" "Txs1" "Useless")
(ng #t)
(use "STotalListCons")
(use "Txs1")
;; Step
(assume "n^1" "Tn1" "IHn1" "xs^" "STxs")
(elim "STxs")
(ng #t)
(use "STotalListCons")
(use "IHn1")
(use "STotalListNil")
(assume "x^1" "xs^1" "STxs1" "Useless")
(ng #t)
(use "STotalListCons")
(use "IHn1")
(use "STxs1")
;; Proof finished.
;; (cdp)
(save "ConsnSTotal")

;; ListLhConsn
(set-goal "allnc x^1,xs^(
        STotalList xs^ ->
        all n(
         Lh xs^ <=n ->
         Lh(xs^ :+:(Consn alpha)x^1(n--Lh xs^)(Nil alpha))eqd n))")
(assume "x^1" "xs^" "STxs")
(elim "STxs")
(ind)
;; 5,6
(assume "Useless")
(ng #t)
(use  "InitEqD")
;; 6
(assume "n" "IHn" "Useless")
(ng #t)
(simp "IHn")
(use "InitEqD")
(use "Truth")
;; 4
(assume "x^2" "xs^1" "STxs1" "IHl")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n" "Lh xs^1 <=n")
(ng #t)
(assert "allnc n1,n^2(TotalNat n^2 -> Pred(Succ n1--n^2)eqd n1--n^2)")
 (assume "n1")
 (use-with (make-proof-in-aconst-form alltotal-elim-aconst)
	   (py "nat")
	   (make-cterm (pv "n^2") (pf "Pred(Succ n1--n^2)eqd n1--n^2"))
	   "?")
 (assume "n2")
 (ng #t)
 (use "InitEqD")
(assume "H")
(simp "H")
(simp "IHl")
(use "InitEqD")
(use "Lh xs^1 <=n")
(use "ListLengthSTotal")
(use "STxs1")
;; Proof finished.
;; (cdp)
(save "ListLhConsn")

;; ListLhConsnAppd
(set-goal "allnc x^1,xs^(
        STotalList xs^ ->
        all n(
         Lh xs^ <=n ->
         Lh(xs^ ++(Consn alpha)x^1(n--Lh xs^)(Nil alpha))eqd n))")
(assume "x^1" "xs^" "STxs")
(elim "STxs")
(ind)
(assume "Useless")
(ng #t)
(use "InitEqD")
(assume "n" "IHn" "Useless")
(ng #t)
(simp "IHn")
(use "InitEqD")
(use "Truth")
(assume "x^2" "xs^2" "STxs2" "IHl")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n" "Lh xs^ <=n")
(ng #t)
(assert "all n1 allnc n^2(TotalNat n^2 -> Pred(Succ n1--n^2)eqd n1--n^2)")
 (assume "n1")
 (use-with (make-proof-in-aconst-form alltotal-elim-aconst)
	   (py "nat")
	   (make-cterm (pv "n^2") (pf "Pred(Succ n1--n^2)eqd n1--n^2"))
	   "?")
 (assume "n2")
 (ng #t)
 (use "InitEqD")
(assume "H")
(simp "H")
(simp "IHl")
(use "InitEqD")
(use "Lh xs^ <=n")
(use "ListLengthSTotal")
(use "STxs2")
;; Proof finished.
;; (cdp)
(save "ListLhConsnAppd")

;; We add a bounded universal quantifier.  AllBList n P means that for
;; all lists of length n of booleans the property P holds.

(add-program-constant
 "AllBList" (py "nat=>(list boole=>boole)=>boole") t-deg-zero)

(add-var-name "ps" (py "list boole"))
(add-var-name "pstop" (py "list boole=>boole"))

(add-computation-rules
 "AllBList 0 pstop" "pstop(Nil boole)"
 "AllBList(Succ n)pstop" "(AllBList n([ps]pstop(True::ps)))andb
                          (AllBList n([ps]pstop(False::ps)))")

;; AllBListTotal
(set-goal (rename-variables (term-to-totality-formula (pt "AllBList"))))

;; allnc n^(
;;      TotalNat n^ -> 
;;      allnc pstop^(
;;       allnc ps^(TotalList ps^ -> TotalBoole(pstop^ ps^)) -> 
;;       TotalBoole(AllBList n^ pstop^)))

(assume "n^" "Tn")
(elim "Tn")
;; 3,4
(assume "pstop^" "Tpstop")
(ng #t)
(use "Tpstop")
(use "TotalListNil")
;; 4
(assume "n^1" "Tn1" "IH" "pstop^" "Tpstop")
(ng #t)
(use "AndConstTotal")
;; 10,11
(use "IH")
(ng #t)
(assume "ps^" "Tps")
(use "Tpstop")
(use "TotalListCons")
(use "TotalBooleTrue")
(use "Tps")
;; 11
(use "IH")
(ng #t)
(assume "ps^" "Tps")
(use "Tpstop")
(use "TotalListCons")
(use "TotalBooleFalse")
(use "Tps")
;; Proof finished.
;; (cdp)
;; (save "AllBListTotal")
(save-totality)

;; ok, AllBListTotal has been added as a new theorem.
;; ok, computation rule AllBList 0 pstop -> pstop(Nil boole) added
;; ok, computation rule AllBList(Succ n)pstop ->
;;        AllBList n([ps]pstop(True::ps))andb
;;        AllBList n([ps]pstop(False::ps)) added

;; (term-to-t-deg (pt "AllBList"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (Rec nat=>(list boole=>boole)=>boole)n([pstop]pstop(Nil boole))
;;  ([n0,((list boole=>boole)=>boole),pstop]
;;    ((list boole=>boole)=>boole)([ps]pstop(True::ps))andb
;;    ((list boole=>boole)=>boole)([ps]pstop(False::ps)))

;; Moreover we have extensionality of AllBList:

;; AllBListExt
(set-goal
 (rename-variables (terms-to-eqp-formula (pt "AllBList") (pt "AllBList"))))

;; allnc n^(
;;      TotalNat n^ -> 
;;      allnc pstop^,pstop^0(
;;       allnc ps^(TotalList ps^ -> EqPBoole(pstop^ ps^)(pstop^0 ps^)) -> 
;;       EqPBoole(AllBList n^ pstop^)(AllBList n^ pstop^0)))

(assume "n^" "Tn")
(elim "Tn")
;; 3,4
(assume  "pstop^1" "pstop^2" "Hyp")
(use "Hyp")
(use "TotalListNil")
;; 4
(assume "n^1" "Tn1" "IH" "pstop^1" "pstop^2" "EqPHyp")
(ng #t)
(use "AndConstEqP")
;; 9,10
(use "IH")
(ng #t)
(assume "ps^" "Tps")
(use "EqPHyp")
(use "TotalListCons")
(use "TotalBooleTrue")
(use "Tps")
;; 10
(use "IH")
(ng #t)
(assume "ps^" "Tps")
(use "EqPHyp")
(use "TotalListCons")
(use "TotalBooleFalse")
(use "Tps")
;; Proof finished.
;; (cdp)
(save "AllBListExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (Rec nat=>(list boole=>boole)=>boole)n([pstop]pstop(Nil boole))
;;  ([n0,((list boole=>boole)=>boole),pstop]
;;    cAndConstEqP(((list boole=>boole)=>boole)([ps]pstop(True::ps)))
;;    (((list boole=>boole)=>boole)([ps]pstop(False::ps))))

;; AllBListIntro
(set-goal
 "all n,pstop(allnc ps^(Lh ps^ =n -> pstop ps^) -> AllBList n pstop)")
(ind)
;; Base
(assume "pstop" "Hyp")
(ng #t)
(use "Hyp")
(ng #t)
(use "Truth")
;; Step
(assume "n" "IH" "pstop" "Hyp")
(ng #t)
(split)
(use "IH")
(assume "ps^" "Lhn")
(ng #t)
(use "Hyp")
(ng #t)
(use "Lhn")
(use "IH")
(assume "ps^" "Lhn")
(ng #t)
(use "Hyp")
(ng #t)
(use "Lhn")
;; Proof finished.
;; (cdp)
(save "AllBListIntro")

;; AllBListElim
(set-goal "all n,pstop(AllBList n pstop -> all ps(Lh ps=n -> pstop ps))")
(ind)
;; Base
(assume "pstop" "H1")
(cases)
(assume "Useless")
(use "H1")
(assume "boole" "ps" "Absurd")
(use "EfAtom")
(use "Absurd")
;; Step
(assume "n" "IH" "pstop" "H1")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(cases)
(assume "ps" "Lhn")
(use-with "IH" (pt "[ps1]pstop(True::ps1)") "?" (pt "ps") "?")
(ng "H1")
(use "H1")
(use "Lhn")
(assume "ps" "Lhn")
(use-with "IH" (pt "[ps1]pstop(False::ps1)") "?" (pt "ps") "?")
(ng "H1")
(use "H1")
(use "Lhn")
;; Proof finished.
;; (cdp)
(save "AllBListElim")

(add-program-constant "ListRev" (py "list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListRev" "Rev")
(add-computation-rules
 "Rev(Nil alpha)" "(Nil alpha)"
 "Rev(x::xs)" "Rev xs++x:")

(set-totality-goal "ListRev")
(use "AllTotalElim")
(ind)
(use "TotalListNil")
(assume "x" "xs" "IH")
(ng #t)
(use "ListAppdTotal")
(use "IH")
(use "ListTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; ListRevSTotal
(set-goal (rename-variables (term-to-stotality-formula (pt "(ListRev alpha)"))))
(assume "xs^" "STxs")
(elim "STxs")
(use "STotalListNil")
(assume "x^1" "xs^1" "STxs1" "IH")
(ng #t)
(use "ListAppdSTotal")
(use "IH")
(use "STotalListCons")
(use "STotalListNil")
;; Proof finished.
;; (cdp)
(save "ListRevSTotal")

;; ListLengthRev
(set-goal "all xs Lh Rev xs eqd Lh xs")
(ind)
(use "InitEqD")
(assume "x" "xs" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListLengthRev")

;; ListRevAppd
(set-goal "all xs1,xs2 Rev(xs1++xs2)eqd Rev xs2++Rev xs1")
(ind)
(ng #t)
(strip)
(use "InitEqD")
(assume "x" "xs" "IH")
(ng #t)
(assume "xs2")
(simp "IH")
(simp "ListAppdAssoc")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListRevAppd")

;; ListRevAppdPartial
(set-goal "allnc xs^1(STotalList xs^1 -> allnc xs^2(STotalList xs^2 ->
                   Rev(xs^1 ++xs^2)eqd Rev xs^2 ++Rev xs^1))")
(assume "xs^1" "STxs1")
(elim "STxs1")
(ng #t)
(assume "xs^2" "STxs2")
(simp "ListAppdNilPartial")
(use "InitEqD")
(use "ListRevSTotal")
(use "STxs2")
(assume "x^" "xs^" "STxs" "IH")
(ng #t)
(assume "xs^2" "STxs2")
(simp "IH")
(simp "ListAppdAssocPartial")
(use "InitEqD")
(use "ListRevSTotal")
(use "STxs2")
(use "STxs2")
;; Proof finished.
;; (cdp)
(save "ListRevAppdPartial")

;; ListRevInvol
(set-goal "all xs Rev(Rev xs)eqd xs")
(ind)
(use "InitEqD")
(assume "x" "xs" "IH")
(ng #t)
(simp "ListRevAppd")
(simp "IH")
(ng #t)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListRevInvol")

;; ListRevInvolPartial
(set-goal "allnc xs^(STotalList xs^ -> Rev(Rev xs^)eqd xs^)")
(assume "xs^" "STxs")
(elim "STxs")
(ng #t)
(use "InitEqD")
(assume "x^1" "xs^1" "STxs1" "IH")
(ng #t)
(simp "ListRevAppdPartial")
(simp "IH")
(ng #t)
(use "InitEqD")
(use "STotalListCons")
(use "STotalListNil")
(use "ListRevSTotal")
(use "STxs1")
;; Proof finished.
;; (cdp)
(save "ListRevInvolPartial")

;; ListProjRev
(set-goal "all xs,n(n<Lh xs -> (n thof Rev xs)eqd(Pred(Lh xs--n)thof xs))")
(assert "all xs,n(n<Lh xs -> (n thof xs)eqd(Pred(Lh xs--n)thof Rev xs))")
 (ind)
 (ng)
 (assume "n" "Absurd")
 (use "InitEqD")
 (assume "x" "xs" "IH")
 (ng #t)
 (cases)
 (ng #t)
 (assume "Useless")
 (assert "Lh xs eqd Lh Rev xs+0")
  (simp "ListLengthRev")
  (use "InitEqD")
 (assume "EqHyp")
 (simp "EqHyp")
 (simp "ListProjAppdRight")
 (use "InitEqD")
 (use "Truth")
;; Case Succ n
 (ng #t)
 (assume "n" "n<Lh xs")
 (simp "ListProjAppdLeft")
 (use "IH")
 (use "n<Lh xs")
;; ?_22:Pred(Lh xs--n)<Lh Rev xs
 (simp "ListLengthRev")
 (cases (pt "Lh xs"))
 (assume "Lh xs=0")
 (simphyp-with-to "n<Lh xs" "Lh xs=0" "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "n0" "Lh xs=Sn0")
 (ng #t)
 (use "NatLeLtTrans" (pt "n0"))
 (use "Truth")
 (use "Truth")
(assume "ListProjRevAux" "xs" "n" "n<Lh xs")
(inst-with-to "ListProjRevAux" (pt "Rev xs") (pt "n") "Aux")
(assert "Rev Rev xs eqd xs")
 (use "ListRevInvol")
(assume "Assertion")
(simphyp-with-to "Aux" "Assertion" "SimpAux")
(assert "Lh Rev xs eqd Lh xs")
 (use "ListLengthRev")
(assume "Lh Rev xs eqd Lh xs")
(simphyp-with-to "SimpAux" "Lh Rev xs eqd Lh xs" "SimpSimpAux")
(use "SimpSimpAux")
(use "n<Lh xs")
;; Proof finished.
;; (cdp)
(save "ListProjRev")

;; ListRevFBarSucc
(set-goal "all n,xf Rev(xf fbar Succ n)eqd(xf n::Rev(xf fbar n))")
(assume "n" "xf")
(simp "ListFBarAppdLast")
(simp "ListRevAppd")
(ng)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListRevFBarSucc")

;; Similar to Pred in nat.scm we define Head and Tail.  They are
;; easier to handle than the general (Destr list alpha).

(add-program-constant "ListHead" (py "list alpha=>alpha") t-deg-zero)
(add-prefix-display-string "ListHead" "Head")
(add-computation-rules
 "Head(Nil alpha)" "(Inhab alpha)"
 "Head(x::xs)" "x")

(set-totality-goal "ListHead")
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "InhabTotal")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "Tx")
;; Proof finished.
;; (cdp)
(save-totality)

;; ListHeadExtNc
(set-goal
 (make-imp
  (pf "EqPNc(Inhab alpha)(Inhab alpha)")
  (rename-variables (term-to-pure-extnc-formula (pt "(ListHead alpha)")))))

;; EqPNc(Inhab alpha)(Inhab alpha) -> 
;;     allnc xs^,xs^0(
;;      (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))xs^ xs^0 -> 
;;      EqPNc(Head xs^)(Head xs^0))

(assume "InhabExtNc" "xs^1" "xs^2" "xs1=xs2")
(elim "xs1=xs2")
;; 3,4
(ng #t)
(use "InhabExtNc")
;; 4
(assume "x^1" "x^2" "x1=x2" "xs^3" "xs^4" "xs3=xs4" "Useless")
(ng #t)
(use "x1=x2")
;; Proof finished.
;; (cdp)
(save "ListHeadExtNc")

(add-program-constant "ListTail" (py "list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListTail" "Tail")
(add-computation-rules
 "Tail(Nil alpha)" "(Nil alpha)"
 "Tail(x::xs)" "xs")

(set-totality-goal "ListTail")
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(intro 0)
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "Txs1")
;; Proof finished.
;; (cdp)
(save-totality)

;; ListTailExtNc
(set-goal
 (rename-variables
  (term-to-pure-extnc-formula (pt "(ListTail alpha)"))))

;; allnc xs^,xs^0(
;;      (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))xs^ xs^0 -> 
;;      (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))(Tail xs^)(Tail xs^0))

(assume "xs^1" "xs^2" "xs1=xs2")
(elim "xs1=xs2")
;; 3,4
(ng #t)
(intro 0)
;; 4
(assume "x^1" "x^2" "x1=x2" "xs^3" "xs^4" "xs3=xs4" "Useless")
(ng #t)
(use "xs3=xs4")
;; Proof finished.
;; (cdp)
(save "ListTailExtNc")

;; ListZeroLtLhToHeadTailId
(set-goal "all xs(0<Lh xs -> (Head xs::Tail xs)eqd xs)")
(cases)
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "x" "xs" "Useless")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListZeroLtLhToHeadTailId")

(add-program-constant "ListLast" (py "list alpha=>alpha") t-deg-zero)
(add-prefix-display-string "ListLast" "Last")
(add-computation-rules
 "Last(Nil alpha)" "(Inhab alpha)"
 "Last(x::xs)" "[if (Lh xs=0) x (Last xs)]")

(set-totality-goal "ListLast")
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "InhabTotal")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "BooleIfTotal")
(use "NatEqTotal")
(use "ListLengthTotal")
(use "Txs1")
(use "TotalNatZero")
(use "Tx")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

(add-program-constant "ListMain" (py "list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListMain" "Main")
(add-computation-rules
 "Main(Nil alpha)" "(Nil alpha)"
 "Main(x::xs)" "[if (Lh xs=0) (Nil alpha) (x::Main xs)]")

(set-totality-goal "ListMain")
(assume "xs^" "Txs")
(elim "Txs")
;; 3,4
(ng #t)
(use "TotalListNil")
;; 4
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "BooleIfTotal")
(use "NatEqTotal")
(use "ListLengthTotal")
(use "Txs1")
(use "TotalNatZero")
(use "TotalListNil")
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

;; ListZeroLtLhToMainLastId
(set-goal "all xs(0<Lh xs -> Main xs++(Last xs):eqd xs)")
(assert "all n,xs(Lh xs<=n -> 0<Lh xs -> Main xs++(Last xs):eqd xs)")
(ind)
(assume "xs")
(ng)
(assume "Lh xs=0")
(simp "Lh xs=0")
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n" "IHn")
(cases)
(ng)
(assume "Useless" "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "x" "xs" "LhBound" "Useless")
(ng)
(cases (pt "Lh xs=0"))
(assume "Lh xs=0")
(assert "xs eqd(Nil alpha)")
 (use "ListLhZeroToEqNilPartial")
 (use "ListSTotalVar")
 (use "Lh xs=0")
(assume "xs eqd(Nil alpha)")
(simp "xs eqd(Nil alpha)")
(ng)
(use "InitEqD")
(assume "0=Lh xs -> F")
(ng)
(simp "IHn")
(use "InitEqD")
(cases (pt "Lh xs"))
(assume "Lh xs=0")
(use "0=Lh xs -> F")
(use "Lh xs=0")
(strip)
(use "Truth")
(use "LhBound")
;; Now the assertion is proved.
(assume "Assertion" "xs")
(use "Assertion" (pt "Lh xs"))
(use "Truth")
;; Proof finished.
;; (cdp)
(save "ListZeroLtLhToMainLastId")

(add-var-name "xss" (py "list list alpha"))

(add-program-constant "ListHeads" (py "list list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListHeads" "Heads")
(add-computation-rules
 "Heads(Nil list alpha)" "(Nil alpha)"
 "Heads(xs::xss)" "Head xs::Heads xss")

;; 2020-07-13.  Commented out, since we do not have ListHeadTotal.
;; (set-totality-goal "ListHeads")
;; (assume "xss^" "Txss")
;; (elim "Txss")
;; (use "TotalListNil")
;; (assume "xs^" "Txs" "xss^1" "Txss1" "IH")
;; (ng #t)
;; (use "TotalListCons")
;; (use "ListHeadTotal")
;; (use "Txs")
;; (use "IH")
;; ;; Proof finished.
;; ;; (cdp)
;; (save-totality)

;; We also define ListPHeads (p for proper), which ignores heads of
;; empty lists.

(add-program-constant
 "ListPHeads" (py "list list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListPHeads" "PHeads")
(add-computation-rules
 "PHeads(Nil list alpha)" "(Nil alpha)"
 "PHeads((Nil alpha)::xss)" "PHeads xss"
 "PHeads((x::xs)::xss)" "x::PHeads xss")

(set-totality-goal "ListPHeads")
(assume "xss^" "Txss")
(elim "Txss")
(use "TotalListNil")
(assume "xs^" "Txs")
(elim "Txs")
(assume "xss^1" "Txss1" "IH")
(ng #t)
(use "IH")
(assume "x^" "Tx" "xs^1" "Txs1" "Useless" "xss^1" "Txss1" "IH")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

(add-program-constant "ListInit" (py "nat=>list alpha=>list alpha") t-deg-zero)
(add-infix-display-string "ListInit" "init" 'mul-op)
(add-computation-rules
 "0 init xs" "(Nil alpha)"
 "Succ n init(Nil alpha)" "(Nil alpha)"
 "Succ n init(x::xs)" "x::n init xs")

;; Above there is a similar ListBar.  Difference: in case the number n
;; is larger than the length, ListInit returns the original list
;; whereas ListBar appends Inhab's.

;; (pp (nt (pt "7 init(0::1::2::3::4:)")))
;; 0::1::2::3::4:

;; (pp (nt (pt "(0::1::2::3::4:)bar 7")))
;; 0::1::2::3::4::(Inhab nat)::(Inhab nat):

(set-totality-goal "ListInit")
(use "AllTotalElim")
(ind)
(ng)
(strip)
(use "TotalListNil")
(assume "n" "IHn" "xs^" "Txs")
(elim "Txs")
(ng)
(use "TotalListNil")
(assume "x^" "Tx" "xs^1" "Txs1" "Useless")
(ng)
(use "TotalListCons")
(use "Tx")
(use "IHn")
(use "Txs1")
;; Proof finished.
;; (cdp)
(save "ListInitTotal")

(add-program-constant "ListRest" (py "nat=>list alpha=>list alpha") t-deg-zero)
(add-infix-display-string "ListRest" "rest" 'mul-op)
(add-computation-rules
 "0 rest xs" "xs"
 "Succ n rest(Nil alpha)" "(Nil alpha)"
 "Succ n rest(x::xs)" "n rest xs")

(set-totality-goal "ListRest")
(use "AllTotalElim")
(ind)
(ng)
(assume "xs^" "Txs")
(use "Txs")
(assume "n" "IHn" "xs^" "Txs")
(elim "Txs")
(ng)
(use "TotalListNil")
(assume "x^" "Tx" "xs^1" "Txs1" "Useless")
(ng)
(use "IHn")
(use "Txs1")
;; Proof finished.
;; (cdp)
(save-totality)

;; (pp (nt (pt "1 init(5::6::7::8::9:)")))
;; 5:
;; (pp (nt (pt "1 rest(5::6::7::8::9:)")))
;; 6::7::8::9:

;; (pp (nt (pt "7 init(5::6::7::8::9:)")))
;; (pp (nt (pt "7 rest(5::6::7::8::9:)")))
;; (pp (nt (pt "0 init(5::6::7::8::9:)")))
;; (pp (nt (pt "0 rest(5::6::7::8::9:)")))

;; ListAppdInitRest
(set-goal "all n,xs xs eqd n init xs++(n rest xs)")
(ind)
(ng)
(assume "xs")
(use "InitEqD")
(assume "n" "IHn")
(ind)
(ng)
(use "InitEqD")
(assume "x" "xs" "IHxs")
(ng)
(simp "<-" "IHn")
(use "InitEqD")
;; Proof finished
;; (cdp)
(save "ListAppdInitRest")

;; ListAppdInitRestPartial
(set-goal
 "all n allnc xs^(STotalList xs^ -> xs^ eqd n init xs^ ++(n rest xs^))")
(ind)
(ng)
(assume "xs^" "STxs")
(elim "STxs")
(use "InitEqD")
(strip)
(use "InitEqD")
(assume "n" "IHn" "xs^" "STxs")
(elim "STxs")
(ng)
(use "InitEqD")
(assume "x^1" "xs^1" "STxs1" "IH")
(ng)
(simp "<-" "IHn")
(use "InitEqD")
(use "STxs1")
;; Proof finished.
;; (cdp)
(save "ListAppdInitRestPartial")

;; ListLhAppdSinglePartial
(set-goal "allnc xs^,x^(STotalList xs^ -> Lh(xs^ ++x^ :)eqd Succ Lh xs^)")
(assume "xs^" "x^" "STxs")
(elim "STxs")
(ng)
(use "InitEqD")
(assume "x^1" "xs^1" "STxs1" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListLhAppdSinglePartial")

;; ListLhRevPartial
(set-goal "allnc xs^(STotalList xs^ -> Lh(Rev xs^)eqd Lh xs^)")
(assume "xs^" "STxs")
(elim "STxs")
(use "InitEqD")
(assume "x^1" "xs^1" "STxs1" "IH")
(ng)
(simp "ListLhAppdSinglePartial")
(simp "IH")
(use "InitEqD")
(use "ListRevSTotal")
(use "STxs1")
;; Proof finished.
;; (cdp)
(save "ListLhRevPartial")

;; ListLhAppdPartial
(set-goal "allnc xs^1(STotalList xs^1 -> allnc xs^2(STotalList xs^2 ->
 Lh(xs^1++xs^2) eqd Lh xs^1+Lh xs^2))")
(assume "xs^1" "STxs1")
(elim "STxs1")
(assume "xs^2" "STxs2")
(elim "STxs2")
(use "InitEqD")
(assume "x^" "xs^3" "STxs3" "IH")
(ng)
(simp "<-" "IH")
(use "InitEqD")
;; 4
(assume "x^1" "xs^11" "STxs11" "IH1" "xs^2" "STxs2")
(elim "STxs2")
(ng)
(simp "IH1")
(ng)
(use "InitEqD")
(use "STotalListNil")
(assume "x^2" "xs^3" "STxs3" "IH2")
(ng)
(simp "IH1")
(ng)
(simp "<-" "IH2")
(simp "IH1")
(use "InitEqD")
(use "STxs3")
(use "STotalListCons")
(use "STxs3")
;; Proof finished.
;; (cdp)
(save "ListLhAppdPartial")

;; ListInitLh
(set-goal "all xs Lh xs init xs eqd xs")
(ind)
(use "InitEqD")
(assume "x" "xs" "IHxs")
(ng)
(simp "IHxs")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListInitLh")
(add-rewrite-rule "Lh xs init xs" "xs")

;; ListInitLhPartial
(set-goal "allnc xs^(STotalList xs^ -> Lh xs^ init xs^ eqd xs^)")
(assume "xs^" "STxs")
(elim "STxs")
(ng)
(use "InitEqD")
(assume "x^" "xs^1" "STxs1")
(ng)
(assume "EqHyp")
(simp "EqHyp")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListInitLhPartial")

;; ListRestLh
(set-goal "all xs Lh xs rest xs eqd(Nil alpha)")
(ind)
(use "InitEqD")
(assume "x" "xs" "IHxs")
(ng)
(simp "IHxs")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListRestLh")
(add-rewrite-rule "Lh xs rest xs" "(Nil alpha)")

;; ListLhInit
(set-goal "all xs,n(n<=Lh xs -> Lh(n init xs)=n)")
(ind)
(ng)
(assume "n" "n=0")
(simp "n=0")
(use "Truth")
(assume "x" "xs" "IHxs")
(ng)
(cases)
(ng)
(assume "Useless")
(use "Useless")
(use "IHxs")
;; Proof finished.
;; (cdp)
(save "ListLhInit")

;; ListLhRest
(set-goal "all xs,n(n<=Lh xs -> Lh(n rest xs)=Lh xs--n)")
(ind)
(ng)
(assume "n" "n=0")
(simp "n=0")
(use "Truth")
(assume "x" "xs" "IHxs")
(ng)
(cases)
(ng)
(assume "Useless")
(use "Useless")
(use "IHxs")
;; Proof finished.
;; (cdp)
(save "ListLhRest")

;; ListInitAppd
(set-goal "all xs1,xs2 Lh xs1 init(xs1++xs2) eqd xs1")
(ind)
(ng)
(assume "xs")
(use "InitEqD")
(assume "x" "xs" "IH" "xs2")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListInitAppd")

;; ListInitAppdPartial
(set-goal "allnc xs^1,xs^2(
 STotalList xs^1 -> Lh xs^1 init(xs^1++xs^2) eqd xs^1)")
(assume "xs^1" "xs^2" "Txs1")
(elim "Txs1")
(ng)
(use "InitEqD")
(assume "x^" "xs^" "Txs" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListInitAppdPartial")

;; ListInitAppdGen
(set-goal "all n,xs1,xs2(n<=Lh xs1 -> n init(xs1++xs2)eqd n init xs1)")
(ind)
(ng)
(strip)
(use "InitEqD")
(assume "n" "IHn")
(cases)
(ng #t)
(assume "xs1")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "x" "xs1" "xs2")
(ng)
(assume "n<=Lh xs1")
(simp "IHn")
(use "InitEqD")
(use "n<=Lh xs1")
;; Proof finished.
;; (cdp)
(save "ListInitAppdGen")

;; ListInitPlusAppdPartial
(set-goal "all n allnc xs^1(STotalList xs^1 ->
 allnc xs^2((n+Lh xs^1)init(xs^1 ++xs^2)eqd xs^1++(n init xs^2)))")
(assume "n" "xs^1" "STxs1")
(elim "STxs1")
(ng)
(strip)
(use "InitEqD")
;; 4
(assume "x^" "xs^2" "STxs2" "IH" "xs^")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListInitPlusAppdPartial")

;; ListInitPlusAppd
(set-goal
 "all n allnc xs1,xs^2 (n+Lh xs1)init(xs1 ++xs^2)eqd xs1++(n init xs^2)")
(assume "n" "xs1" "xs^2")
(use "ListInitPlusAppdPartial")
(use "ListSTotalVar")
;; Proof finished.
;; (cdp)
(save "ListInitPlusAppd")

;; ListRestAppd
(set-goal "all xs1,xs2 Lh xs1 rest(xs1++xs2) eqd xs2")
(ind)
(ng)
(assume "xs")
(use "InitEqD")
(assume "x" "xs" "IH" "xs2")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListRestAppd")

;; ListRestAppdPartial
(set-goal "allnc xs^1,xs^2(
 STotalList xs^1 -> Lh xs^1 rest(xs^1++xs^2) eqd xs^2)")
(assume "xs^1" "xs^2" "Txs1")
(elim "Txs1")
(ng)
(use "InitEqD")
(assume "x^" "xs^" "Txs" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListRestAppdPartial")

;; ListRestAppdGen
(set-goal
 "allnc n^ all xs1 allnc xs^2 (n^ +Lh xs1)rest(xs1++xs^2) eqd n^ rest xs^2")
(assume "n^")
(ind)
(ng)
(assume "xs^2")
(use "InitEqD")
(assume "x" "xs1" "IHxs1" "xs^2")
(ng)
(use "IHxs1")
;; Proof finished.
;; (cdp)
(save "ListRestAppdGen")

;; ListLhInitRestEq
(set-goal "all xs(NatEven Lh xs ->
 Lh(NatHalf Lh xs init xs)=
 Lh(NatHalf Lh xs rest xs))")
(assume "xs" "Exs")
(simp "ListLhInit")
(simp "ListLhRest")
(use "NatPlusCancelR" (pt "NatHalf Lh xs"))
(simp "NatMinusPlusEq")
(simp "NatDoublePlusEq")
(use "NatDoubleHalfEven")
(use "Exs")
(use "NatHalfLe")
(use "NatHalfLe")
(use "NatHalfLe")
;; Proof finshed.
;; (cdp)
(save "ListLhInitRestEq")

;; Now ListFilter

(add-var-name "xtop" (py "alpha=>boole"))

(add-program-constant
 "ListFilter" (py "(alpha=>boole)=>list alpha=>list alpha") t-deg-zero)
(add-infix-display-string "ListFilter" "filter" 'pair-op) ;right associative
(add-computation-rules
 "xtop filter(Nil alpha)" "(Nil alpha)"
 "xtop filter x::xs" "[if (xtop x) (x::xtop filter xs) (xtop filter xs)]")

;; ListFilterTotal
(set-goal
 (rename-variables (term-to-totality-formula (pt "(ListFilter alpha)"))))

;; allnc xtop^(
;;      allnc x^(Total x^ -> TotalBoole(xtop^ x^)) -> 
;;      allnc xs^(TotalList xs^ -> TotalList(xtop^ filter xs^)))

(assume "xtop^" "Txtop" "xs^" "Txs")
(elim "Txs")
;; 3,4
(ng #t)
(use "TotalListNil")
;; 4
(assume "x^1" "Tx1" "xs^1" "Txs1" "IH")
(ng #t)
(use "BooleIfTotal")
(use "Txtop")
(use "Tx1")
(use "TotalListCons")
(use "Tx1")
(use "IH")
(use "IH")
;; Proof finished.
;; (cdp)
;; (save "ListFilterTotal")
(save-totality)

;; ok, ListFilterTotal has been added as a new theorem.
;; ok, computation rule xtop filter(Nil alpha) -> (Nil alpha) added
;; ok, computation rule xtop filter x::xs ->
;; [if (xtop x) (x::xtop filter xs) (xtop filter xs)] added

;; (term-to-t-deg (pt "(ListFilter alpha)"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [xtop,xs]
;;  (Rec list alpha=>list alpha)xs(Nil alpha)
;;  ([x,xs0,xs1][if (xtop x) (x::xs1) xs1])

;; Moreover we have extensionality of ListFilter:

;; Need (in ets.scm)

;; BooleIfREqPList
(set-goal
 "allnc p^1,p^2(
     EqPBoole p^1 p^2 -> 
     allnc xs^11,xs^21(
      (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^11 xs^21 -> 
      allnc xs^12,xs^22(
       (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^12 xs^22 -> 
       (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))
       [if p^1 xs^11 xs^12]
       [if p^2 xs^21 xs^22])))")
(assume "p^1" "p^2" "EqPp1p2")
(elim "EqPp1p2")
;; 3,4
(ng #t)
(search)
;; 4
(ng #t)
(search)
;; Proof finished.
;; (cdp)
(save "BooleIfREqPList")

;; ListFilterExt
(set-goal (rename-variables
	   (terms-to-eqp-formula
	    (pt "(ListFilter alpha)") (pt "(ListFilter alpha)"))))

;; allnc xtop^,xtop^0(
;;      allnc x^,x^0(EqP x^ x^0 -> EqPBoole(xtop^ x^)(xtop^0 x^0)) -> 
;;      allnc xs^,xs^0(
;;       (REqPList (cterm (x^,x^0) EqP x^ x^0))xs^ xs^0 -> 
;;       (REqPList (cterm (x^,x^0) EqP x^ x^0))(xtop^ filter xs^)
;;       (xtop^0 filter xs^0)))

(assume "xtop^1" "xtop^2" "EqPBooleHyp" "xs^1" "xs^2" "REqPHyp")
(elim "REqPHyp")
;; 3,4
(ng #t)
(use "REqPListNil")
;; 4
(assume "x^1" "x^2" "EqPHyp" "xs^3" "xs^4" "H1" "H2")
(ng #t)
(use-with
 "BooleIfREqPList"
 (py "alpha")
 (make-cterm (pv "x^1") (pv "x^2") (pf "EqP x^1 x^2"))
 (pt "xtop^1 x^1")  (pt "xtop^2 x^2") "?"
 (pt "(x^1::xtop^1 filter xs^3)") (pt "(x^2::xtop^2 filter xs^4)") "?"
 (pt "xtop^1 filter xs^3") (pt "xtop^2 filter xs^4") "?")
(use "EqPBooleHyp")
(use "EqPHyp")
(use-with
 "REqPListCons"
 (py "alpha")
 (make-cterm (pv "x^1") (pv "x^2") (pf "EqP x^1 x^2"))
 (pt "x^1") (pt "x^2") "EqPHyp" 
 (pt "xtop^1 filter xs^3") (pt "xtop^2 filter xs^4") "?")
(use "H2")
(use "H2")
;; Proof finished.
;; (cdp)
(save "ListFilterExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [xtop,xs]
;;  (Rec list alpha=>list alpha)xs(Nil alpha)
;;  ([x,xs0,xs1](cBooleIfREqPList alpha)(xtop x)(x::xs1)xs1)

(add-var-name "fst" (py "alpha1=>alpha2=>alpha1"))
(add-var-name "snd" (py "alpha1=>alpha2=>alpha2"))

;; (Foldl bin-op init-val list).  If list is empty, return init-val.
;; If not, apply ListFoldl with (i) initial value: the result of
;; applying bin-op to init-val and the head of list and (ii) the tail
;; of the list.

(add-program-constant
 "Foldl" (py "(alpha1=>alpha2=>alpha1)=>alpha1=>list alpha2=>alpha1")
 t-deg-zero)
(add-computation-rules
 "(Foldl alpha1 alpha2)fst y(Nil alpha2)" "y"
 "(Foldl alpha1 alpha2)fst y(z::zs)" "(Foldl alpha1 alpha2)fst(fst y z)zs")

;; FoldLTotal
(set-totality-goal "Foldl")

;; allnc fst^(
;;      allnc y^(Total y^ -> allnc z^(Total z^ -> Total(fst^ y^ z^))) -> 
;;      allnc y^(
;;       Total y^ -> 
;;       allnc zs^(TotalList zs^ -> Total((Foldl alpha1 alpha2)fst^ y^ zs^))))

(assume "fst^" "Tfst")
(assert "allnc zs^(TotalList zs^ ->
 allnc y^(Total y^ -> Total((Foldl alpha1 alpha2)fst^ y^ zs^)))")
(assume "zs^" "Tzs")
(elim "Tzs")
;; 6,7
(assume "y^" "Ty")
(ng #t)
(use "Ty")
;; 7
(assume "z^1" "Tz1" "zs^1" "Tzs1" "IH" "y^" "Ty")
(ng #t)
(use "IH")
(use "Tfst")
(use "Ty")
(use "Tz1")
;; Assertion proved.
(assume "Assertion" "y^" "Ty" "zs^" "Tzs")
(use "Assertion")
(use "Tzs")
(use "Ty")
;; Proof finished.
;; (cdp)
(save-totality)

;; (term-to-t-deg (pt "(Foldl alpha1 alpha2)"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [fst,y,zs]
;;  (Rec list alpha2=>alpha1=>alpha1)zs([y0]y0)
;;  ([z,zs0,(alpha1=>alpha1),y0](alpha1=>alpha1)(fst y0 z))
;;  y

;; Moreover we have extensionality of FoldlExt:

;; FoldlExt
(set-goal
 (rename-variables (terms-to-eqp-formula (pt "(Foldl alpha1 alpha2)")
					 (pt "(Foldl alpha1 alpha2)"))))

;; allnc fst^,fst^0(
;;      allnc y^,y^0(
;;       EqP y^ y^0 -> 
;;       allnc z^,z^0(EqP z^ z^0 -> EqP(fst^ y^ z^)(fst^0 y^0 z^0))) -> 
;;      allnc y^,y^0(
;;       EqP y^ y^0 -> 
;;       allnc zs^,zs^0(
;;        (REqPList (cterm (z^,z^0) EqP z^ z^0))zs^ zs^0 -> 
;;        EqP((Foldl alpha1 alpha2)fst^ y^ zs^)
;;        ((Foldl alpha1 alpha2)fst^0 y^0 zs^0))))

(assume "fst^1" "fst^2" "EqPfst1fst2")
(assert "allnc zs^,zs^0(
     (REqPList (cterm (z^,z^0) EqP z^ z^0))zs^ zs^0 -> 
     allnc y^,y^0(
      EqP y^ y^0 -> 
      EqP((Foldl alpha1 alpha2)fst^1 y^ zs^)
      ((Foldl alpha1 alpha2)fst^2 y^0 zs^0)))")
(assume "zs^1" "zs^2" "EqPzs1zs2")
(elim "EqPzs1zs2")
;; 6,7
(assume "y^1" "y^2" "EqPy1y2")
(ng #t)
(use "EqPy1y2")
;; 7
(assume "z^1" "z^2" "EqPz1z2" "zs^3" "zs^4" "EqPzs3zs4" "IH"
	"y^1" "y^2" "EqPy1y2")
(ng #t)
(use "IH")
(use "EqPfst1fst2")
(use "EqPy1y2")
(use "EqPz1z2")
;; Assertion proved.
(assume "Assertion" "y^1" "y^2" "EqPy1y2" "zs^1" "zs^2" "EqPzs1zs2")
(use "Assertion")
(use "EqPzs1zs2")
(use "EqPy1y2")
;; Proof finished.
;; (cdp)
(save "FoldlExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [fst,y,zs]
;;  (Rec list alpha2=>alpha1=>alpha1)zs([y0]y0)
;;  ([z,zs0,(alpha1=>alpha1),y0](alpha1=>alpha1)(fst y0 z))

;; (Foldr bin-op init-val list).  If list is empty, return init-val.
;; If not, apply bin-op to the head of list and the result of applying
;; Foldr to bin-op, init-val and the tail of the list.

(add-program-constant
 "Foldr" (py "(alpha1=>alpha2=>alpha2)=>alpha2=>list alpha1=>alpha2")
 t-deg-zero)
(add-computation-rules
 "(Foldr alpha1 alpha2)snd z(Nil alpha1)" "z"
 "(Foldr alpha1 alpha2)snd z(y::ys)" "snd y((Foldr alpha1 alpha2)snd z ys)") 

;; FoldRTotal
(set-totality-goal "Foldr")

;; allnc snd^(
;;      allnc y^(Total y^ -> allnc z^(Total z^ -> Total(snd^ y^ z^))) -> 
;;      allnc z^(
;;       Total z^ -> 
;;       allnc ys^(TotalList ys^ -> Total((Foldr alpha1 alpha2)snd^ z^ ys^))))

(assume "snd^" "Tsnd")
(assert "allnc ys^(
     TotalList ys^ -> 
     allnc z^(Total z^ -> Total((Foldr alpha1 alpha2)snd^ z^ ys^)))")
(assume "ys^" "Tys")
(elim "Tys")
;; 6,7
(assume "z^" "Tz")
(ng #t)
(use "Tz")
;; 7
(assume "y^1" "Ty1" "ys^1" "Tys1" "IH" "z^" "Tz")
(ng #t)
(use "Tsnd")
(use "Ty1")
(use "IH")
(use "Tz")
;; Assertion proved.
(assume "Assertion" "z^" "Tz" "ys^" "Tys")
(use "Assertion")
(use "Tys")
(use "Tz")
;; Proof finished.
;; (cdp)
(save-totality)

;; ok, FoldrTotal has been added as a new theorem.
;; ok, computation rule (Foldr alpha1 alpha2)snd z(Nil alpha1) -> z added
;; ok, computation rule (Foldr alpha1 alpha2)snd z(y::ys) ->
;;  snd y((Foldr alpha1 alpha2)snd z ys) added

;; (term-to-t-deg (pt "(Foldr alpha1 alpha2)"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [snd,z,ys]
;;  (Rec list alpha1=>alpha2=>alpha2)ys([z0]z0)
;;  ([y,ys0,(alpha2=>alpha2),z0]snd y((alpha2=>alpha2)z0))
;;  z

;; Moreover we have extensionality of FoldrExt:

;; FoldrExt
(set-goal
 (rename-variables (terms-to-eqp-formula (pt "(Foldr alpha1 alpha2)")
					 (pt "(Foldr alpha1 alpha2)"))))

;; allnc snd^,snd^0(
;;      allnc y^,y^0(
;;       EqP y^ y^0 -> 
;;       allnc z^,z^0(EqP z^ z^0 -> EqP(snd^ y^ z^)(snd^0 y^0 z^0))) -> 
;;      allnc z^,z^0(
;;       EqP z^ z^0 -> 
;;       allnc ys^,ys^0(
;;        (REqPList (cterm (y^,y^0) EqP y^ y^0))ys^ ys^0 -> 
;;        EqP((Foldr alpha1 alpha2)snd^ z^ ys^)
;;        ((Foldr alpha1 alpha2)snd^0 z^0 ys^0))))

(assume "snd^1" "snd^2" "EqPsnd1snd2")
(assert "allnc ys^,ys^0(
     (REqPList (cterm (y^,y^0) EqP y^ y^0))ys^ ys^0 -> 
     allnc z^,z^0(
      EqP z^ z^0 -> 
      EqP((Foldr alpha1 alpha2)snd^1 z^ ys^)
      ((Foldr alpha1 alpha2)snd^2 z^0 ys^0)))")
(assume "ys^1" "ys^2" "EqPys1ys2")
(elim "EqPys1ys2")
;; 6,7
(assume "z^1" "z^2" "EqPz1z2")
(ng #t)
(use "EqPz1z2")
;; 7
(assume "y^1" "y^2" "EqPy1y2" "ys^3" "ys^4" "EqPys3ys4" "IH"
	"z^1" "z^2" "EqPz1z2")
(ng #t)
(use "EqPsnd1snd2")
(use "EqPy1y2")
(use "IH")
(use "EqPz1z2")
;; Assertion proved.
(assume "Assertion" "z^1" "z^2" "EqPz1z2" "ys^1" "ys^2" "EqPys1ys2")
(use "Assertion")
(use "EqPys1ys2")
(use "EqPz1z2")
;; Proof finished.
;; (cdp)
(save "FoldrExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [snd,z,ys]
;;  (Rec list alpha1=>alpha2=>alpha2)ys([z0]z0)
;;  ([y,ys0,(alpha2=>alpha2),z0]snd y((alpha2=>alpha2)z0))

;; ListFrom m n returns the list of increasing natural numbers
;; starting from m of length n.

(add-program-constant "ListFrom" (py "nat=>nat=>list nat") t-deg-zero)
(add-computation-rules
 "ListFrom m 0" "(Nil nat)"
 "ListFrom m(Succ n)" "m::ListFrom(Succ m)n")

;; (pp (nt (pt "ListFrom 2 5")))
;; 2::3::4::5::6:

(set-totality-goal "ListFrom")
(assert "all n,m TotalList(ListFrom m n)")
 (ind)
 (assume "m")
 (use "TotalListNil")
 (assume "n" "IH" "m")
 (ng)
 (use "TotalListCons")
 (use "NatTotalVar")
 (use "IH")
(assume "Assertion")
(use "AllTotalElim")
(assume "n")
(use "AllTotalElim")
(assume "m")
(use "Assertion")
;; Proof finished.
;; (cdp)
(save-totality)

;; Some important concepts for list depend on a decidable equality for
;; the list elements and hence are defined for finitary algebras only.

(add-program-constant "ListNatIn" (py "nat=>list nat=>boole") t-deg-zero)
(add-infix-display-string "ListNatIn" "in" 'pair-op)
(add-computation-rules
 "n in(Nil nat)" "False"
 "n in(m::ns)" "[if (n=m) True (n in ns)]")

(set-totality-goal "ListNatIn")
(use "AllTotalElim")
(assume "n")
(use "AllTotalElim")
(ind)
(use "TotalBooleFalse")
(assume "m" "ns" "IHn")
(ng)
(cases (pt "n=m"))
(strip)
(use "TotalBooleTrue")
(strip)
(use "IHn")
;; Proof finished.
;; (cdp)
(save-totality)

(add-var-name "nss" (py "list list nat"))

;; ListListNatEqToEqD
(set-goal "all nss1,nss2(nss1=nss2 -> nss1 eqd nss2)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "ns1" "nss1" "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "ns1" "nss1" "IH")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(ng #t)
(assume "ns2" "nss2" "Conj")
(inst-with-to "Conj" 'left "ns1=ns2")
(inst-with-to "Conj" 'right "nss1=nss2")
(drop "Conj")
(assert "ns1 eqd ns2")
 (use "ListNatEqToEqD")
 (use "ns1=ns2")
(assume "ns1 eqd ns2")
(assert "nss1 eqd nss2")
 (use "IH")
 (use "nss1=nss2")
(assume "nss1 eqd nss2")
(elim "nss1 eqd nss2")
(assume "(list list nat)^1")
(elim "ns1 eqd ns2")
(assume "ns^")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListListNatEqToEqD")

(define (list-to-first lst)
  (and (pair? lst)
       (or (car lst) (list-to-first (cdr lst)))))

;; (list-to-first '(#f #f 1 #f 2 3)) ;1
;; (list-to-first '(#f #f)) ;#f

;; Computation rule for (Inhab list alpha) with CoRec, which can be
;; undelayed.  Extensionality w.r.t. colist alpha is a special case of
;; ListCoRecExtNc.

(add-computation-rules
 "(Inhab list alpha)"
 "(CoRec unit=>list alpha)Dummy
  ([unit]Inr((Inhab alpha)pair(InR unit (list alpha))unit))")

;; (pp (rename-variables (nt (undelay-delayed-corec (nt (pt "(Inhab list alpha)")) 3))))

;; (Inhab alpha)::
;; (Inhab alpha)::
;; (Inhab alpha)::
;; (CoRec unit=>list alpha)Dummy
;; ([unit]Inr((Inhab alpha)pair(InR unit (list alpha))unit))

;; Added 2021-06-14

;; To approximate Riemann integrable functions we use equidistant
;; partitions whose length is a power of two, denoted EL xs below.
;; For rational arguments we can view them as step functions.

;; A basic operation for step functions is refining them by doubling
;; each argument.

(add-program-constant "ListRef" (py "list alpha=>list alpha"))
(add-prefix-display-string "ListRef" "Ref")

(add-computation-rules
 "Ref(Nil alpha)" "(Nil alpha)"
 "Ref(x::xs)" "x::x::Ref xs")

(set-totality-goal "ListRef")
(fold-alltotal)
(ind)
(use "TotalVar")
(assume "x" "xs" "IH")
(ng)
(use "TotalListCons")
(use "TotalVar")
(use "TotalListCons")
(use "TotalVar")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

;; ListLhRef
(set-goal "all xs Lh(Ref xs)=NatDouble Lh xs")
(ind)
;; 2,3
(use "Truth")
;; 3
(assume "x" "xs" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "ListLhRef")

(add-program-constant "ListItRef" (py "nat=>list alpha=>list alpha"))
(add-infix-display-string "ListItRef" "rf" 'pair-op) ;right associative

(add-computation-rules
 "Zero rf xs" "xs"
 "Succ n rf xs" "Ref(n rf xs)")

;; (add-computation-rules
;;  "Zero rf xs" "xs"
;;  "Succ n rf(Nil alpha)" "(Nil alpha)"
;;  "Succ n rf(x::xs)" "x::x::(n rf xs)")

(set-totality-goal "ListItRef")
(fold-alltotal)
(ind)
(fold-alltotal)
(assume "xs")
(use "TotalVar")
(assume "n" "IH")
(fold-alltotal)
(assume "xs")
(ng)
(use "ListRefTotal")
(use "IH")
(use "TotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

(set-goal "all n(n rf(Nil alpha))eqd(Nil alpha)")
(ind)
;; 2,3
(use "InitEqD")
;; 3
(assume "n" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n rf(Nil alpha)" "(Nil alpha)")

;; We defined ItRef by Succ n rf xs=Ref(n rf xs).  An
;; alternative would be Succ n rf xs= n rf(Ref xs).  Generally
;; for iteration the latter follows from the former.

;; ListItRefEq
(set-goal "all xs,n (Succ n rf xs)eqd(n rf Ref xs)")
(assume "xs")
(ind)
(use "InitEqD")
(assume "n" "IH")
(simp "ListItRef1CompRule")
(simp "ListItRef1CompRule")
(simp "ListItRef1CompRule")
(simp "<-" "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListItRefEq")

;; ListItRefPlus
(set-goal "all xs,n,m (n+m rf xs)eqd(m rf n rf xs)")
(assume "xs" "n")
(ind)
(use "InitEqD")
(assume "m" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListItRefPlus")

;; ListItRefComm
(set-goal "all xs,n,m (n rf m rf xs)eqd(m rf n rf xs)")
(assume "xs" "n" "m")
(simp "<-" "ListItRefPlus")
(simp "<-" "ListItRefPlus")
(simp "NatPlusComm")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ListItRefComm")

;; Added 2021-09-14
;; ListLtLhRef
(set-goal "all xs(Zero<Lh xs -> Lh xs<Lh Ref xs)")
(assume "xs" "0<Lx")
(simp "ListLhRef")
(use "NatLtDouble")
(use "0<Lx")
;; Proof finished.
;; (cdp)
(save "ListLtLhRef")

;; (display-default-varnames)

;; nss: 	list list nat
;; snd: 	alpha1=>alpha2=>alpha2
;; fst: 	alpha1=>alpha2=>alpha1
;; xtop: 	alpha=>boole
;; xss: 	list list alpha
;; pstop: 	list boole=>boole
;; yf: 	nat=>alpha1
;; phi: 	alpha1=>alpha2
;; zs: 	list alpha2
;; z: 	alpha2
;; ys: 	list alpha1
;; y: 	alpha1
;; psi: 	alpha1=>list alpha1=>alpha2
;; nf: 	nat=>nat
;; ps: 	list boole
;; p: 	boole
;; ns: 	list nat
;; xf: 	nat=>alpha
;; xs: 	list alpha
;; x: 	alpha
;; n: 	nat

(remove-var-name "x" "xs" "xf" "nf" "psi" "y" "ys" "z" "zs" "phi" "yf"
		 "ps" "pstop" "ns" "p" "xss" "xtop" "fst" "snd" "nss")
