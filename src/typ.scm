;; 2021-10-16.  typ.scm
;; 2. Types
;; ========

;; Generally we consider typed theories only.  Types are built from
;; type variables and type constants by algebra type formation (alg
;; rho_1 ...  rho_n), arrow type formation (rho=>sigma) and product
;; type formation (rho@@sigma) (and possibly other type constructors).
;; We always have type constants atomic, existential, prop and
;; nulltype.  They will be used to assign types to formulas.  For
;; instance, all n n=0 receives the type nat=>atomic, and all n,m ex k
;; n+m=k receives the type nat=>nat=>existential.  The type prop is
;; used for predicate variables, e.g. R of arity nat,nat=>prop.  Types
;; of formulas will be necessary for normalization by evaluation of
;; proof terms.  The type nulltype will be useful when assigning to a
;; formula the type of a program to be extracted from a proof of this
;; formula.  Types not involving the types atomic, existential, prop
;; and nulltype are called object types.

;; Types always have the form (tag ...) where tag is one of tvar,
;; tconst, alg, arrow, star, and ... is a list with further
;; information.

(define tag car)

(define RESERVED-NAMES
  (list "=" "Total" "TotalNc" "CoTotal" "CoTotalNc" "TotalMR"
	"Equal" "EqP" "EqPNc" "CoEqP" "CoEqPNc" "EqPMR" "CoEqPMR"
	"E" "SE" "Rec" "CoRec" "coRec" "Destr"
	"GRec" "GRecGuard" "Ind" "Cases" "GInd" "Intro" "Elim"
	"Ex-Intro" "Ex-Elim"
	"all" "ex" "allnc" "excl" "exca"
	"exi" "exd" "exl" "exr" "exnc"
	"or" "ori" "ord" "orl" "orr" "oru" "ornc"
	"and" "andd" "andl" "andr" "andnc"
	"lambda" "left" "right" "lft" "rht" "cterm" "if"
	"Pvar" "MPC" "PROOF" "CLASSIC" "INTUITIONISTIC" "END" "LOAD"
	"INCLUDE" "SCHEME" "TYPE" "PRED" "ALGEBRA" "FUNCTION" "PARTIAL"
	"REWRITE" "SYNTAX" "PAIROP" "IMPOP" "OROP" "ANDOP" "RELOP"
	"ADDOP" "MULOP" "PREFIXOP" "POSTFIXOP" "CONST"))

(define (is-used? string additional-info sort)
  (let ((display-for-true (lambda x (apply comment x) #t)))
    (cond
     ((not (string? string))
      (myerror "is-used?" "string expected" string))
     ((member string RESERVED-NAMES)
      (myerror "is-used?" "reserved name" string))
     ((assoc string TYPE-VARIABLES)
      (if (eq? 'tvar sort)
	  (display-for-true "warning: already a type variable " string)
	  (myerror "is-used?" "already a type variable" string)))
     ((assoc string TYPE-CONSTANTS)
      (if (eq? 'type-constant sort)
	  (display-for-true "warning: already a type constant " string)
	  (myerror "is-used?" "already a type constant" string)))
     ((assoc string ALGEBRAS)
      (if (eq? 'algebra sort)
	  (display-for-true "warning: already an algebra " string)
	  (myerror "is-used?" "already an algebra" string)))
     ((assoc string CONSTRUCTORS)
      (if (eq? 'constructor sort)
	  (let* ((info (assoc string CONSTRUCTORS))
		 (constr (constr-name-and-tsubst-to-constr string '()))
		 (uninst-type (const-to-uninst-type constr)))
	    (myerror "is-used" "already a different constructor" string
		     "of type" uninst-type))
	  (myerror "is-used" "already a constructor" string)))
     ((assoc string VARIABLES)
      (let ((info (assoc string VARIABLES)))
	(if (eq? 'var sort)
	    (if (equal? (cadr info) additional-info)
 		(display-for-true
		 "warning: " string " already is a variable of type "
		 (type-to-string additional-info))
		(myerror
 		 "is-used?" "already a variable of different type"
 		 string additional-info))
	    (myerror "is-used?" "already a variable" string
		     "of type" (cadr info)))))
     ((assoc string PROGRAM-CONSTANTS)
      (let ((info (assoc string PROGRAM-CONSTANTS)))
	(if (eq? 'program-constant sort)
	    (let* ((pconst (cadr info))
		   (uninst-type (const-to-uninst-type pconst))
		   (t-deg (const-to-t-deg pconst))
		   (token-type (const-to-token-type pconst))
		   (arity (const-to-object-or-arity pconst)))
	      (if (equal? additional-info
			  (list uninst-type t-deg token-type arity))
		  (display-for-true "warning: program constant " string
				    " already introduced")
		  (myerror
		   "is-used?" "already a program constant with different data"
		   string)))
	    (myerror "is-used?" "already a program constant" string))))
     ((assoc string PREDCONST-NAMES)
      (let ((info (assoc string PREDCONST-NAMES)))
	(if (eq? 'predconst sort)
	    (let ((uninst-type (cadr info)))
	      (if (equal? additional-info uninst-type)
		  (display-for-true "warning: predconst " string
				    " already introduced")
		  (myerror
		   "is-used?" "already a predconst with different data"
		   string)))
	    (myerror "is-used?" "already a predconst" string))))
     ((assoc string IDS)
      (if (eq? 'idpredconst sort)
	  (display-for-true "warning: already an idpredconst " string)
	  (myerror "is-used?" "already an idpredconst" string)))
     ((assoc string PREDICATE-VARIABLES)
      (let ((info (assoc string PREDICATE-VARIABLES)))
	(if (eq? 'pvar sort)
	    (if (equal? (cadr info) additional-info)
		(display-for-true
		 "warning: " string
		 " already is a predicate variable of arity "
		 (arity-to-string additional-info))
		(myerror
		 "is-used?" "already a predicate variable of different arity"
		 string additional-info))
	    (myerror "is-used?" "already a predicate variable" string
		     "of arity" (cadr info)))))
     ((assoc string THEOREMS)
      (let ((formula (aconst-to-formula (cadr (assoc string THEOREMS)))))
	(if (eq? 'theorem sort)
	    (if (and (formula-form? additional-info)
		     (classical-formula=? formula additional-info))
		(display-for-true
		 "warning: " string " already is a theorem constant for "
		 (formula-to-string formula))
		(myerror
		 "is-used?" string "already is a theorem constant for"
		 formula))
	    (myerror "is-used?" "already a theorem constant" string))))
     ((assoc string GLOBAL-ASSUMPTIONS)
      (let ((formula (aconst-to-formula
		      (cadr (assoc string GLOBAL-ASSUMPTIONS)))))
	(if (eq? 'global-assumption sort)
	    (if (and (formula-form? additional-info)
		     (classical-formula=? formula additional-info))
		(display-for-true
		 "warning: " string " already is a global assumption for "
		 (formula-to-string formula))
		(myerror
		 "is-used?" string "already is a global assumption for"
		 formula))
	    (myerror "is-used?" "already a global assumption" string))))
     (else #f))))

;; Type variables

;; Type variable names are alpha, beta etc.  alpha is provided by default.
;; To have infinitely many type variables available, we allow appended
;; indices: alpha1, alpha2, alpha3,... will be type variables.

(define DEFAULT-TVAR-NAME "alpha")

(define TYPE-VARIABLES
  (list (list "gamma")
	(list "beta")
	(list DEFAULT-TVAR-NAME)))

(define (add-tvar-name . x)
  (if (null? x)
      (myerror "add-tvar-name" "arguments expected")
      (do ((l x (cdr l)))
	  ((null? l))
	(let ((string (car l)))
	  (if (and (string? string) (not (string=? string "")))
	      (if (is-used? string '() 'tvar)
		  *the-non-printing-object*
		  (begin
		    (set! TYPE-VARIABLES
			  (append TYPE-VARIABLES (list (list string))))
		    (add-token string 'tvar-name string)
		    (comment "ok, type variable " string " added")))
	      (myerror "add-tvar-name" "string expected" string))))))

(define atv add-tvar-name)

(define (remove-tvar-name . strings)
  (define (rtv1 tvar-name)
    (if (assoc tvar-name TYPE-VARIABLES)
	(begin (do ((l TYPE-VARIABLES (cdr l))
		    (res '() (let* ((info (car l))
				    (string (car info)))
			       (if (string=? string tvar-name)
				   res
				   (cons info res)))))
		   ((null? l) (set! TYPE-VARIABLES (reverse res))))
	       (remove-token tvar-name)
	       (comment "ok, type variable " tvar-name " is removed"))
	(multiline-comment
	 "remove-tvar-name" "type variable expected" tvar-name)))
  (for-each rtv1 strings))

(define rtv remove-tvar-name)

;; Type variables are implemented as lists ('tvar index name).  If a type
;; variable carries no index, we let the index be -1.  name is a string
;; (the name of the type variable), to be used for output.

;; To make sure that type variables generated by the system are different
;; from all previously introduced variables, we maintain a global counter
;; MAXTVARINDEX.  Whenever a type variable is created, e.g.alpha27, then
;; MAXTVARINDEX is incremented to at least 27.

(define MAXTVARINDEX -1)

;; Constructor, accessors and tests for type variables:

(define (make-tvar index name)
  (set! MAXTVARINDEX (max index MAXTVARINDEX))
  (list 'tvar index name))

(define (tvar-form? x) (and (pair? x) (eq? 'tvar (car x))))

(define tvar-to-index cadr)
(define tvar-to-name caddr)

;; Complete test:

(define (tvar? x)
  (and (list? x)
       (= 3 (length x))
       (let ((tag (car x))
	     (index (cadr x))
	     (name (caddr x)))
	 (and (eq? 'tvar tag)
	      (integer? index)
	      (<= -1 index)
	      (assoc name TYPE-VARIABLES)))))

;; For display we use

(define (tvar-to-string tvar)
  (let ((index (tvar-to-index tvar))
	(name (tvar-to-name tvar)))
    (if (= index -1)
	name
	(string-append name (number-to-string index)))))

;; To generate new type variables we use

(define (new-tvar)
  (make-tvar (+ 1 MAXTVARINDEX) DEFAULT-TVAR-NAME))

;; Type constants are implemented as lists ('tconst name).

(define TYPE-CONSTANTS
  (list (list "atomic") (list "existential") (list "prop") (list "nulltype")))

(define (make-tconst name) (list 'tconst name))
(define (tconst-form? x) (and (pair? x) (eq? 'tconst (car x))))
(define tconst-to-name cadr)

(define (nulltype? x) ;x is ('tconst "nulltype")
  (and (list? x) (= 2 (length x)) (eq? 'tconst (car x))
       (string? (cadr x)) (string=? "nulltype" (cadr x))))

;; Complete test:

(define (tconst? x)
  (and (list? x)
       (= 2 (length x))
       (let ((tag (car x))
	     (name (cadr x)))
	 (and (eq? 'tconst tag)
	      (assoc name TYPE-CONSTANTS)))))

;; Constructor, accessors and test for alg types:

(define (make-alg name . types) (cons 'alg (cons name types)))

(define alg-form-to-name cadr)
(define alg-form-to-types cddr)
(define (alg-form? x) (and (pair? x) (eq? 'alg (car x))))

;; Complete test:

(define (alg? x)
  (and (list? x)
       (<= 2 (length x))
       (let ((tag (car x))
	     (name (cadr x)))
	 (and (eq? 'alg tag)
	      (assoc name ALGEBRAS)
              (= (alg-name-to-arity name)
                 (length (alg-form-to-types x)))
	      (apply and-op (map type? (alg-form-to-types x)))))))

(define (ground-type? type) (memq (tag type) '(tvar tconst alg)))

;; Constructor and accessors for arrow types:

(define (make-arrow type1 type2) (list 'arrow type1 type2))

(define arrow-form-to-arg-type cadr)
(define arrow-form-to-val-type caddr)

(define (mk-arrow x . rest)
  (if (null? rest)
      x
      (make-arrow x (apply mk-arrow rest))))

;; arrow-form-to-arg-types computes the first (car x) arg-types from x

(define (arrow-form-to-arg-types type . x)
  (cond ((null? x)
	 (if (arrow-form? type)
	     (cons (arrow-form-to-arg-type type)
		   (arrow-form-to-arg-types (arrow-form-to-val-type type)))
	     '()))
	((and (integer? (car x)) (not (negative? (car x))))
	 (let ((n (car x)))
	   (do ((rho type (arrow-form-to-val-type rho))
		(i 0 (+ 1 i))
		(res '() (cons (arrow-form-to-arg-type rho) res)))
	       ((or (= n i) (not (arrow-form? rho)))
		(if (= n i)
		    (reverse res)
		    (myerror "arrow-form-to-arg-types:"
			     n "arg-types expected in"
			     type))))))
	(else (myerror "arrow-form-to-arg-types" "number expected" (car x)))))

;; arrow-form-to-final-val-type computes the final val-type (val-type
;; after removing the first (car x) arguments)

(define (arrow-form-to-final-val-type type . x)
  (cond ((null? x)
	 (if (arrow-form? type)
	     (arrow-form-to-final-val-type (arrow-form-to-val-type type))
	     type))
	((and (integer? (car x)) (not (negative? (car x))))
	 (let ((n (car x)))
	   (do ((rho type (arrow-form-to-val-type rho))
		(i 0 (+ 1 i))
		(res type (arrow-form-to-val-type res)))
	       ((or (= n i) (not (arrow-form? rho)))
		(if (= n i)
		    res
		    (myerror "arrow-form-to-final-val-type:"
			     n "arg-types expected in"
			     type))))))
	(else (myerror "arrow-form-to-final-val-type" "number expected"
		       (car x)))))

(define (type-to-arity type)
  (if (arrow-form? type)
      (+ 1 (type-to-arity (arrow-form-to-val-type type)))
      0))

(define (remove-nulltype-argtypes type)
  (let* ((argtypes (arrow-form-to-arg-types type))
	 (valtype (arrow-form-to-final-val-type type))
	 (proper-argtypes
	  (list-transform-positive argtypes
	    (lambda (t) (not (nulltype? (arrow-form-to-final-val-type t)))))))
    (apply mk-arrow (append proper-argtypes (list valtype)))))
;; (pp (remove-nulltype-argtypes (py "boole=>(alpha=>nulltype)=>unit")))
;; boole=>unit

;; Test:

(define (arrow-form? x)
  (and (list? x) (= 3 (length x)) (eq? 'arrow (car x))))

;; Constructor, accessors and test for star types:

(define (make-star type1 type2) (list 'star type1 type2))
(define star-form-to-left-type cadr)
(define star-form-to-right-type caddr)
(define (star-form? x) (and (list? x) (= 3 (length x)) (eq? 'star (car x))))

(define (mk-star . x)
  (cond ((null? x) (make-alg "unit"))
	((null? (cdr x)) (car x))
	(else (make-star (car x) (apply mk-star (cdr x))))))

;; Moreover we need

(define (type-form? x)
  (or (tvar-form? x)
      (tconst-form? x)
      (alg-form? x)
      (arrow-form? x)
      (star-form? x)))

;; Complete test:

(define (type? x)
  (and (type-form? x)
       (case (tag x)
	 ((tvar) (tvar? x))
	 ((tconst) (tconst? x))
	 ((alg) (alg? x))
	 ((arrow) (and (type? (arrow-form-to-arg-type x))
		       (type? (arrow-form-to-val-type x))))
	 ((star) (and (type? (star-form-to-left-type x))
		      (type? (star-form-to-right-type x))))
	 (else #f))))

(define (object-type? type)
  (case (tag type)
    ((tvar alg) #t)
    ((tconst) #f)
    ((arrow)
     (and (object-type? (arrow-form-to-arg-type type))
	  (object-type? (arrow-form-to-val-type type))))
    ((star)
     (and (object-type? (star-form-to-left-type type))
	  (object-type? (star-form-to-right-type type))))
    (else (myerror "object-type?" "type expected" type))))

(define (type-to-alg-names type)
  (case (tag type)
    ((tvar tconst) '())
    ((alg)
     (adjoin (alg-form-to-name type)
	     (apply union (map type-to-alg-names (alg-form-to-types type)))))
    ((arrow)
     (union (type-to-alg-names (arrow-form-to-arg-type type))
	    (type-to-alg-names (arrow-form-to-val-type type))))
    ((star)
     (union (type-to-alg-names (star-form-to-left-type type))
	    (type-to-alg-names (star-form-to-right-type type))))
    (else (myerror "type-to-alg-names" "type expected" type))))

(define (type-to-alg-with-simalg-names type)
  (case (tag type)
    ((tvar tconst) '())
    ((alg)
     (let ((names (alg-name-to-simalg-names (alg-form-to-name type)))
	   (types (alg-form-to-types type)))
       (append names (apply union (map type-to-alg-with-simalg-names types)))))
    ((arrow)
     (union (type-to-alg-with-simalg-names (arrow-form-to-arg-type type))
	    (type-to-alg-with-simalg-names (arrow-form-to-val-type type))))
    ((star)
     (union (type-to-alg-with-simalg-names (star-form-to-left-type type))
	    (type-to-alg-with-simalg-names (star-form-to-right-type type))))
    (else (myerror "type-to-alg-with-simalg-names" "type expected" type))))

(define (type-to-tvars type)
  (case (tag type)
    ((tvar) (list type))
    ((tconst) '())
    ((alg)
     (apply union (map type-to-tvars (alg-form-to-types type))))
    ((arrow)
     (union (type-to-tvars (arrow-form-to-arg-type type))
	    (type-to-tvars (arrow-form-to-val-type type))))
    ((star)
     (union (type-to-tvars (star-form-to-left-type type))
	    (type-to-tvars (star-form-to-right-type type))))
    (else (myerror "type-to-tvars" "type expected" type))))

(define (alg-name-to-spos-tvars alg-name)
  (let* ((typed-constr-names (alg-name-to-typed-constr-names alg-name))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (simalg-names (alg-name-to-simalg-names alg-name))
	 (tvars (alg-name-to-tvars alg-name))
	 (algs (map (lambda (name) (apply make-alg name tvars)) simalg-names))
	 (alg-tvars (map (lambda (x) (new-tvar)) simalg-names))
	 (constr-types-with-alg-tvars
	  (map (lambda (type) (type-gen-substitute
			       type (map list algs alg-tvars)))
	       constr-types))
	 (argtypes-with-alg-tvars
	  (apply union (map arrow-form-to-arg-types
			    constr-types-with-alg-tvars)))
	 (spos-tvars (apply union (map type-to-spos-tvars
				       argtypes-with-alg-tvars))))
    (set-minus spos-tvars alg-tvars)))

(define (alg-to-spos-tvars alg)
  (let* ((alg-name (alg-form-to-name alg))
	 (types (alg-form-to-types alg))
	 (spos-types (list-head types (length (alg-name-to-spos-tvars
					       alg-name)))))
    (apply union (map type-to-spos-tvars spos-types))))

(define (type-to-spos-tvars type)
  (case (tag type)
    ((tvar) (list type))
    ((tconst) '())
    ((alg) (alg-to-spos-tvars type))
    ((arrow) (type-to-spos-tvars (arrow-form-to-val-type type)))
    ((star) (union (star-form-to-left-type type)
		   (star-form-to-right-type type)))
    (else (myerror "type-to-spos-tvars" "type expected" type))))

;; For type-to-level we need

(define (alg-name-to-constr-arg-types alg-name)
  (let* ((typed-constr-names (alg-name-to-typed-constr-names alg-name))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (simalg-names (alg-name-to-simalg-names alg-name))
	 (tvars (alg-name-to-tvars alg-name))
	 (algs (map (lambda (name) (apply make-alg name tvars)) simalg-names))
	 (alg-tvars (map (lambda (x) (new-tvar)) simalg-names))
	 (constr-types-with-alg-tvars
	  (map (lambda (type) (type-gen-substitute
			       type (map list algs alg-tvars)))
	       constr-types)))
    (apply union (map arrow-form-to-arg-types constr-types-with-alg-tvars))))

(define (type-to-level type)
  (cond
   ((alg-form? type)
    (let* ((name (alg-form-to-name type))
	   (types (alg-form-to-types type))
	   (constr-arg-types (alg-name-to-constr-arg-types name))
	   (prevs (map type-to-level (union types constr-arg-types))))
      (foldr max 0 prevs)))
   ((arrow-form? type)
    (let* ((arg-type (arrow-form-to-arg-type type))
	   (val-type (arrow-form-to-val-type type))
	   (prev-arg (type-to-level arg-type))
	   (prev-val (type-to-level val-type)))
      (max (+ 1 prev-arg) prev-val)))
   ((ground-type? type) ;tvar or tconst
    0)
   (else (myerror "type-to-level" "type expected" type))))

;; Tests
;; (type-to-level (py "nat"))
;; (type-to-level (py "nat ysum nat"))
;; (type-to-level (py "nat ysum (boole=>nat)"))

;; For backwards compatibility we keep

(define (type-to-free type)
  (type-to-tvars type))

(define (type-gen-substitute type gen-tsubst)
  (let ((info (assoc type gen-tsubst)))
    (if info
	(cadr info)
	(cond
	 ((alg-form? type)
	  (let* ((alg-name (alg-form-to-name type))
		 (types (alg-form-to-types type)))
	    (apply make-alg alg-name (map (lambda (t)
					    (type-gen-substitute t gen-tsubst))
					  types))))
	 ((arrow-form? type)
	  (let ((arg-type (arrow-form-to-arg-type type))
		(val-type (arrow-form-to-val-type type)))
	    (make-arrow (type-gen-substitute arg-type gen-tsubst)
			(type-gen-substitute val-type gen-tsubst))))
	 ((star-form? type)
	  (let ((left-type (star-form-to-left-type type))
		(right-type (star-form-to-right-type type)))
	    (make-star (type-gen-substitute left-type gen-tsubst)
		       (type-gen-substitute right-type gen-tsubst))))
	 (else type)))))

(define (type-gen-subst type type1 type2)
  (type-gen-substitute type (list (list type1 type2))))

(define (constr-types-with-names-and-rest-names-to-inhabcrits
	 constr-types-with-names rest-names)
  (let* ((clause-choices
	  (map (lambda (constr-type-with-names)
		 (let* ((argtypes (arrow-form-to-arg-types
				   constr-type-with-names))
			(prev-crit-lists
			 (map (lambda (type)
				(apply type-to-inhabcrits type rest-names))
			      argtypes))
			(tvar-indep-prev-crit-lists
			 (map (lambda (prev-crits)
				(list-transform-positive prev-crits
				  (lambda (crit)
				    (null? (intersection crit rest-names)))))
			      prev-crit-lists)))
		   (choices tvar-indep-prev-crit-lists)))
	       constr-types-with-names))
	 (appended-clause-choices (apply append clause-choices)))
    (minima (lambda (x y) (null? (set-minus x y))) appended-clause-choices)))

(define (type-to-inhabcrits type-with-names . names)
  (cond
   ((alg-form? type-with-names)
    (let* ((alg-name (alg-form-to-name type-with-names))
	   (constr-types-with-names
	    (alg-name-to-constr-types-with-names alg-name))
	   (simalg-names (alg-name-to-simalg-names alg-name)))
      (constr-types-with-names-and-rest-names-to-inhabcrits
       constr-types-with-names simalg-names)))
   ((arrow-form? type-with-names)
    (apply type-to-inhabcrits (arrow-form-to-val-type type-with-names) names))
   ((tvar-form? type-with-names) (list (list type-with-names)))
   ((tconst-form? type-with-names) '(()))
   ((string? type-with-names) (list (list type-with-names)))
   (else (myerror "type-to-inhabcrits"
		  "alg-, arrow-, tvar or tconst-form or name expected"
		  type-with-names))))

(define (alg-name-to-constr-types-with-names alg-name)
  (let* ((typed-constr-names (alg-name-to-typed-constr-names alg-name))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (simalg-names (alg-name-to-simalg-names alg-name))
	 (tvars (alg-name-to-tvars alg-name))
	 (simalgs-with-tvars (map (lambda (simalg-name)
				    (apply make-alg simalg-name tvars))
				  simalg-names)))
    (map (lambda (constr-type)
	   (type-gen-substitute
	    constr-type (map list simalgs-with-tvars simalg-names)))
	 constr-types)))

;; As an intermediate step for the display functions we use token trees.

(define (make-token-tree tttag op-string . args)
  (cons tttag (cons op-string args)))
(define token-tree-to-tag car)
(define token-tree-to-op-string cadr)
(define token-tree-to-args cddr)

(define (type-to-token-tree type)
  (case (tag type)
    ((tvar) (make-token-tree 'atomic-type (tvar-to-string type)))
    ((tconst) (make-token-tree 'atomic-type (tconst-to-name type)))
    ((alg)
     (let* ((name (alg-form-to-name type))
	    (types (alg-form-to-types type))
	    (token-type (alg-name-to-token-type name)))
       (apply make-token-tree
	      token-type name
	      (map type-to-token-tree types))))
    ((arrow)
     (make-token-tree 'arrow-typeop "=>"
		      (type-to-token-tree (arrow-form-to-arg-type type))
		      (type-to-token-tree (arrow-form-to-val-type type))))
    ((star)
     (make-token-tree 'prod-typeop "@@"
		      (type-to-token-tree (star-form-to-left-type type))
		      (type-to-token-tree (star-form-to-right-type type))))
    (else (myerror "type-to-token-tree" "type expected" type))))

;; Generalities for substitutions

;; A substitution is a list ((x_1 t_1) ... (x_n t_n)) with distinct
;; variables x_i and such that for each i, x_i is different from to t_i.
;; The default domain equality is equal?

(define (make-substitution-wrt arg-val-equal? args vals)
  (if (not (and (list? args) (list? vals) (= (length args) (length vals))))
      (apply myerror "make-substitution-wrt" "lists of equal lengths expected"
	     (append
	      args
	      (list "of length" (length args))
	      vals
	      (list "of length" (length vals)))))
  (do ((l1 args (cdr l1))
       (l2 vals (cdr l2))
       (res '() (if (arg-val-equal? (car l1) (car l2))
		    res
		    (cons (list (car l1) (car l2)) res))))
      ((null? l1) (reverse res))))

(define (make-substitution args vals)
  (make-substitution-wrt equal? args vals))

(define (make-subst-wrt arg-val-equal? arg val)
  (make-substitution-wrt arg-val-equal? (list arg) (list val)))

(define (make-subst arg val) (make-subst-wrt equal? arg val))

(define empty-subst '())

(define (restrict-substitution-to-args subst args)
  (do ((l subst (cdr l))
       (res '() (if (member (caar l) args)
		    (cons (car l) res)
		    res)))
      ((null? l) (reverse res))))

(define (restrict-substitution-wrt subst test?)
  (do ((l subst (cdr l))
       (res '() (if (test? (caar l))
		    (cons (car l) res)
		    res)))
      ((null? l) (reverse res))))

(define (substitution-equal? subst1 subst2)
  (substitution-equal-wrt? equal? equal? subst1 subst2))

(define (substitution-equal-wrt? arg-equal? val-equal? subst1 subst2)
  (multiset-equal-wrt?
   (lambda (substpair1 substpair2)
     (let ((arg1 (car substpair1)) (val1 (cadr substpair1))
	   (arg2 (car substpair2)) (val2 (cadr substpair2)))
       (and (arg-equal? arg1 arg2) (val-equal? val1 val2))))
   subst1 subst2))

(define (subst-item-equal-wrt? arg-equal? val-equal? item1 item2)
  (and (arg-equal? (car item1) (car item2))
       (val-equal? (cadr item1) (cadr item2))))

(define (consistent-substitutions-wrt? arg-equal? val-equal? subst1 subst2)
  (let* ((args1 (map car subst1))
	 (args2 (map car subst2))
	 (common-args (intersection-wrt arg-equal? args1 args2)))
    (do ((l common-args (cdr l))
	 (res #t (let* ((arg (car l))
			(info1 (assoc-wrt arg-equal? arg subst1))
			(info2 (assoc-wrt arg-equal? arg subst2)))
		   (if (and info1 info2)
		       (val-equal? (cadr info1) (cadr info2))
		       #t))))
	((null? l) res))))

;; Composition (eta o theta) (eta past theta, or subst2 past subst1)
;; with theta = ((y_i v_i))_i and eta = ((z_j w_j))_j is defined as
;; follows.  (1) In the list ((y_i (v_i eta)))_i remove all bindings
;; (y_i (v_i eta)) with (v_i eta) = y_i.  (2) Append to the result the
;; list of all bindings (z_j w_j) with z_j not among the y_i.

(define (compose-substitutions topasubst1 topasubst2)
  (let* ((substitution-proc
	  (lambda (e s)
	    (cond ((type-form? e) (type-substitute e s))
		  ((term-form? e) (term-substitute e s))
		  ((cterm-form? e) (cterm-substitute e s))
		  ((proof-form? e) (proof-substitute e s))
		  (else
		   (myerror "compose-substitutions"
			    "type, term, cterm or proof expected" e)))))
	 (arg-val-equal?
	  (lambda (y v)
	    (cond ((tvar-form? y) (equal? y v))
		  ((var-form? y) (var-term-equal? y v))
		  ((pvar-form? y) (pvar-cterm-equal? y v))
		  ((avar-form? y) (avar-proof-equal? y v))
		  (else
		   (myerror "compose-substitutions" "variable expected" y)))))
	 (arg-equal?
	  (lambda (y v)
	    (cond ((tvar-form? y) (equal? y v))
		  ((var-form? y) (equal? y v))
		  ((pvar-form? y) (equal? y v))
		  ((avar-form? y) (avar=? y v))
		  (else
		   (myerror "compose-substitutions" "variable expected" y)))))
	 (new-topasubst1
	  (do ((l topasubst1 (cdr l))
	       (res
		'()
		(let ((val (if (admissible-substitution? topasubst2 (cadar l))
			       (substitution-proc (cadar l) topasubst2)
			       (myerror "compose-substitutions"
					"inadmissible substitution"
					topasubst2 "for" (cadar l)))))
		  (if (arg-val-equal? (caar l) val)
		      res
		      (cons (list (caar l) val) res)))))
	      ((null? l) (reverse res))))
	 (new-topasubst2
	  (do ((l topasubst2 (cdr l))
	       (res '() (if (assoc-wrt arg-equal? (caar l) topasubst1)
			    res
			    (cons (car l) res))))
	      ((null? l) (reverse res)))))
    (append new-topasubst1 new-topasubst2)))

;; avar-form? moved here from axiom.scm and proof-form? moved here from
;; proof.scm, since compose-substitutions is used in boole.scm when
;; adding computation-rules for "AndConst", and at that time neither
;; axiom.scm nor proof.scm is loaded.

(define (avar-form? x) (and (pair? x) (eq? 'avar (car x))))

(define (proof-form? x)
  (and (pair? x)
       (memq (tag x) '(proof-in-avar-form
		       proof-in-aconst-form
		       proof-in-imp-intro-form
		       proof-in-imp-elim-form
		       proof-in-impnc-intro-form
		       proof-in-impnc-elim-form
		       proof-in-and-intro-form
		       proof-in-and-elim-left-form
		       proof-in-and-elim-right-form
		       proof-in-all-intro-form
		       proof-in-all-elim-form
		       proof-in-allnc-intro-form
		       proof-in-allnc-elim-form))))

(define (compose-substitutions-and-beta-nf topasubst1 topasubst2)
  (let* ((substitution-proc
	  (lambda (e s)
	    (cond ((type-form? e) (type-substitute e s))
		  ((term-form? e) (term-to-beta-nf (term-substitute e s)))
		  ((cterm-form? e) (cterm-to-beta-nf (cterm-substitute e s)))
		  ((proof-form? e) (proof-substitute e s))
		  (else (myerror "compose-substitutions-and-beta-nf"
				 "type, term, cterm or proof expected" e)))))
	 (arg-val-equal?
	  (lambda (y v)
	    (cond ((tvar-form? y) (equal? y v))
		  ((var-form? y) (var-term-equal? y v))
		  ((pvar-form? y) (pvar-cterm-equal? y v))
		  ((avar-form? y) (avar-proof-equal? y v))
		  (else (myerror "compose-substitutions-and-beta-nf"
				 "variable expected" y)))))
	 (arg-equal?
	  (lambda (y v)
	    (cond ((tvar-form? y) (equal? y v))
		  ((var-form? y) (equal? y v))
		  ((pvar-form? y) (equal? y v))
		  ((avar-form? y) (avar=? y v))
		  (else (myerror "compose-substitutions-and-beta-nf"
				 "variable expected" y)))))
	 (new-topasubst1
	  (do ((l topasubst1 (cdr l))
	       (res
		'()
		(let ((val (if (admissible-substitution? topasubst2 (cadar l))
			       (substitution-proc (cadar l) topasubst2)
			       (myerror "compose-substitutions-and-beta-nf"
					"inadmissible substitution"
					topasubst2 "for" (cadar l)))))
		  (if (arg-val-equal? (caar l) val)
		      res
		      (cons (list (caar l) val) res)))))
	      ((null? l) (reverse res))))
	 (new-topasubst2
	  (do ((l topasubst2 (cdr l))
	       (res '() (if (assoc-wrt arg-equal? (caar l) topasubst1)
			    res
			    (cons (car l) res))))
	      ((null? l) (reverse res)))))
    (append new-topasubst1 new-topasubst2)))

(define (compose-substitutions-and-beta0-nf topasubst1 topasubst2)
  (let* ((substitution-proc
	  (lambda (e s)
	    (cond ((type-form? e) (type-substitute e s))
		  ((term-form? e) (term-substitute-and-beta0-nf e s))
		  ((cterm-form? e) (cterm-substitute-and-beta0-nf e s))
		  ((proof-form? e) (proof-substitute e s))
		  (else (myerror "compose-substitutions-and-beta0-nf"
				 "type, term, cterm or proof expected" e)))))
	 (arg-val-equal?
	  (lambda (y v)
	    (cond ((tvar-form? y) (equal? y v))
		  ((var-form? y) (var-term-equal? y v))
		  ((pvar-form? y) (pvar-cterm-equal? y v))
		  ((avar-form? y) (avar-proof-equal? y v))
		  (else (myerror "compose-substitutions-and-beta0-nf"
				 "variable expected" y)))))
	 (arg-equal?
	  (lambda (y v)
	    (cond ((tvar-form? y) (equal? y v))
		  ((var-form? y) (equal? y v))
		  ((pvar-form? y) (equal? y v))
		  ((avar-form? y) (avar=? y v))
		  (else (myerror "compose-substitutions-and-beta0-nf"
				 "variable expected" y)))))
	 (new-topasubst1
	  (do ((l topasubst1 (cdr l))
	       (res
		'()
		(let ((val (if (admissible-substitution? topasubst2 (cadar l))
			       (substitution-proc (cadar l) topasubst2)
			       (myerror "compose-substitutions-and-beta0-nf"
					"inadmissible substitution"
					topasubst2 "for" (cadar l)))))
		  (if (arg-val-equal? (caar l) val)
		      res
		      (cons (list (caar l) val) res)))))
	      ((null? l) (reverse res))))
	 (new-topasubst2
	  (do ((l topasubst2 (cdr l))
	       (res '() (if (assoc-wrt arg-equal? (caar l) topasubst1)
			    res
			    (cons (car l) res))))
	      ((null? l) (reverse res)))))
    (append new-topasubst1 new-topasubst2)))

(define (admissible-substitution? topasubst expr)
  (let* ((tsubst (list-transform-positive topasubst
		   (lambda (x) (tvar-form? (car x)))))
	 (topsubst (list-transform-positive topasubst
		     (lambda (x) (or (tvar-form? (car x))
				     (var-form? (car x))
				     (pvar-form? (car x)))))))
    (cond
     ((tvar-form? expr) #t)
     ((var-form? expr)
      (let* ((info (assoc expr topasubst))
	     (val-term (if info (cadr info) (make-term-in-var-form expr)))
	     (type (var-to-type expr)))
	(equal? (term-to-type val-term)
		(type-substitute type tsubst))))
     ((pvar-form? expr)
      (let* ((info (assoc expr topasubst))
	     (val-cterm (if info (cadr info) (pvar-to-cterm expr)))
	     (types (arity-to-types (pvar-to-arity expr))))
	(equal? (map var-to-type (cterm-to-vars val-cterm))
		(map (lambda (type) (type-substitute type tsubst))
		     types))))
     ((avar-form? expr)
      (let* ((info (assoc-wrt avar=? expr topasubst))
	     (val-proof (if info (cadr info) (make-proof-in-avar-form expr)))
	     (formula (avar-to-formula expr)))
	(formula=? (proof-to-formula val-proof)
		   (formula-substitute formula topsubst))))
     ((type-form? expr) #t)
     ((term-form? expr)
      (let ((free (term-to-free expr)))
	(apply and-op (map (lambda (var)
			     (admissible-substitution? topasubst var))
			   free))))
     ((formula-form? expr)
      (let ((free (formula-to-free expr))
	    (pvars (formula-to-pvars expr)))
	(and
	 (apply and-op (map (lambda (var)
			      (admissible-substitution? topasubst var))
			    free))
	 (apply and-op (map (lambda (pvar)
			      (admissible-substitution? topasubst pvar))
			    pvars)))))
     ((cterm-form? expr)
      (let ((free (cterm-to-free expr))
	    (pvars (formula-to-pvars (cterm-to-formula expr))))
	(and
	 (apply and-op (map (lambda (var)
			      (admissible-substitution? topasubst var))
			    free))
	 (apply and-op (map (lambda (pvar)
			      (admissible-substitution? topasubst pvar))
			    pvars)))))
     ((proof-form? expr)
      (let ((free (proof-to-free expr))
	    (pvars (proof-to-pvars expr))
	    (free-avars (proof-to-free-avars expr)))
	(and
	 (apply and-op (map (lambda (var)
			      (admissible-substitution? topasubst var))
			    free))
	 (apply and-op (map (lambda (pvar)
			      (admissible-substitution? topasubst pvar))
			    pvars))
	 (apply and-op (map (lambda (avar)
			      (admissible-substitution? topasubst avar))
			    free-avars)))))
     (else (myerror "admissible-substitution?" "unexpected expression"
		    expr)))))

;; check-admissible-tpsubst is a test function for tpsubsts.  If the
;; argument is not an admissible tpsubst, an error is returned.

(define (check-admissible-tpsubst x)
  (if (not (list? x))
      (myerror "check-admissible-tpsubst" "list expected" x))
  (for-each
   (lambda (item)
     (if (not (and (list? item) (= 2 (length item))))
	 (myerror "check-admissible-tpsubst"
		  "list of length 2 expected" item)))
   x)
  (for-each
   (lambda (item)
     (if (not (or (and (tvar? (car item)) (type? (cadr item)))
		  (and (pvar? (car item)) (cterm? (cadr item)))))
	 (myerror "check-admissible-tpsubst"
		  "list tvar - type or pvar - cterm expected" item)))
   x)
  (let* ((tvars (list-transform-positive (map car x) tvar-form?))
	 (types (list-transform-positive (map cadr x) type-form?))
	 (tsubst (make-substitution tvars types))
	 (pvars (list-transform-positive (map car x) pvar-form?))
	 (cterms (list-transform-positive (map cadr x) cterm-form?))
	 (pvar-cterm-alist (map (lambda (pvar cterm) (list pvar cterm))
				pvars cterms)))
    (for-each
     (lambda (item)
       (let* ((pvar (car item))
	      (cterm (cadr item))
	      (pvar-arity (pvar-to-arity pvar))
	      (cterm-arity (cterm-to-arity cterm))
	      (pvar-types (arity-to-types pvar-arity))
	      (cterm-types (arity-to-types cterm-arity)))
	 (if (not (= (length pvar-types) (length cterm-types)))
	     (myerror "check-admissible-tpsubst"
		      "arities of the same length expected"
		      pvar-arity cterm-arity))
	 (if (not (equal? cterm-types
			  (map (lambda (type) (type-substitute type tsubst))
			       pvar-types)))
	     (myerror "check-admissible-tpsubst"
		      "pvar-arity" pvar-arity
		      "and cterm-arity" cterm-arity
		      "do not correspond under tsubst" tsubst))))
     pvar-cterm-alist)))

;; In extend-subst we assume that arg and val are distinct.  The result
;; is the composition of subst with (var -> val).

(define (extend-subst subst arg val)
  (compose-substitutions subst (make-subst arg val)))

;; Type substitutions.  Complete test:

(define (tsubst? x)
  (and (list? x)
       (apply and-op (map (lambda (item)
			    (and (list? item)
				 (= 2 (length item))
				 (tvar? (car item))
				 (type? (cadr item))
				 (not (equal? (car item) (cadr item)))))
			  x))
       (= (length (remove-duplicates (map car x)))
	  (length x))))

(define (type-substitute type tsubst)
  (if
   (null? tsubst)
   type
   (case (tag type)
     ((tvar) (let ((info (assoc type tsubst)))
	       (if info (cadr info) type)))
     ((tconst) type)
     ((alg)
      (apply make-alg
	     (alg-form-to-name type)
	     (map (lambda (x) (type-substitute x tsubst))
		  (alg-form-to-types type))))
     ((arrow)
      (make-arrow (type-substitute (arrow-form-to-arg-type type) tsubst)
		  (type-substitute (arrow-form-to-val-type type) tsubst)))
     ((star)
      (make-star (type-substitute (star-form-to-left-type type) tsubst)
		 (type-substitute (star-form-to-right-type type) tsubst)))
     (else (myerror "type-substitute" "type expected" type)))))

(define (type-subst type tvar type1)
  (type-substitute type (make-subst tvar type1)))

;; A display function for type substitutions.

(define (display-t-substitution tsubst)
  (display-comment "Type substitution:") (newline)
  (for-each
   (lambda (x)
     (let* ((tvar (car x))
	    (type (cadr x)))
       (comment
	(tvar-to-string tvar) tab "->" tab (type-to-string type))))
   tsubst))

;; Type unification
;; ================

;; We need type-unify for object types only, that is, types built from
;; type variables and algebra types by arrow and star.  However, the
;; type constants "atomic" "existential" "prop" "nulltype" do not do
;; any harm and can be included.

;; modules/type-inf.scm contains a function type-unify as well.
;; However, there it is assumed that types are built from type
;; variables by arrow and star, hence equal type constants do not
;; unify.

(define (type-occurs? tvar type)
  (case (tag type)
    ((tvar) (equal? tvar type))
    ((alg) (apply or-op (map (lambda (x) (type-occurs? tvar x))
			     (alg-form-to-types type))))
    ((tconst) #f)
    ((arrow)
     (or (type-occurs? tvar (arrow-form-to-arg-type type))
	 (type-occurs? tvar (arrow-form-to-val-type type))))
    ((star)
     (or (type-occurs? tvar (star-form-to-left-type type))
	 (type-occurs? tvar (star-form-to-right-type type))))
    (else (myerror "type-occurs?" "type expected" type))))

;; type-unify checks whether two terms can be unified.  It returns #f,
;; if this is impossible, and a most general unifier otherwise.
;; type-unify-list does the same for lists of terms.

(define (type-disagreement-pair type1 type2)
  (cond
   ((and (tvar-form? type1) (tvar-form? type2))
    (if (equal? type1 type2) #f (list type1 type2)))
   ((and (alg-form? type1) (alg-form? type2))
    (if (string=? (alg-form-to-name type1) (alg-form-to-name type2))
	(type-disagreement-pair-l (alg-form-to-types type1)
				  (alg-form-to-types type2))
	(list type1 type2)))
   ((and (tconst-form? type1) (tconst-form? type2))
    (if (equal? type1 type2) #f (list type1 type2)))
   ((and (arrow-form? type1) (arrow-form? type2))
    (type-disagreement-pair-l
     (list (arrow-form-to-arg-type type1) (arrow-form-to-val-type type1))
     (list (arrow-form-to-arg-type type2) (arrow-form-to-val-type type2))))
   ((and (star-form? type1) (star-form? type2))
    (type-disagreement-pair-l
     (list (star-form-to-left-type type1) (star-form-to-right-type type1))
     (list (star-form-to-left-type type2) (star-form-to-right-type type2))))
   (else (list type1 type2))))

(define (type-disagreement-pair-l types1 types2)
  (cond
   ((null? types1)
    (if (null? types2)
	#f
	(myerror "type-disagreement-pair-l"
		 "typelists of equal length expected"
		 types1 types2)))
   ((null? types2)
    (myerror "type-disagreement-pair-l" "typelists of equal length expected"
	     types1 types2))
   (else (let ((a (type-disagreement-pair (car types1) (car types2))))
	   (if a
	       a
	       (type-disagreement-pair-l (cdr types1) (cdr types2)))))))

(define (type-unify type1 type2)
  (let type-unify-aux ((t1 type1) (t2 type2))
    (let ((p (type-disagreement-pair t1 t2)))
      (if (not p)
	  empty-subst
	  (let ((l (car p)) (r (cadr p)))
	    (cond ((and (tvar? l)
			(not (type-occurs? l r)))
		   (let* ((var l)
			  (prev (type-unify-aux (type-subst t1 var r)
						(type-subst t2 var r))))
		     (if prev
			 (extend-subst prev var r)
			 #f)))
		   ((and (tvar? r)
			 (not (type-occurs? r l)))
		    (let* ((var r)
			   (prev (type-unify-aux (type-subst t1 var l)
						 (type-subst t2 var l))))
		      (if prev
			  (extend-subst prev var l)
			  #f)))
		   (else #f)))))))

;; special handling for empty lists in type-unify-lists
(define (type-unify-list types1 types2)
  (if (null? types1)
      (if (null? types2)
          '()
          (myerror "type-unify-list"
		 "typelists of equal length expected"
		 types1 types2))
      (type-unify (apply mk-arrow types1)
                  (apply mk-arrow types2))))

;; Notice that this algorithm does not yield idempotent unifiers
;; (as opposed to the Martelli-Montanari algorithm in modules/type-inf.scm):

;; (pp-subst
;;  (type-unify (py "alpha1=>alpha2=>boole") (py "alpha2=>alpha1=>alpha1")))

;;   alpha2 -> boole
;;   alpha1 -> alpha2

;; Type-matching
;; =============

;; type-match checks whether a given pattern can be transformed by a
;; substitution into a given instance.  It returns #f, if this is
;; impossible, and the substitution otherwise.

;; type-match-aux is an auxiliary function.  It takes a list of patterns,
;; a list of instances, a list of identical variables at corresponding
;; locations, and the substitution built so far.

(define (type-match pattern instance)
  (type-match-aux (list pattern) (list instance) '() empty-subst))

(define (type-match-aux patterns instances sig-tvars tsubst)
  (if
   (null? patterns)
   tsubst
   (let ((pattern (car patterns))
	 (instance (if (pair? instances) (car instances)
		       (apply myerror
			      "type-match-aux"
			      "more instances expected for"
			      patterns))))
     (case (tag pattern)
       ((tvar)
	(cond
	 ((equal? pattern instance)
	  (type-match-aux (cdr patterns) (cdr instances)
			  (cons pattern sig-tvars) tsubst))
	 ((member pattern sig-tvars) #f)
	 ((assoc pattern tsubst)
	  (if (equal? instance (cadr (assoc pattern tsubst)))
	      (type-match-aux (cdr patterns) (cdr instances)
			      sig-tvars tsubst)
	      #f))
	 (else (type-match-aux
		(cdr patterns) (cdr instances) sig-tvars
		(append tsubst (list (list pattern instance)))))))
       ((tconst)
	(if (equal? pattern instance)
	    (type-match-aux (cdr patterns) (cdr instances) sig-tvars tsubst)
	    #f))
       ((alg)
	(if (alg-form? instance)
	    (let ((name1 (alg-form-to-name pattern))
		  (name2 (alg-form-to-name instance)))
	      (if (string=? name1 name2)
		  (let ((types1 (alg-form-to-types pattern))
			(types2 (alg-form-to-types instance)))
		    (type-match-aux
		     (append types1 (cdr patterns))
		     (append types2 (cdr instances))
		     sig-tvars tsubst))
		  #f))
	    #f))
       ((arrow)
	(if (arrow-form? instance)
	    (let ((arg-type1 (arrow-form-to-arg-type pattern))
		  (val-type1 (arrow-form-to-val-type pattern))
		  (arg-type2 (arrow-form-to-arg-type instance))
		  (val-type2 (arrow-form-to-val-type instance)))
	      (type-match-aux
	       (cons arg-type1 (cons val-type1 (cdr patterns)))
	       (cons arg-type2 (cons val-type2 (cdr instances)))
	       sig-tvars tsubst))
	    #f))
       ((star)
	(if (star-form? instance)
	    (let ((left-type1 (star-form-to-left-type pattern))
		  (right-type1 (star-form-to-right-type pattern))
		  (left-type2 (star-form-to-left-type instance))
		  (right-type2 (star-form-to-right-type instance)))
	      (type-match-aux
	       (cons left-type1 (cons right-type1 (cdr patterns)))
	       (cons left-type2 (cons right-type2 (cdr instances)))
	       sig-tvars tsubst))
	    #f))
       (else #f)))))

;; We also provide

(define (type-match-list patterns instances)
  (cond
   ((and (null? patterns) (null? instances))
     empty-subst)
   ((= (length patterns) (length instances))
    (type-match-aux patterns instances '() empty-subst))
   (else (apply myerror "type-match-list" "equal lengths expected"
		(append patterns instances)))))

(define (tsubst-match pattern-tsubst instance-tsubst)
  (let* ((tvars (remove-duplicates
		 (map car (append pattern-tsubst instance-tsubst))))
	 (patterns
	  (map (lambda (tvar) (let ((info (assoc tvar pattern-tsubst)))
				(if info (cadr info) tvar)))
	       tvars))
	 (instances
	  (map (lambda (tvar) (let ((info (assoc tvar instance-tsubst)))
				(if info (cadr info) tvar)))
	       tvars)))
    (type-match-list patterns instances)))

;; type-match-modulo-coercion checks whether a given pattern can be
;; transformed modulo coercion by a substitution into a given instance.
;; It returns #f, if this is impossible, and the substitution
;; otherwise.

;; type-match-modulo-coercion-aux is an auxiliary function.  It takes a
;; list of patterns, a list of instances, a list of identical variables
;; at corresponding locations, and the substitution built so far.

(define (type-match-modulo-coercion pattern instance)
  (type-match-modulo-coercion-aux
   (list pattern) (list instance) '() empty-subst))

(define (type-match-modulo-coercion-aux patterns instances sig-tvars tsubst)
  (if
   (null? patterns)
   tsubst
   (let ((pattern (car patterns))
	 (instance (if (pair? instances) (car instances)
		       (apply myerror
			      "type-match-modulo-coercion-aux"
			      "more instances expected for"
			      patterns))))
     (case (tag pattern)
       ((tvar)
	(cond
	 ((equal? pattern instance)
	  (type-match-modulo-coercion-aux (cdr patterns) (cdr instances)
					  (cons pattern sig-tvars) tsubst))
	 ((member pattern sig-tvars) #f)
	 ((assoc pattern tsubst)
	  (if (type-le? (cadr (assoc pattern tsubst)) instance)
	      (type-match-modulo-coercion-aux (cdr patterns) (cdr instances)
					      sig-tvars tsubst)
	      #f))
	 (else (type-match-modulo-coercion-aux
		(cdr patterns) (cdr instances) sig-tvars
		(append tsubst (list (list pattern instance)))))))
       ((tconst)
	(if (type-le? instance pattern)
	    (type-match-modulo-coercion-aux
	     (cdr patterns) (cdr instances) sig-tvars tsubst)
	    #f))
       ((alg)
	(if (alg-form? instance)
	    (if (type-le? instance pattern)
		(type-match-modulo-coercion-aux
		 (cdr patterns) (cdr instances) sig-tvars tsubst)
		(let ((name1 (alg-form-to-name pattern))
		      (name2 (alg-form-to-name instance)))
		  (if (string=? name1 name2)
		      (let ((types1 (alg-form-to-types pattern))
			    (types2 (alg-form-to-types instance)))
			(type-match-modulo-coercion-aux
			 (append types1 (cdr patterns))
			 (append types2 (cdr instances))
			 sig-tvars tsubst))
		      #f)))
	    #f))
       ((arrow)
	(if (arrow-form? instance)
	    (let ((arg-type1 (arrow-form-to-arg-type pattern))
		  (val-type1 (arrow-form-to-val-type pattern))
		  (arg-type2 (arrow-form-to-arg-type instance))
		  (val-type2 (arrow-form-to-val-type instance)))
	      (type-match-modulo-coercion-aux
	       (cons arg-type1 (cons val-type1 (cdr patterns)))
	       (cons arg-type2 (cons val-type2 (cdr instances)))
	       sig-tvars tsubst))
	    #f))
       ((star)
	(if (star-form? instance)
	    (let ((left-type1 (star-form-to-left-type pattern))
		  (right-type1 (star-form-to-right-type pattern))
		  (left-type2 (star-form-to-left-type instance))
		  (right-type2 (star-form-to-right-type instance)))
	      (type-match-modulo-coercion-aux
	       (cons left-type1 (cons right-type1 (cdr patterns)))
	       (cons left-type2 (cons right-type2 (cdr instances)))
	       sig-tvars tsubst))
	    #f))
       (else #f)))))

;; We allow (simultaneously defined) finitary and infinitary free
;; algebras as types.  They may depend on other type parameters
;; (e.g. list rho).  The freeness of the constructors is expressed by
;; requiring that their domains are disjoint, and that they are injective
;; (in particular non-strict) and total.

;; Equality is decidable for finitary algebras only.  Infinitary algebras
;; are to be treated similarly to arrow types.  For infinitary algebras
;; (extensional) equality is given by a predicate constant (schema), with
;; appropriate axioms.  In a finitary algebra equality is a (recursively
;; defined) constant.

;; The standard example for a finitary free algebra is the type nat of
;; unary natural numbers, with constructors Zero and Succ.  Objects of
;; type nat are essentially
;; - Zero or lists (Succ obj)
;; - term families

(define ALGEBRAS '())
(define OLD-ALGEBRAS '())

;; Format of ALGEBRAS:
;; ((alg-name simalg-names token-type
;;            (constr-name1 type1 <token-type1>)
;;            (constr-name2 type2 <token-type2>) ...) ...)
;; simalgs are the algebras defined simultaneously with alg (including
;; alg), and token-type is one of
;; postfix-typeop (arity 1)
;; prefix-typeop  (arity 1)
;; prod-typeop    (arity 2)
;; tensor-typeop  (arity 2)
;; sum-typeop     (arity 2)
;; alg     (arity an integer >=0)

(define (alg-name-to-simalg-names alg-name) (cadr (assoc alg-name ALGEBRAS)))
(define (alg-name-to-token-type alg-name) (caddr (assoc alg-name ALGEBRAS)))
(define (alg-name-to-typed-constr-names alg-name)
  (cdddr (assoc alg-name ALGEBRAS)))

(define (typed-constr-name-to-name y) (car y))
(define (typed-constr-name-to-type y) (cadr y))
(define (typed-constr-name-to-optional-token-type y) (cddr y))

(define (alg-name-to-tvars name)
  (let ((typed-constr-names (alg-name-to-typed-constr-names name)))
    (if (null? typed-constr-names) '()
	(let* ((typed-constr-name (car typed-constr-names))
	       (type (typed-constr-name-to-type typed-constr-name))
	       (val-type (arrow-form-to-final-val-type type)))
	  (alg-form-to-types val-type)))))

(define (alg-name-to-arity alg-name) (length (alg-name-to-tvars alg-name)))

(define (finalg? type . types)
  (or
   (member type types)
   (and
    (alg-form? type)
    (let* ((name (alg-form-to-name type))
	   (param-types (alg-form-to-types type))
	   (names (if (assoc name ALGEBRAS)
		      (alg-name-to-simalg-names name)
		      (myerror "finalg?" "alg name expected" name)))
	   (typed-constr-names ;all constructors are relevant
	    (apply union (map alg-name-to-typed-constr-names names)))
	   (constr-types (map typed-constr-name-to-type typed-constr-names))
	   (argtypes (apply union (map arrow-form-to-arg-types constr-types)))
	   (tvars (alg-name-to-tvars name))
	   (tsubst (make-substitution tvars param-types))
	   (subst-argtypes (map (lambda (argtype)
				  (type-substitute argtype tsubst))
				argtypes))
	   (algs (map (lambda (name) (apply make-alg name param-types))
		      names)))
      (apply and-op (map (lambda (subst-argtype)
			   (apply finalg? subst-argtype (append algs types)))
			 subst-argtypes))))))

;; sfinalg? checks whether type is a structure-finitary algebra.

(define (sfinalg? type)
  (and
   (alg-form? type)
   (let* ((name (alg-form-to-name type))
          (names (if (assoc name ALGEBRAS)
		     (alg-name-to-simalg-names name)
		     (myerror "sfinalg?" "alg name expected" name)))
          (typed-constr-names ;all constructors are relevant
           (apply union (map alg-name-to-typed-constr-names names)))
          (constr-types (map typed-constr-name-to-type typed-constr-names))
          (argtypes-lists (map arrow-form-to-arg-types constr-types))
          (not-param-type? ;filters non parameter types
           (lambda (x)
             (let ((val-type (arrow-form-to-final-val-type x)))
               (and (alg-form? val-type)
		    (member (alg-form-to-name val-type) names)))))
	  (argtypes-lists-wo-params
           (map (lambda (lst)
                  (list-transform-positive lst not-param-type?))
                argtypes-lists))
          (argargtypes-lists
           (map (lambda (lst)
                  (apply union (map arrow-form-to-arg-types lst)))
                argtypes-lists-wo-params))
          (argargtypes-union (apply union argargtypes-lists)))
     (null? argargtypes-union))))

(define (string-to-last-name string)
  (do ((l (reverse (string->list string)) (cdr l))
       (res '() (cons (car l) res)))
      ((or (null? l) (not (char-alphabetic? (car l))))
       (list->string res))))

(define (string-to-first-name string)
  (do ((l (string->list string) (cdr l))
       (res '() (cons (car l) res)))
      ((or (null? l) (not (char-alphabetic? (car l))))
       (list->string (reverse res)))))

;; (string-to-last-name "NatPlus1CompRule") ;"CompRule"
;; (string-to-first-name "NatPlus1CompRule") ;"NatPlus"

(define (type-string-to-new-tvar type-string)
  (let ((tvar (new-tvar)))
    (if (substring? (tvar-to-string tvar) type-string)
	(type-string-to-new-tvar type-string)
	tvar)))

(define (nested-alg-name? alg-name)
  (if (not (assoc alg-name ALGEBRAS))
      (myerror "nested-alg-name?" "alg-name expected" alg-name))
  (let* ((simalg-names (alg-name-to-simalg-names alg-name))
	 (typed-constr-names
	  (apply union (map alg-name-to-typed-constr-names simalg-names)))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (tvars (alg-name-to-tvars alg-name))
	 (algs (map (lambda (name) (apply make-alg name tvars)) simalg-names))
	 (alg-tvars (map (lambda (x) (new-tvar)) simalg-names))
	 (constr-types-with-alg-tvars
	  (map (lambda (type)
		 (type-gen-substitute type (map list algs alg-tvars)))
	       constr-types))
	 (argtypes-with-alg-tvars
	  (apply union (map arrow-form-to-arg-types
			    constr-types-with-alg-tvars))))
    (apply
     or-op
     (map (lambda (a) (pair? (intersection (type-to-tvars a) alg-tvars)))
	  (list-transform-positive (map arrow-form-to-final-val-type
					argtypes-with-alg-tvars)
	    alg-form?)))))

(define (coalg-name? name)
  (and (string=? "co" (substring name 0 2))
       (assoc (substring name 2 (string-length name)) ALGEBRAS)))
      
;; A cotype is like a type, except that some alg-names have received a
;; prefix co.  In formula-to-cotype this will indicate that at this
;; point the companion of a c.r. idpredconst appears.

(define (cotype-to-co-free? cotype)
  (case (tag cotype)
    ((tvar tconst) #t)
    ((alg) (let* ((name (alg-form-to-name cotype))
		  (cotypes (alg-form-to-types cotype)))
	     (and (not (coalg-name? name))
		  (apply and-op (map cotype-to-co-free? cotypes)))))
    ((arrow) (and (cotype-to-co-free? (arrow-form-to-arg-type cotype))
		  (cotype-to-co-free? (arrow-form-to-val-type cotype))))
    ((star) (and (cotype-to-co-free? (star-form-to-left-type cotype))
		 (cotype-to-co-free? (star-form-to-right-type cotype))))
    (else (myerror "cotype-to-co-free?" "cotype expected" cotype))))

(define (cotype-to-type cotype)
  (case (tag cotype)
    ((tvar tconst) cotype)
    ((alg)
     (let* ((name (alg-form-to-name cotype))
	    (alg-name (if (coalg-name? name)
			  (substring name 2 (string-length name))
			  name)))
       (apply make-alg alg-name
	      (map cotype-to-type (alg-form-to-types cotype)))))
    ((arrow)
     (make-arrow (cotype-to-type (arrow-form-to-arg-type cotype))
		 (cotype-to-type (arrow-form-to-val-type cotype))))
    ((star)
     (make-star (cotype-to-type (star-form-to-left-type cotype))
		(cotype-to-type(star-form-to-right-type cotype))))
    (else (myerror "cotype-to-type" "cotype expected" cotype))))

(define (type-to-cotype type)
  (case (tag type)
    ((tvar tconst) type)
    ((alg)
     (let* ((name (alg-form-to-name type))
	    (coalg-name (if (coalg-name? name)
			    name
			    (string-append "co" name))))
       (apply make-alg coalg-name
	      (map type-to-cotype (alg-form-to-types type)))))
    ((arrow)
     (make-arrow (type-to-cotype (arrow-form-to-arg-type type))
		 (type-to-cotype (arrow-form-to-val-type type))))
    ((star)
     (make-star (type-to-cotype (star-form-to-left-type type))
		(type-to-cotype (star-form-to-right-type type))))
    (else (myerror "type-to-cotype" "type expected" type))))

(define (alg-name-to-recursive? alg-name)
  (let* ((typed-constr-names (alg-name-to-typed-constr-names alg-name))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (arg-types (apply union (map arrow-form-to-arg-types constr-types)))
	 (arg-val-types (map arrow-form-to-final-val-type arg-types))
	 (arg-val-algs (list-transform-positive arg-val-types alg-form?))
	 (arg-val-alg-names (map alg-form-to-name arg-val-algs))
	 (simalg-names (alg-name-to-simalg-names alg-name)))
    (pair? (intersection arg-val-alg-names simalg-names))))

;; (alg-name-to-recursive? "yprod")
;; (alg-name-to-recursive? "nat")
;; (alg-name-to-recursive? "list")
;; (alg-name-to-recursive? "tlist")
;; (alg-name-to-recursive? "tree")

;; To add algebras use add-algs.  Example:

;; (add-algs (list "list") 'prefix-typeop
;; 	  '("list" "Nil")
;; 	  '("alpha=>list=>list" "Cons"))

;; How it works: add list temporarily as an algebra name.  Then parse
;; the constructor types.  Create new tvar xi.  Substitute list by xi.
;; Remove the algebra name list.  Create algebra name list.  Form
;; constructor types by substituting (list alpha1) for xi.

(define (add-algs alg-name-or-alg-names .
		  opt-token-type-and-constr-type-strings-with-opt-names)
  (if (null? opt-token-type-and-constr-type-strings-with-opt-names)
      (myerror "add-algs" "constructor type strings with opt names expected"))
  (let*
      ((alg-names
	(cond
	 ((string? alg-name-or-alg-names) (list alg-name-or-alg-names))
	 ((and (list? alg-name-or-alg-names)
	       (pair? alg-name-or-alg-names)
	       (apply and-op (map string? alg-name-or-alg-names)))
	  alg-name-or-alg-names)
	 (else (myerror "add-algs" "list of algebra names expected"
			alg-name-or-alg-names))))
       (alg-names-test
	(if (apply or-op (map (lambda (s) (is-used? s '() 'algebra))
			      alg-names))
	    (apply myerror "add-algs" "new strings expected" alg-names)))
       (opt-token-type
	(if (memq (car opt-token-type-and-constr-type-strings-with-opt-names)
		  (list 'postfix-typeop 'prefix-typeop 'prod-typeop
			'tensor-typeop 'sum-typeop 'alg 'alg-typeop))
	    (car opt-token-type-and-constr-type-strings-with-opt-names)
	    '()))
       (rest (if (null? opt-token-type)
		 opt-token-type-and-constr-type-strings-with-opt-names
		 (cdr opt-token-type-and-constr-type-strings-with-opt-names)))
       (constr-type-strings-with-opt-names
	(map (lambda (x)
	       (if ;constructor name (capitalized) comes first
		(and (pair? x)
		     (string? (car x))
		     (char-upper-case? (car (string->list (car x)))))
					;revert, i.e., take typestring first
		(reverse x)
		x))
	     rest))
       (constr-type-strings-with-opt-names-test
	(if (null? constr-type-strings-with-opt-names)
	    (myerror "add-algs"
		     "constructor type strings with optional names expected")
	    (for-each ;test for constr-type strings with opt names
	     (lambda (x)
	       (if (or (not (list? x))
		       (< 2 (length x))
		       (not (string? (car x)))
		       (and (pair? (cdr x)) (not (string? (cadr x)))))
		   (myerror
		    "add-algs"
		    "list of constr type string and optional name expected" x)))
	     constr-type-strings-with-opt-names)))
       (constr-type-strings (map car constr-type-strings-with-opt-names))
       (opt-names (map cdr constr-type-strings-with-opt-names))
       (alg-tvars (map (lambda (alg-name)
			 (type-string-to-new-tvar
			  (apply string-append constr-type-strings)))
		       alg-names))
       (alg-name-to-alg-tvar-alist (map list alg-names alg-tvars))
       (val-alg-names-with-duplicates
	(map string-to-last-name constr-type-strings))
       (val-alg-names (remove-duplicates val-alg-names-with-duplicates))
       (alg-names-test1
	(if (pair? (set-minus alg-names val-alg-names))
	    (apply myerror "add-algs" "too many alg-names"
		   (set-minus alg-names val-alg-names))))
       (alg-names-test2
	(if (pair? (set-minus val-alg-names alg-names))
	    (apply myerror "add-algs" "too many val-alg-names"
		   (set-minus val-alg-names alg-names))))
					;temporarily add alg-names
					;with token type alg to ALGEBRAS
       (constr-types-with-alg-tvars
	(begin
	  (set! OLD-ALGEBRAS ALGEBRAS)
	  (for-each
	   (lambda (x)
	     (set! ALGEBRAS (cons (list x alg-name-to-alg-tvar-alist 'alg)
				  ALGEBRAS)))
	   alg-names)
					;add them as tokens
	  (for-each (lambda (x) (add-token x 'alg x)) alg-names)
					;parse constr-type-strings
	  (map (lambda (x) (type-gen-substitute
			    (py x)
			    (map list (map make-alg alg-names) alg-tvars)))
	       constr-type-strings)))
       (cleanup	(begin (set! ALGEBRAS OLD-ALGEBRAS)
		       (for-each remove-token alg-names)))
       (param-tvars (set-minus (apply union (map type-to-tvars
						 constr-types-with-alg-tvars))
			       alg-tvars))
       (arity (length param-tvars))
       (token-type
	(if (null? opt-token-type)
	    (if (zero? arity) 'alg 'alg-typeop)
	    (if (= arity (token-type-to-arity opt-token-type))
		opt-token-type
		(apply myerror "add-algs" "for token type" opt-token-type
		       "the expected number of parameter type variables is"
		       (token-type-to-arity opt-token-type)
		       "but the present parameter type variables are"
		       param-tvars))))
					;test that alg-tvars occur only strictly
					;positive in arg-types of constr-types
       (test-for-strict-positivity-of-alg-tvars-in-argtypes
	(let* ((argtypes (apply append (map arrow-form-to-arg-types
					    constr-types-with-alg-tvars)))
	       (arg-tvars (apply union (map type-to-tvars argtypes)))
	       (spos-arg-tvars (apply union (map type-to-spos-tvars
						 argtypes))))
	  (if (pair? (intersection (set-minus arg-tvars spos-arg-tvars)
				   alg-tvars))
	      (apply myerror "add-algs"
		     "strict positivity of alg tvars in argtypes expected"
		     constr-types-with-alg-tvars))))
       (constr-types-with-alg-tvars-and-opt-names
	(map cons constr-types-with-alg-tvars opt-names))
					;create names AlgZero etc if
					;none are given
       (constr-types-with-alg-tvars-and-names
	(do ((l constr-types-with-alg-tvars-and-opt-names (cdr l))
	     (tvar-counter-alist-and-res
	      (list (map (lambda (tvar) (list tvar 0)) alg-tvars) '())
	      (let* ((tvar-counter-alist (car tvar-counter-alist-and-res))
		     (res (cadr tvar-counter-alist-and-res))
		     (constr-type-with-alg-tvar-and-opt-name (car l))
		     (constr-type (car constr-type-with-alg-tvar-and-opt-name))
		     (opt-name (cdr constr-type-with-alg-tvar-and-opt-name))
		     (tvar (arrow-form-to-final-val-type constr-type))
		     (alg-name
		      (cadr (assoc tvar (map list alg-tvars alg-names))))
		     (char-list (string->list alg-name))
		     (capitalized-alg-name
		      (list->string
		       (cons (char-upcase (car char-list)) (cdr char-list))))
		     (i (cadr (assoc tvar tvar-counter-alist)))
		     (name (if (null? opt-name)
			       (string-append capitalized-alg-name
					      (number-to-alphabetic-string i))
			       (car opt-name))))
		(list (cons (list tvar (+ 1 i))
			    (remove (list tvar i) tvar-counter-alist))
		      (cons (list constr-type name) res)))))
	    ((null? l) (reverse (cadr tvar-counter-alist-and-res)))))
       (constr-names (map cadr constr-types-with-alg-tvars-and-names))
       (test-for-undefined-alg-names
	(for-each (lambda (constr-type-with-alg-tvars)
		    (let ((test (set-minus (type-to-alg-names
					    constr-type-with-alg-tvars)
					   (append (map car TYPE-CONSTANTS)
						   (map car ALGEBRAS)
						   alg-names))))
		      (if (pair? test)
			  (apply myerror "add-algs" "undefined alg-names"
				 test))))
		  constr-types-with-alg-tvars))
					;test for unnecessary simultaneous def
       (alg-tvars-with-immed-pd-alg-tvars
	(map
	 (lambda (alg-tvar)
	   (do ((l constr-types-with-alg-tvars (cdr l))
		(res
		 '()
		 (if
		  (equal? alg-tvar (arrow-form-to-final-val-type (car l)))
		  (let* ((type (car l))
			 (argtypes (arrow-form-to-arg-types type))
			 (argvaltypes
			  (map arrow-form-to-final-val-type argtypes))
			 (pd-tvars
			  (intersection (apply union (map type-to-tvars
							  argvaltypes))
					alg-tvars)))
		    (union pd-tvars res))
		  res)))
	       ((null? l) (cons alg-tvar (reverse res)))))
	 alg-tvars))
       (alg-tvars-with-simalg-tvars
	(let ((closure-op
	       (lambda (tvars)
		 (apply
		  union
		  tvars
		  (map (lambda (tvar)
			 (let ((info
				(assoc
				 tvar alg-tvars-with-immed-pd-alg-tvars)))
			   (if info (cdr info) '())))
		       tvars)))))
	  (map (lambda (tvar)
		 (cons tvar (set-closure (list tvar) closure-op)))
	       alg-tvars)))
       (test-for-unnecessary-simultaneous-definition
	(for-each (lambda (x)
		    (let ((alg-tvar (car x))
			  (cl (cdr x)))
		      (if (not (null? (set-minus alg-tvars cl)))
			  (myerror "unnecessary simultaneous definition for"
				   alg-tvar))))
		  alg-tvars-with-simalg-tvars))
       (alg-tvars-algs-tsubst
	(make-substitution alg-tvars (map (lambda (alg-name)
					    (apply make-alg alg-name
						   param-tvars))
					  alg-names)))
       (alg-names-with-typed-constr-names ;((alg1 constr1 constr2 ...) ...)
	(map (lambda (alg-name alg-tvar)
	       (do ((l1 constr-names (cdr l1))
		    (l2 constr-types-with-alg-tvars (cdr l2))
		    (res '()
			 (if (equal? alg-tvar (arrow-form-to-final-val-type
					       (car l2)))
			     (let* ((constr-type-with-alg-tvars (car l2))
				    (constr-type
				     (type-substitute
				      constr-type-with-alg-tvars
				      alg-tvars-algs-tsubst)))
			       (cons (list (car l1) constr-type) res))
			     res)))
		   ((null? l1) (cons alg-name (reverse res)))))
	     alg-names alg-tvars))
       ;; Test for inhabitedness
       ;; (alg-names-with-constr-types-with-names
       ;; 	(map (lambda (alg-name alg-tvar)
       ;; 	       (do ((l constr-types-with-alg-tvars (cdr l))
       ;; 		    (res '()
       ;; 			 (if (equal? alg-tvar (arrow-form-to-final-val-type
       ;; 					       (car l)))
       ;; 			     (let* ((constr-type-with-alg-tvars (car l))
       ;; 				    (constr-type-with-names
       ;; 				     (type-gen-substitute
       ;; 				      constr-type-with-alg-tvars
       ;; 				      (map list alg-tvars alg-names))))
       ;; 			       (cons constr-type-with-names res))
       ;; 			     res)))
       ;; 		   ((null? l) (cons alg-name (reverse res)))))
       ;; 	     alg-names alg-tvars))
       ;; (test-for-inhabitedness
       ;; 	(for-each
       ;; 	 (lambda (name)
       ;; 	   (let* ((info (assoc name alg-names-with-constr-types-with-names))
       ;; 		  (constr-types-with-names
       ;; 		   (if info (cdr info)
       ;; 		       (myerror "add-algs" "simalg-name expected" name)))
       ;; 		  (rest-names (member name alg-names))
       ;; 		  (inhabcrits
       ;; 		   (constr-types-with-names-and-rest-names-to-inhabcrits
       ;; 		    constr-types-with-names rest-names)))
       ;; 	     (if (null? inhabcrits)
       ;; 		 (myerror "add-algs"
       ;; 			  "nullary initial constructor type expected for"
       ;; 			  name))))
       ;; 	 alg-names))
       )
					;update ALGEBRAS, extend CONSTRUCTORS
    (for-each ;of alg-names-with-typed-constr-names
     (lambda (x)
       (let ((alg-name (car x))
	     (typed-constr-names (cdr x)))
	 (for-each ;of typed-constr-names
	  (lambda (y)
	    (let* ((name (typed-constr-name-to-name y))
		   (type (typed-constr-name-to-type y))
		   (const-token-type
		    (if (null? (cddr y))
			(if (null? param-tvars) 'const 'constscheme)
			(caddr y)))
		   (argtypes (arrow-form-to-arg-types type))
		   (arity (length argtypes))
		   (valtype (arrow-form-to-final-val-type type))
		   (delayed-constr
		    (eval-once (lambda () (constr-name-to-constr name))))
		   (obj (nbe-make-object
			 type
			 (if
			  (zero? arity)
			  (nbe-make-constr-value name '() delayed-constr)
			  (nbe-curry
			   (lambda objs ;as many as argtypes
			     (nbe-make-object valtype
					      (nbe-make-constr-value
					       name objs delayed-constr)))
			   type
			   arity))))
		   (constr (make-const obj name 'constr type
				       empty-subst 1 const-token-type)))
	      (set! CONSTRUCTORS
		    (cons (list name (list (list empty-subst constr)))
			  CONSTRUCTORS))
	      (add-token name
			 const-token-type
			 (if (null? param-tvars)
			     (const-to-token-value constr)
			     constr))))
	  typed-constr-names)
	 (if (not (member alg-name (list "unit" "boole" "yprod" "ysum"
					 "uysum" "ysumu")))
	     (comment "ok, algebra " alg-name " added"))
	 (set! ALGEBRAS
	       (cons (cons alg-name
			   (cons alg-names
				 (cons token-type typed-constr-names)))
		     ALGEBRAS))
	 (add-token alg-name
		    token-type
		    (alg-name-to-token-value alg-name))))
     alg-names-with-typed-constr-names)))

(define (alg-inhabited? alg-name)
  (let* ((typed-constr-names (alg-name-to-typed-constr-names alg-name))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (alg-names (alg-name-to-simalg-names alg-name))
	 (tvars (alg-name-to-tvars alg-name))
	 (algs (map (lambda (name) (apply make-alg name tvars)) alg-names))
	 (alg-tvars (map (lambda (x) (new-tvar)) alg-names))
	 (constr-types-with-alg-tvars
	  (map (lambda (type) (type-gen-substitute
			       type (map list algs alg-tvars)))
	       constr-types))
	 (alg-names-with-constr-types-with-names
	  (map (lambda (alg-name alg-tvar)
		 (do ((l constr-types-with-alg-tvars (cdr l))
		      (res '()
			   (if (equal? alg-tvar (arrow-form-to-final-val-type
						 (car l)))
			       (let* ((constr-type-with-alg-tvars (car l))
				      (constr-type-with-names
				       (type-gen-substitute
					constr-type-with-alg-tvars
					(map list alg-tvars alg-names))))
				 (cons constr-type-with-names res))
			       res)))
		     ((null? l) (cons alg-name (reverse res)))))
	       alg-names alg-tvars))
	 (info (assoc alg-name alg-names-with-constr-types-with-names))
	 (constr-types-with-names
	  (if info (cdr info)
	      (myerror "add-algs" "simalg-name expected" alg-name)))
	 (rest-names (member alg-name alg-names))
	 (inhabcrits (constr-types-with-names-and-rest-names-to-inhabcrits
		      constr-types-with-names rest-names)))
    (pair? inhabcrits)))

;; Kept for backwards compatibility

(define add-alg add-algs)
(define add-param-alg add-algs)
(define add-param-algs add-algs)

;; A display function for algebras with their constructors:

(define (display-alg . x)
  (if
   COMMENT-FLAG
   (let ((reduced-algs (if (null? x)
			   ALGEBRAS
			   (do ((l ALGEBRAS (cdr l))
				(res '() (if (member (caar l) x)
					     (cons (car l) res)
					     res)))
			       ((null? l) res)))))
     (for-each
      (lambda (alg)
	(let* ((alg-name (car alg))
	       (typed-constr-names
		(alg-name-to-typed-constr-names alg-name)))
	  (display alg-name) (newline)
	  (for-each (lambda (tcn)
		      (let ((name (typed-constr-name-to-name tcn))
			    (type (typed-constr-name-to-type tcn))
			    (optional-token-type
			     (typed-constr-name-to-optional-token-type tcn)))
			(display tab)
			(display name) (display ":")
			(display tab)
			(display (type-to-string type))
			(if (pair? optional-token-type)
			    (begin
			      (display tab)
			      (display (car optional-token-type))))
			(newline)))
		    typed-constr-names)))
      reduced-algs))))

;; For backwards compatibility we keep

(define display-constructors display-alg)

(define (remove-alg-name . strings)
  (define (ran1 alg-name)
    (if
     (assoc alg-name ALGEBRAS)
     (let* ((simalg-names (alg-name-to-simalg-names alg-name))
	    (affected-constr-names
	     (list-transform-positive (map car CONSTRUCTORS)
	       (lambda (x)
		 (pair? (intersection simalg-names
				      (type-to-alg-names
				       (const-to-type
					(constr-name-to-constr x))))))))
	    (affected-pconst-names
	     (list-transform-positive (map car PROGRAM-CONSTANTS)
	       (lambda (x)
		 (pair? (intersection simalg-names
				      (type-to-alg-names
				       (const-to-type
					(pconst-name-to-pconst x)))))))))
       (set! ALGEBRAS
	     (list-transform-positive ALGEBRAS
	       (lambda (x) (not (member (car x) simalg-names)))))
       (for-each (lambda (x)
		   (remove-token x)
		   (comment "ok, algebra " x " removed"))
		 simalg-names)
       (set! CONSTRUCTORS
	     (list-transform-positive CONSTRUCTORS
	       (lambda (x) (not (member (car x) affected-constr-names)))))
       (for-each (lambda (x)
		   (remove-token x)
		   (comment "ok, constructor " x " removed"))
		 affected-constr-names)
       (apply remove-program-constant affected-pconst-names))
     (multiline-comment  "remove-alg-name" "algebra name expected" alg-name)))
  (let* ((list-of-simalgs (map alg-name-to-simalg-names strings))
	 (reduced-list-of-simalgs (remove-duplicates list-of-simalgs))
	 (reduced-strings (map car reduced-list-of-simalgs)))
    (for-each ran1 reduced-strings)))

(define ran remove-alg-name)

(define (alg-and-excluded-simalg-names-to-inhab-or-f alg . excl-names)
  (let* ((alg-name (alg-form-to-name alg))
	 (types (alg-form-to-types alg))
	 (tvars (alg-name-to-tvars alg-name))
	 (tsubst (make-substitution tvars types))
	 (typed-constr-names (alg-name-to-typed-constr-names alg-name))
	 (constr-names (map typed-constr-name-to-name typed-constr-names))
	 (constrs (map constr-name-to-constr constr-names))
	 (cycle-free-constrs ;for simplicity no immediate cycles
	  (list-transform-positive constrs
	    (lambda (constr)
	      (let* ((type (const-to-type constr))
		     (arg-types (arrow-form-to-arg-types type))
		     (arg-val-types
		      (map arrow-form-to-final-val-type arg-types))
		     (arg-val-algs
		      (list-transform-positive arg-val-types alg-form?)))
		(not (member alg-name (map alg-form-to-name arg-val-algs)))))))
	 (inst-constr-terms (map (lambda (constr)
				   (make-term-in-const-form
				    (const-substitute constr tsubst #t)))
				 cycle-free-constrs)))
    (do ((l inst-constr-terms (cdr l))
	 (res
	  #f
	  (let* ((inst-constr-term (car l))
		 (type (term-to-type inst-constr-term))
		 (arg-types (arrow-form-to-arg-types type))
		 ;; (arg-val-types (map arrow-form-to-final-val-type arg-types))
		 (inhab-or-fs ;rec call for each arg-type w.r.t ext excl-names
		  (map (lambda (x) ;x an arg-type
			 (let* ((arg-val-type (arrow-form-to-final-val-type x))
				(arg-arg-types (arrow-form-to-arg-types x))
				(vars (map type-to-new-var arg-arg-types)))
			   (cond
			    ((tvar-form? arg-val-type)
			     (let* ((inhab-pconst
				     (pconst-name-to-pconst "Inhab"))
				    (tvars (const-to-tvars inhab-pconst))
				    (tsubst (make-substitution
					     tvars (list arg-val-type))))
			       (apply
				mk-term-in-abst-form
				(append vars
					(list (make-term-in-const-form
					       (const-substitute
						inhab-pconst tsubst #f)))))))
			    ((alg-form? arg-val-type) ;rec. call
			     (apply
			      mk-term-in-abst-form
			      (append
			       vars
			       (list
				(apply
				 alg-and-excluded-simalg-names-to-inhab-or-f
				 arg-val-type
				 (alg-form-to-name arg-val-type)
				 excl-names)))))
			    (else (myerror
				   "alg-and-excluded-simalg-names-to-inhab-or-f"
				   "tvar or alg-from expected" arg-val-type)))))
		       arg-types)))
	    (if (member #f inhab-or-fs) #f
		(apply mk-term-in-app-form inst-constr-term inhab-or-fs)))))
	((or res (null? l)) res))))

;; In alg-to-canonical-inhabitant it is assumed that alg has level
;; zero, i.e., that all its paramter types have level zero as well.

(define (alg-to-canonical-inhabitant alg)
  (let ((inhab-or-f (alg-and-excluded-simalg-names-to-inhab-or-f alg)))
    (if inhab-or-f
	inhab-or-f
	(make-term-in-const-form
	 (let* ((inhab-pconst (pconst-name-to-pconst "Inhab"))
		(tvars (const-to-tvars inhab-pconst))
		(tsubst (make-substitution tvars (list alg))))
	   (const-substitute inhab-pconst tsubst #f))))))

(define (type-to-canonical-inhabitant type)
  (case (tag type)
    ((tvar tconst) (make-term-in-const-form
		    (let* ((inhab-pconst (pconst-name-to-pconst "Inhab"))
			   (tvars (const-to-tvars inhab-pconst))
			   (tsubst (make-substitution tvars (list type))))
		      (const-substitute inhab-pconst tsubst #f))))
    ((alg) (alg-to-canonical-inhabitant type))
    ((arrow) (let* ((arg-type (arrow-form-to-arg-type type))
		    (val-type (arrow-form-to-val-type type))
		    (var (type-to-new-var arg-type)))
	       (make-term-in-abst-form
		var (type-to-canonical-inhabitant val-type))))
    ((star) (let ((left-type (star-form-to-left-type type))
		  (right-type (star-form-to-right-type type)))
	      (make-term-in-pair-form
	       (type-to-canonical-inhabitant left-type)
	       (type-to-canonical-inhabitant right-type))))
    (else (myerror "type-to-canonical-inhabitant" "type expected" type))))

;; Code discarded 2018-06-10
;; (define (cycle-free-constr? inst-constr . opt-excluded-algs)
;;   (let* ((type (term-to-type inst-constr))
;; 	 (alg (arrow-form-to-final-val-type type))
;; 	 (arg-types (arrow-form-to-arg-types type))
;; 	 (arg-val-types (map arrow-form-to-final-val-type arg-types)))
;;     (null? (intersection arg-val-types (cons alg opt-excluded-algs)))))

;; (define (alg-to-canonical-inhabitant alg . opt-excluded-algs)
;;   (if (member alg opt-excluded-algs) #f
;;       (let* ((alg-name (alg-form-to-name alg))
;; 	     (tvars (alg-name-to-tvars alg-name))
;; 	     (types (alg-form-to-types alg))
;; 	     (tsubst (make-substitution tvars types))
;; 	     (typed-constr-names (alg-name-to-typed-constr-names alg-name))
;; 	     (constr-names (map typed-constr-name-to-name typed-constr-names))
;; 	     (constrs (map constr-name-to-constr constr-names))
;; 	     (inst-constrs (map (lambda (constr)
;; 				  (make-term-in-const-form
;; 				   (const-substitute constr tsubst #t)))
;; 				constrs))
;; 	     (cycle-free-inst-constrs
;; 	      (list-transform-positive inst-constrs cycle-free-constr?))
;; 	     (canonical-insts
;; 	      (map inst-constr-to-canonical-inst-or-f cycle-free-inst-constrs)))
;; 	(list-to-first canonical-insts))))

;; ;; Assume that inst-constr is cycle-free w.r.t. the final alg and the
;; ;; opt-excluded-algs.

;; (define (inst-constr-to-canonical-inst-or-f inst-constr . opt-excluded-algs)
;;   (let* ((type (term-to-type inst-constr))
;; 	 (alg (arrow-form-to-final-val-type type))
;; 	 (arg-types (arrow-form-to-arg-types type))
;; 	 (args
;; 	  (map (lambda (arg-type)
;; 		 (let ((arg-val-type (arrow-form-to-final-val-type arg-type))
;; 		       (arg-arg-types (arrow-form-to-arg-types arg-type)))
;; 		   (cond
;; 		    ((member arg-val-type opt-excluded-algs) #f)
;; 		    ((or (tvar? arg-val-type) (tconst? arg-val-type))
;; 		     (apply
;; 		      mk-term-in-abst-form
;; 		      (append
;; 		       (map type-to-new-var arg-arg-types)
;; 		       (list
;; 			(make-term-in-const-form
;; 			 (let* ((inhab-pconst (pconst-name-to-pconst "Inhab"))
;; 				(tvars (const-to-tvars inhab-pconst))
;; 				(tsubst (make-substitution
;; 					 tvars (list arg-val-type))))
;; 			   (const-substitute inhab-pconst tsubst #f)))))))
;; 		    ((alg-form? arg-val-type) ;recursive call
;; 		     (let ((alg-inhab
;; 			    (apply alg-to-canonical-inhabitant
;; 				   arg-val-type alg opt-excluded-algs)))
;; 		       (type-and-val-type-inhab-to-inhab
;; 			arg-type alg-inhab)))
;; 		    (else (myerror "inst-constr-to-canonical-inst-or-f"
;; 				   "alg or tvar expected" arg-val-type)))))
;; 	       arg-types)))
;;     (if (member #f args) #f
;; 	(apply mk-term-in-app-form inst-constr args))))

;; (define (type-and-val-type-inhab-to-inhab type val-type-inhab)
;;   (if (arrow-form? type)
;;       (let* ((arg (arrow-form-to-arg-type type))
;; 	     (val (arrow-form-to-val-type type))
;; 	     (prev (type-and-val-type-inhab-to-inhab val val-type-inhab))
;; 	     (var (type-to-new-var arg)))
;; 	(make-term-in-abst-form var prev))
;;       val-type-inhab))

;; (define (type-to-canonical-inhabitant type)
;;   (case (tag type)
;;     ((tvar tconst) (make-term-in-const-form
;; 		    (let* ((inhab-pconst (pconst-name-to-pconst "Inhab"))
;; 			   (tvars (const-to-tvars inhab-pconst))
;; 			   (tsubst (make-substitution tvars (list type))))
;; 		      (const-substitute inhab-pconst tsubst #f))))
;;     ((alg) (alg-to-canonical-inhabitant type))
;;     ((arrow) (let* ((arg-type (arrow-form-to-arg-type type))
;; 		    (val-type (arrow-form-to-val-type type))
;; 		    (var (type-to-new-var arg-type)))
;; 	       (make-term-in-abst-form
;; 		var (type-to-canonical-inhabitant val-type))))
;;     ((star) (let ((left-type (star-form-to-left-type type))
;; 		  (right-type (star-form-to-right-type type)))
;; 	      (make-term-in-pair-form
;; 	       (type-to-canonical-inhabitant left-type)
;; 	       (type-to-canonical-inhabitant right-type))))
;;     (else (myerror "type-to-canonical-inhabitant" "type expected" type))))

;; Code discarded 2018-05-30
;; ;; type-to-canonical-inhabitant can be defined directly using the required
;; ;; order of the constructor types.

;; (define (type-to-canonical-inhabitant type)
;;   (case (tag type)
;;     ((tvar tconst)
;;      (make-term-in-const-form
;;       (let* ((inhab-pconst (pconst-name-to-pconst "Inhab"))
;; 	     (tvars (const-to-tvars inhab-pconst))
;; 	     (tsubst (make-substitution tvars (list type))))
;; 	(const-substitute inhab-pconst tsubst #f))))
;;     ((alg)
;;      (if
;;       (not (alg-inhabited? (alg-form-to-name type)))
;;       (make-term-in-const-form
;;        (let* ((inhab-pconst (pconst-name-to-pconst "Inhab"))
;; 	      (tvars (const-to-tvars inhab-pconst))
;; 	      (tsubst (make-substitution tvars (list type))))
;; 	 (const-substitute inhab-pconst tsubst #f)))
;;       (let* ((alg-name (alg-form-to-name type))
;; 	     (types (alg-form-to-types type))
;; 	     (typed-constr-names (alg-name-to-typed-constr-names alg-name))
;; 	     (constr-names (map typed-constr-name-to-name typed-constr-names))
;; 	     (constr-types (map typed-constr-name-to-type typed-constr-names))
;; 	     (init-constr-name-and-constr-type
;; 	      (do ((l1 constr-names (cdr l1))
;; 		   (l2 constr-types (cdr l2))
;; 		   (res #f (if res res
;; 			       (let* ((constr-name (car l1))
;; 				      (constr-type (car l2)))
;; 				 (if (string=? (alg-form-to-name
;; 						(arrow-form-to-final-val-type
;; 						 constr-type))
;; 					       alg-name)
;; 				     (list constr-name constr-type)
;; 				     #f)))))
;; 		  ((null? l1) (if res res #f))))
;; 	     (constr-name (car init-constr-name-and-constr-type))
;; 	     (constr-type (cadr init-constr-name-and-constr-type))
;; 	     (arg-types (arrow-form-to-arg-types constr-type))
;; 	     (tvars (alg-name-to-tvars alg-name))
;; 	     (tsubst (make-substitution tvars types))
;; 	     (substituted-arg-types
;; 	      (map (lambda (arg-type) (type-substitute arg-type tsubst))
;; 		   arg-types))
;; 	     (ih-inhabs (map type-to-canonical-inhabitant
;; 			     substituted-arg-types))
;; 	     (constr (const-substitute (constr-name-to-constr constr-name)
;; 				       tsubst #t)))
;; 	(apply mk-term-in-app-form
;; 	       (make-term-in-const-form constr)
;; 	       ih-inhabs))))
;;     ((arrow)
;;      (let* ((arg-type (arrow-form-to-arg-type type))
;; 	    (val-type (arrow-form-to-val-type type))
;; 	    (var (type-to-new-var arg-type)))
;;        (make-term-in-abst-form
;; 	var (type-to-canonical-inhabitant val-type))))
;;     ((star)
;;      (let ((left-type (star-form-to-left-type type))
;; 	   (right-type (star-form-to-right-type type)))
;;        (make-term-in-pair-form
;; 	(type-to-canonical-inhabitant left-type)
;; 	(type-to-canonical-inhabitant right-type))))
;;     (else (myerror "type-to-canonical-inhabitant" "type expected" type))))

;; For Huets unification algorithm we need

(define (type-to-canonical-term type groundtype-var-alist)
  (case (tag type)
    ((tvar tconst alg)
     (let ((info (assoc type groundtype-var-alist)))
       (if (not info)
	   (myerror "type-to-canonical-term" "no variable assigned to"
		    type))
       (make-term-in-var-form (cadr info))))
    ((arrow)
     (let* ((arg-type (arrow-form-to-arg-type type))
	    (val-type (arrow-form-to-val-type type))
	    (var (type-to-new-var arg-type)))
       (make-term-in-abst-form
	var (type-to-canonical-term val-type groundtype-var-alist))))
    ((star)
     (let ((left-type (star-form-to-left-type type))
	   (right-type (star-form-to-right-type type)))
       (make-term-in-pair-form
	(type-to-canonical-term left-type groundtype-var-alist)
	(type-to-canonical-term right-type groundtype-var-alist))))
    (else
     (myerror "type-to-canonical-term" "type expected" type))))

(define (type-to-final-groundtypes type)
  (case (tag type)
    ((tvar tconst alg) (list type))
    ((arrow) (type-to-final-groundtypes (arrow-form-to-val-type type)))
    ((star)
     (union (type-to-final-groundtypes (star-form-to-left-type type))
	    (type-to-final-groundtypes (star-form-to-right-type type))))
    (else (myerror "type-to-final-groundtypes" "type expected" type))))

;; We need a subtype relation generated from pos < nat < int < rat <
;; rea < cpx and (str alpha)<(list alpha)

;; View pos, nat, int, rat, rea and cpx as algebras, with constructors
;; pos: One SZero SOne
;; nat: Zero Succ
;; int: IntPos IntZero IntNeg
;; rat: RatConstr (written # infix) and destructors RatN RatD
;; rea: RealConstr and Destructors RealSeq RealMod
;; cpx: CpxConstr (written ## infix) and destructors RealPart ImagPart

;; View str, list as algebras with constructors
;; str: SCons
;; list: Nil Cons

;; We use a global variable ALGEBRA-EDGE-TO-EMBED-TERM-ALIST
;; initially set to '().

(define ALGEBRA-EDGE-TO-EMBED-TERM-ALIST '())

(define (add-item-to-algebra-edge-to-embed-term-alist
         alg1-name alg2-name embed-term)
  (set! ALGEBRA-EDGE-TO-EMBED-TERM-ALIST
        (cons (list
	       (list (apply make-alg alg1-name (alg-name-to-tvars alg1-name))
		     (apply make-alg alg2-name (alg-name-to-tvars alg2-name)))
	       embed-term)
              ALGEBRA-EDGE-TO-EMBED-TERM-ALIST)))

(define (add-item-to-algebra-edge-to-embed-term-alist
         alg1-name alg2-name embed-term)
  (set! ALGEBRA-EDGE-TO-EMBED-TERM-ALIST
        (cons (list
	       (list (apply make-alg alg1-name (alg-name-to-tvars alg1-name))
		     (apply make-alg alg2-name (alg-name-to-tvars alg2-name)))
	       embed-term)
              ALGEBRA-EDGE-TO-EMBED-TERM-ALIST)))

;; When later we have proved totality of e.g. PosToNat and NatToInt we
;; need to replace their item accordingly.

(define (replace-item-in-algebra-edge-to-embed-term-alist
         alg1-name alg2-name new-embed-term)
  (let* ((alg1 (apply make-alg alg1-name (alg-name-to-tvars alg1-name)))
	 (alg2 (apply make-alg alg2-name (alg-name-to-tvars alg2-name)))
	 (new-alist (map (lambda (item)
			   (if (equal? (car item) (list alg1 alg2))
			       (list (car item) new-embed-term)
			       item))
			 ALGEBRA-EDGE-TO-EMBED-TERM-ALIST)))
    (set! ALGEBRA-EDGE-TO-EMBED-TERM-ALIST new-alist)))

(define (alg-le? alg1 alg2)
  (let ((name1 (alg-form-to-name alg1))
	(name2 (alg-form-to-name alg2)))
    (if
     (string=? name1 name2)
     (let ((types1 (alg-form-to-types alg1))
	   (types2 (alg-form-to-types alg2)))
       (apply and-op (map type-le? types1 types2)))
     (do ((l ALGEBRA-EDGE-TO-EMBED-TERM-ALIST (cdr l))
	  (res #f (let* ((item (car l))
			 (edge (car item))
			 (lhs (car edge))
			 (rhs (cadr edge))
			 (embed-term (cadr item))
			 (tsubst2 (type-match rhs alg2)))
		    (and tsubst2
			 (alg-le? alg1 (type-substitute lhs tsubst2))))))
	 ((or res (null? l)) res)))))

;; (alg-le? (py "pos") (py "int"))
;; (alg-le? (py "pos") (py "rat"))
;; (alg-le? (py "list pos") (py "list int"))
;; (alg-le? (py "list pos") (py "list rat"))
;; (alg-le? (py "str pos") (py "str int"))
;; (alg-le? (py "str pos") (py "list pos"))
;; (alg-le? (py "str pos") (py "list int"))
;; (alg-le? (py "str pos") (py "list rat"))
;; (alg-le? (py "list pos") (py "str pos"))

(define (type-le? type1 type2)
  (or (equal? type1 type2)
      (and (alg-form? type1) (alg-form? type2)
	   (alg-le? type1 type2))
      (and (arrow-form? type1) (arrow-form? type2)
	   (type-le? (arrow-form-to-arg-type type2)
		     (arrow-form-to-arg-type type1))
	   (type-le? (arrow-form-to-val-type type1)
		     (arrow-form-to-val-type type2)))
      (and (star-form? type1) (star-form? type2)
	   (type-le? (star-form-to-left-type type1)
		     (star-form-to-left-type type2))
	   (type-le? (star-form-to-right-type type1)
		     (star-form-to-right-type type2)))
      (and (star-form? type1) (yprod-form? type2)
	   (type-le? (star-form-to-left-type type1)
		     (yprod-form-to-left-type type2))
	   (type-le? (star-form-to-right-type type1)
		     (yprod-form-to-right-type type2)))
      (and (yprod-form? type1) (star-form? type2)
	   (type-le? (yprod-form-to-left-type type1)
		     (star-form-to-left-type type2))
	   (type-le? (yprod-form-to-right-type type1)
		     (star-form-to-right-type type2)))))

;; (type-le? (py "pos") (py "int"))
;; (type-le? (py "pos") (py "rat"))
;; (type-le? (py "list pos") (py "list int"))
;; (type-le? (py "list pos") (py "list rat"))
;; (type-le? (py "str pos") (py "str int"))
;; (type-le? (py "str pos") (py "list pos"))
;; (type-le? (py "str pos") (py "list int"))
;; (type-le? (py "str pos") (py "list rat"))
;; (type-le? (py "list pos") (py "str pos"))

;; (type-le? (py "nat") (py "int")) ;#t
;; (alg-le? (py "list pos") (py "list int"))

;; (set! ALGEBRA-EDGE-TO-EMBED-TERM-ALIST '())

;; For compatibility we (temporarily) define
(define type-leq? type-le?)

;; The original of a term under possibly repeated embeddings stored in
;; ALGEBRA-EDGE-TO-EMBED-TERM-ALIST

(define (term-to-original term)
  (do ((l ALGEBRA-EDGE-TO-EMBED-TERM-ALIST (cdr l))
       (res #f (let* ((item (car l))
		      (edge (car item))
		      (lhs (car edge))
		      (rhs (cadr edge))
		      (tsubst (type-match rhs (term-to-type term))))
		 (if tsubst
		     (let* ((embed-term (cadr item))
			    (var (term-in-abst-form-to-var embed-term))
			    (kernel (term-in-abst-form-to-kernel embed-term))
			    (match-res (match kernel term)))
		       (if match-res
			   (term-to-original
			    (let ((info (assoc var match-res)))
			      (if info
				  (cadr info)
				  (make-term-in-var-form var))))
			   #f))
		     #f))))
      ((or res (null? l)) (if res res term))))

;; (pp (term-to-original (pt "(IntPos p):")))
;; p:

;; The following returns #f in case alg1 not <= alg2

(define (algebras-to-embedding alg1 alg2) ;alg1=str pos, alg2=list rat
  (let ((name1 (alg-form-to-name alg1))
	(name2 (alg-form-to-name alg2)))
    (if
     (string=? name1 name2)
     (let ((types1 (alg-form-to-types alg1))
	   (types2 (alg-form-to-types alg2)))
       (if
	(equal? types1 types2)
	(lambda (term) term)
	(let ((prevs ;of types (pos=>rat)
	       (map types-to-embedding types1 types2)))
	  (and (apply and-op prevs)
	       (let* ((tvars (alg-name-to-tvars name1))
		      (map-const ;str pos=>(pos=>rat)=>str rat
		       (make-map-const
			(apply make-alg name1 tvars) tvars types1 types2))
		      (var ;str pos
		       (make-var alg1 -1 t-deg-one (default-var-name alg1)))
		      (xs (map (lambda (type)
				 (make-var
				  type -1 t-deg-one (default-var-name type)))
			       types1))
		      (prevs-terms
		       (map (lambda (prev x)
			      (make-term-in-abst-form
			       x (prev (make-term-in-var-form x))))
			    prevs xs)))
		 (lambda (term)
		   (apply mk-term-in-app-form
			  (make-term-in-const-form map-const)
			  term
			  prevs-terms)))))))
     (do ((l ALGEBRA-EDGE-TO-EMBED-TERM-ALIST (cdr l))
	  (res #f (let* ((item (car l))
			 (edge (car item)) ;((str alpha) (list alpha))
			 (lhs (car edge)) ;str alpha
			 (rhs (cadr edge)) ;list alpha
			 (embed-term (cadr item)) ;str alpha=>list alpha
			 (tsubst2 (type-match rhs alg2))) ;alpha=>rat
		    (and
		     tsubst2
		     (let* ((subst-embed-term ;str rat=>list rat
			     (term-substitute embed-term tsubst2))
			    (subst-embed-var ;str rat
			     (term-in-abst-form-to-var subst-embed-term))
			    (subst-embed-kernel ;list rat
			     (term-in-abst-form-to-kernel subst-embed-term))
			    (prev ;str pos=>str rat
			     (algebras-to-embedding ;recursive call
			      alg1 (type-substitute lhs tsubst2))))
		       (and prev
			    (lambda (term)
			      (term-subst subst-embed-kernel
					  subst-embed-var
					  (prev term)))))))))
	 ((or res (null? l)) res)))))

(define (types-to-embedding type1 type2)
  (if
   (equal? type1 type2)
   (lambda (term) term)
   (cond
    ((and (alg-form? type1) (alg-form? type2))
     (let ((types1 (alg-form-to-types type1))
	   (types2 (alg-form-to-types type2)))
       (if (not (= (length types1) (length types2)))
	   (apply myerror
		  "types-to-embedding"
		  "types of equal lengths expected"
		  (append types1 (list "and") types2)))
       (cond
	((null? types1)	(algebras-to-embedding type1 type2))
	((and (yprod-form? type1) (yprod-form? type2))
	 (let ((prev-left
		(types-to-embedding (yprod-form-to-left-type type1)
				    (yprod-form-to-left-type type2)))
	       (prev-right
		(types-to-embedding (yprod-form-to-right-type type1)
				    (yprod-form-to-right-type type2))))
	   (lambda (x)
	     (make-term-in-cons-form
	      (prev-left (if (term-in-cons-form? x)
			     (term-in-cons-form-to-left x)
			     (make-term-in-car-form x)))
	      (prev-right (if (term-in-cons-form? x)
			      (term-in-cons-form-to-right x)
			      (make-term-in-cdr-form x)))))))
	(else
	 (let ((name1 (alg-form-to-name type1))
	       (name2 (alg-form-to-name type2)))
	   (if (not (string=? name1 name2))
	       (myerror "types-to-embedding" "equal alg names expected"
			type1 type2))
	   (let* ((tvars (alg-name-to-tvars name1))
		  (tvar-to-embedding-alist
		   (map (lambda (tvar type1 type2)
			  (list tvar (types-to-embedding type1 type2)))
			tvars types1 types2))
		  (tsubst1 (make-substitution tvars types1))
		  (tsubst2 (make-substitution tvars types2))
		  (rec-const (type-info-to-rec-const (make-arrow type1 type2)))
		  (uninst-type (const-to-uninst-type rec-const))
		  (arg-types (arrow-form-to-arg-types uninst-type))
		  (step-types (cdr arg-types))
		  (alg-type (car arg-types))
		  (step-arg-type-lists (map arrow-form-to-arg-types step-types))
		  (step-alg-arg-type-lists ;((ss1->mu1 .. ssn->mun) ..)
		   (map (lambda (l)
			  (list-transform-positive l
			    (lambda (y)
			      (let ((val-type (arrow-form-to-final-val-type y)))
				(and (alg-form? y)
				     (string=? (alg-form-to-name y) name1))))))
			step-arg-type-lists))
		  (step-alg-arg-lengths (map length step-alg-arg-type-lists))
		  (step-param-arg-tvar-lists
		   (map (lambda (l n) (list-head l (- (length l) (* 2 n))))
			step-arg-type-lists step-alg-arg-lengths))
		  (subst-step-alg-arg-type-lists
		   (map (lambda (types)
			  (map (lambda (type)
				 (type-substitute type tsubst1)) types))
			step-alg-arg-type-lists))
		  (subst-step-param-arg-type-lists
		   (map (lambda (types)
			  (map (lambda (type)
				 (type-substitute type tsubst1)) types))
			step-param-arg-tvar-lists))
		  (subst-step-alg-arg-var-lists
		   (map (lambda (types) (map type-to-new-var types))
			subst-step-alg-arg-type-lists))
		  (subst-step-param-arg-var-lists
		   (map (lambda (types) (map type-to-new-var types))
			subst-step-param-arg-type-lists))
		  (embedded-subst-step-param-arg-varterm-lists
		   (map
		    (lambda (tvars ps)
		      (map (lambda (tvar p)
			     (let* ((info (assoc tvar tvar-to-embedding-alist))
				    (f (if info (cadr info)
					   (myerror
					    "types-to-embedding" "unknown tvar"
					    tvar))))
			       (f (make-term-in-var-form p))))
			   tvars ps))
		    step-param-arg-tvar-lists
		    subst-step-param-arg-var-lists))
		  (typed-constr-names (alg-name-to-typed-constr-names name1))
		  (constr-names (map typed-constr-name-to-name
				     typed-constr-names))
		  (constrs (map constr-name-to-constr constr-names))
		  (subst-constrs
		   (map (lambda (c) (const-substitute c tsubst2 #t))
			constrs))
		  (step-terms
		   (map (lambda (ps rs c ts)
			  (apply
			   mk-term-in-abst-form
			   (append
			    ps rs (list (apply
					 mk-term-in-app-form
					 (make-term-in-const-form c)
					 ts)))))
			subst-step-param-arg-var-lists
			subst-step-alg-arg-var-lists
			subst-constrs
			embedded-subst-step-param-arg-varterm-lists)))
	     (lambda (term)
	       (nbe-normalize-term
		(apply
		 mk-term-in-app-form
		 (make-term-in-const-form rec-const) term step-terms)))))))))
    ((and (arrow-form? type1) (arrow-form? type2))
     (lambda (r)
       (let* ((argtype1 (arrow-form-to-arg-type type1))
	      (valtype1 (arrow-form-to-val-type type1))
	      (argtype2 (arrow-form-to-arg-type type2))
	      (valtype2 (arrow-form-to-val-type type2))
	      (var (type-to-new-var argtype2))
	      (varterm (make-term-in-var-form var))
	      (incr-varterm ((types-to-embedding argtype2 argtype1) varterm))
	      (term (if (term-in-abst-form? r)
			(term-subst (term-in-abst-form-to-kernel r)
				    (term-in-abst-form-to-var r)
				    incr-varterm)
			(make-term-in-app-form r incr-varterm)))
	      (incr-term ((types-to-embedding valtype1 valtype2) term)))
	 (make-term-in-abst-form var incr-term))))
    ((and (star-form? type1) (star-form? type2))
     (let ((prev-left (types-to-embedding (star-form-to-left-type type1)
					  (star-form-to-left-type type2)))
	   (prev-right (types-to-embedding (star-form-to-right-type type1)
					   (star-form-to-right-type type2))))
       (lambda (x)
	 (make-term-in-pair-form
	  (prev-left (if (term-in-pair-form? x)
			 (term-in-pair-form-to-left x)
			 (make-term-in-lcomp-form x)))
	  (prev-right (if (term-in-pair-form? x)
			  (term-in-pair-form-to-right x)
			  (make-term-in-rcomp-form x)))))))
    ((and (star-form? type1) (yprod-form? type2))
     (let ((prev-left (types-to-embedding (star-form-to-left-type type1)
					  (yprod-form-to-left-type type2)))
	   (prev-right (types-to-embedding (star-form-to-right-type type1)
					   (yprod-form-to-right-type type2))))
       (lambda (x) ;t@s -> (emb t)pair(emb s)
	 (make-term-in-cons-form
	  (prev-left (if (term-in-pair-form? x)
			 (term-in-pair-form-to-left x)
			 (make-term-in-lcomp-form x)))
	  (prev-right (if (term-in-pair-form? x)
			  (term-in-pair-form-to-right x)
			  (make-term-in-rcomp-form x)))))))
    ((and (yprod-form? type1) (star-form? type2))
     (let ((prev-left (types-to-embedding (yprod-form-to-left-type type1)
					  (star-form-to-left-type type2)))
	   (prev-right (types-to-embedding (yprod-form-to-right-type type1)
					   (star-form-to-right-type type2))))
       (lambda (x) ;t pair s -> (emb t)@(emb s)
	 (make-term-in-pair-form
	  (prev-left (if (term-in-pair-form? x)
			 (term-in-pair-form-to-left x)
			 (make-term-in-lcomp-form x)))
	  (prev-right (if (term-in-pair-form? x)
			  (term-in-pair-form-to-right x)
			  (make-term-in-rcomp-form x)))))))
    (else (myerror "types-to-embedding" "increasing types expected"
		   type1 type2)))))

;; For compatibility (temporarily)

(define types-to-coercion types-to-embedding)

(define (types-lub type . types)
  (if (null? types)
      type
      (types-lub-aux type (apply types-lub types))))

(define (types-lub-aux type1 type2)
  (cond
   ((type-le? type1 type2) type2)
   ((type-le? type2 type1) type1)
   ((and (arrow-form? type1) (arrow-form? type2))
    (make-arrow (types-glb-aux (arrow-form-to-arg-type type1)
			       (arrow-form-to-arg-type type2))
		(types-lub-aux (arrow-form-to-val-type type1)
			       (arrow-form-to-val-type type2))))
   ((and (star-form? type1) (star-form? type2))
    (make-star (types-lub-aux (star-form-to-left-type type1)
			      (star-form-to-left-type type2))
	       (types-lub-aux (star-form-to-right-type type1)
			      (star-form-to-right-type type2))))
   (else (myerror "types-lub-aux" "types with least upper bound expected"
		  type1 type2))))

(define (types-glb-aux type1 type2)
  (cond
   ((type-le? type1 type2) type1)
   ((type-le? type2 type1) type2)
   ((and (arrow-form? type1) (arrow-form? type2))
    (make-arrow (types-lub-aux (arrow-form-to-arg-type type1)
			       (arrow-form-to-arg-type type2))
		(types-glb-aux (arrow-form-to-val-type type1)
			       (arrow-form-to-val-type type2))))
   ((and (star-form? type1) (star-form? type2))
    (make-star (types-glb-aux (star-form-to-left-type type1)
			      (star-form-to-right-type type1))
	       (types-glb-aux (star-form-to-left-type type2)
			      (star-form-to-right-type type2))))
   (else (myerror "types-glb-aux" "types with greatest upper bound expected"
		  type1 type2))))


