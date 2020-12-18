;; 2020-12-15.  pconst.scm
;; 4. Constants
;; ============

;; Every constant (more explicitly: object constant) has a type and
;; denotes a computable (hence continuous) functional of that type.  A
;; constant is communicated to the outside world as a string (in order
;; to allow for lower and upper case characters).

;; We have the following three kinds of constants:
;; - constructors, kind 'constr
;; - constants with user defined rules (called program(mable) constant,
;; or pconst), kind 'pconst
;; - constants whose rules are fixed, kind 'fixed-rules.

;; The latter are built into the system: recursion, (possibly guarded)
;; general recursion and corecursion operators for arbitrary algebras,
;; equality and existence operators for finitary algebras, and
;; existence elimination.  They are typed in parametrized form, with
;; the actual type (or formula) given by a type (or type and formula)
;; substitution that is also part of the constant.  For instance,
;; equality is typed by alpha=>alpha=>boole and a type substitution
;; alpha -> rho.  This is done for clarity (and brevity, e.g., for
;; large rho in the example above), since one should think of the type
;; of a constant in this way.

;; For constructors and for constants with fixed rules, by efficiency
;; reasons we keep the object denoted by the constant (as needed for
;; normalization by evaluation) as part of it.  It depends on the type
;; of the constant, hence must be updated in a given proof whenever the
;; type changes by a type substitution.  Then when normalizing it is
;; not necessary to recompute the object each time the constant is
;; considered.

;; For a program constant the denoted object needs to be updated
;; whenever a new rule is added.  These rules are of crucial importance
;; for the correctness of a proof, and should not be invisibly buried
;; in the denoted object taken as part of the constant (hence of any
;; term involving it).  Therefore we keep the rules of a program
;; constant and also its denoted objects (depending on type
;; substitutions) at a central place, a global variable
;; PROGRAM-CONSTANTS which assigns to every name of such a constant the
;; constant itself (with uninstantiated type), the rules presently
;; chosen for it and also its denoted objects (as association list with
;; type substitutions as keys).  When a new rule has been added, the
;; new objects for the program constant are computed (by
;; nbe-pconst-and-tsubst-and-rules-to-object), and the new list to be
;; associated with the program constant is written in PROGRAM-CONSTANTS
;; instead. -- We use the space kept for objects to record the arity of
;; the pconst (a non negative integer).

;; Generalities for all kinds of constants

(define (make-const
	 obj-or-arity name kind uninst-type tsubst t-deg token-type .
	 repro-data)
  (append (list 'const obj-or-arity name kind uninst-type tsubst
		t-deg token-type)
	  repro-data))

;; The type substitution tsubst must be restricted to the type
;; variables in uninst-type.

;; Repro-data are (only) necessary in proof.scm, for normalization of
;; proofs: a (general) induction, efq, introduction or elimination
;; axiom is translated into an appropriate constant, then normalized,
;; and finally from the constant and its repro data the axiom is
;; reproduced.  The repro-data are of the following forms.

;; (1) For a recursion constant.

;; (a) A list of all-formulas.  This form only occurs when translating
;; an axiom for (simultaneous) induction into a recursion constant, in
;; order to achieve normalization of proofs via term normalization.  We
;; have to consider the free variables in the scheme formulas, and let
;; the type of the recursion constant depend on them.  This is needed
;; to have the allnc-conversion be represented in term normalization.
;; The relevant operation is all-formulas-to-rec-const .

;; (b) A list of implication formulas I xs^ -> A(xs^), where all idpcs
;; are simultaneously inductively defined.  This form only occurs when
;; translating an elimination axiom into a recursion constant, in order
;; to achieve normalization of proofs via term normalization.  We again
;; have to consider the free variables in the scheme formulas, and let
;; the type of the recursion constant depend on them.  This is needed
;; to have the allnc-conversion be represented in term normalization.
;; The relevant operation is imp-formulas-to-rec-const .

;; (2) For a cases constant.  Here a single arrow-type or all-formula
;; suffices.  One uses all-formula-to-cases-const .

;; (3) For a guarded general recursion constant: an all-formula.  This
;; form only occurs when translating a general induction axiom into a
;; guarded general recursion constant, in order to achieve
;; normalization of proofs via term normalization.  We have to consider
;; the free variables in the scheme formulas, and let the type of the
;; guarded general recursion constant depend on them.  This is needed
;; to have the allnc-conversion be represented in term normalization.
;; One uses all-formula-and-number-to-grecguard-const .

;; (4) For an efq-constant (of kind 'fixed-rules): a formula.  This
;; form only occurs when translating an efq-aconst into an
;; efq-constant, in order to achieve normalization of proofs via term
;; normalization.  One uses formula-to-efq-const .

;; (5) For a constructor associated with an "Intro" axiom.

;; (a) A number i of a clause for an inductively defined predicate
;; constant, and the constant idpc.  One uses
;; number-and-idpredconst-to-intro-const .

;; (b) An ex-formula for an "Ex-Intro" axiom.  One uses
;; ex-formula-to-ex-intro-const .

;; (6) For an Ex-Elim constant (of kind 'fixed-rules): an ex-formula
;; and a conclusion.  One uses ex-formula-and-concl-to-ex-elim-const .

(define const-to-object-or-arity cadr)
(define const-to-name caddr)
(define const-to-kind cadddr)
(define (const-to-uninst-type x) (car (cddddr x)))
(define (const-to-tsubst x) (cadr (cddddr x)))
(define (const-to-t-deg x) (caddr (cddddr x)))
(define (const-to-token-type x) (cadddr (cddddr x)))
(define (const-to-repro-data x) (cddddr (cddddr x)))

(define (const-to-type const)
  (type-substitute (const-to-uninst-type const) (const-to-tsubst const)))

(define (const-to-tvars const)
  (type-to-tvars (const-to-uninst-type const)))

(define (const-form? x) (and (pair? x) (eq? 'const (car x))))

;; check-const is a test function for constants.  If the argument is
;; not a constant, an error is returned.  check-const assumes that the
;; constant is not one of those used during proof normalization.  Hence
;; repro-data must be empty.

(define (check-const x)
  (if (not (const-form? x))
      (myerror "check-const" "constant expected" x))
  (if (not (list? x))
      (myerror "check-const" "list expected" x))
  (if (not (= 8 (length x)))
      (myerror "check-const" "list of length 8 expected" x))
  (let* ((object-or-arity (cadr x))
	 (name (caddr x))
	 (kind (cadddr x))
	 (uninst-type (car (cddddr x)))
	 (tsubst (cadr (cddddr x)))
	 (t-deg (caddr (cddddr x)))
	 (token-type (cadddr (cddddr x))))
    (if (not (member kind (list 'constr 'pconst 'fixed-rules)))
	(myerror "check-const" "kind constr, pconst or fixed-rules expected"
		 kind))
    (if (and (equal? kind 'pconst)
	     (not (and (integer? object-or-arity)
		       (not (negative? object-or-arity)))))
	(myerror "check-const" "arity expected" object-or-arity))
    (if (and (member kind (list 'constr 'fixed-rules))
	     (not (nbe-object? object-or-arity)))
	(myerror "check-const" "nbe-object expected" object-or-arity))
    (if (not (string? name))
	(myerror "check-const" "string expected" name))
    (if (not (type? uninst-type))
	(myerror "check-const" "type expected" uninst-type))
    (if (not (tsubst? tsubst))
	(myerror "check-const" "tsubst expected" tsubst))
    (if (not (t-deg? t-deg))
	(myerror "check-const" "t-deg expected" t-deg))
    (if (not (memq token-type
		   '(const constscheme
			   postfix-op prefix-op add-op mul-op rel-op pair-op)))
	(myerror "check-const" "token-type expected" token-type))
    #t))

;; const? is an almost complete test for constants.  It returns true or
;; false.

(define (const? x)
  (and (const-form? x)
       (list? x)
       (<= 8 (length x))
       (let ((obj-or-arity (cadr x))
	     (name (caddr x))
	     (kind (cadddr x))
	     (uninst-type (car (cddddr x)))
	     (tsubst (cadr (cddddr x)))
	     (t-deg (caddr (cddddr x)))
	     (token-type (cadddr (cddddr x))))
	 (and (string? name)
	      (t-deg? t-deg)
	      (memq token-type
		    '(const constscheme
			    postfix-op prefix-op add-op mul-op rel-op pair-op))
	      (case kind
		((constr)
		 (and (type? uninst-type)
		      (constr-name? name)))
		((pconst)
		 (and (type? uninst-type)
		      (pconst-name? name)))
		((fixed-rules)
		 (fixed-rules-name? name))
		(else #f))))))

(define (constr-name? string) (assoc string CONSTRUCTORS))
(define (pconst-name? string) (assoc string PROGRAM-CONSTANTS))

(define (fixed-rules-name? string)
  (and (member string '("Rec" "Cases" "GRec" "GRecGuard" "CoRec" "Destr" "Map"
			"Efq" "Ex-Elim" "=" "E" "SE"))))

(define (const=? const1 const2)
  (and (string=? (const-to-name const1) (const-to-name const2))
       (equal? (const-to-type const1)
	       (const-to-type const2))))

;; Constructors

;; A constructor is a special constant with no rules.  We maintain an
;; association list CONSTRUCTORS assigning to every name of a constructor
;; an association list associating with every type substitution
;; (restricted to the type parameters) the corresponding instance of the
;; constructor.

;; Format of CONSTRUCTORS
;; ((name ((tsubst1 constr1) ... (tsubst_n constr_n))) ...)
;; where tsubst_n is the empty type substitution and constr_n the
;; uninstantiated constructor with this name.

(define CONSTRUCTORS '())

(define (constr-name-to-inst-constructors name)
  (let ((info (assoc name CONSTRUCTORS)))
    (if info
	(cadr info)
	(myerror "constr-name-to-inst-constructors" "constructor name expected"
		 name))))

(define (constr-name-and-tsubst-to-constr name tsubst)
  (let ((info (assoc name CONSTRUCTORS)))
    (if info
	(let ((info1 (assoc-wrt substitution-equal? tsubst (cadr info))))
	  (if info1
	      (cadr info1)
	      (myerror "constr-name-and-tsubst-to-constr" "unknown tsubst"
		       tsubst "for constructor" name)))
	(myerror "constr-name-and-tsubst-to-constr" "constructor name expected"
		 name))))

(define (constr-name-to-constr name . rest)
  (cond
   ((string? name)
    (let ((tsubst (if (null? rest) empty-subst (car rest))))
      (constr-name-and-tsubst-to-constr name tsubst)))
   ((and (pair? name) (string=? "Ex-Intro" (car name)))
    (let ((ex-formula
	   (if (pair? (cdr name))
	       (cadr name)
	       (myerror "constr-name-to-constr" "name expected" name))))
      (ex-formula-to-ex-intro-const ex-formula)))
   ((and (pair? name) (string=? "Intro" (car name)))
    (let ((i (if (pair? (cdr name))
		 (cadr name)
		 (myerror "constr-name-to-constr" "name expected" name)))
	  (idpc (if (pair? (cddr name))
			   (caddr name)
			   (myerror "constr-name-to-constr" "name expected"
				    name))))
      (number-and-idpredconst-to-intro-const i idpc)))
   (else (myerror "constr-name-to-constr" "name expected" name))))

(define (ex-formula-to-ex-intro-const ex-formula)
  (let* ((free (formula-to-free ex-formula))
	 (free-types (map var-to-type free))
	 (f (length free))
         (var (ex-form-to-var ex-formula))
         (kernel (ex-form-to-kernel ex-formula))
	 (type (var-to-type var))
	 (kernel-type (nbe-formula-to-type kernel))
	 (arity (+ f 2))
	 (exintroop-type
	  (apply mk-arrow
		 (append free-types
			 (list type kernel-type (make-tconst "existential")))))
	 (obj (nbe-make-object
	       exintroop-type
	       (nbe-curry
		(lambda objs
		  (nbe-make-object
		     (make-tconst "existential")
		     (nbe-make-constr-value
		      (list "Ex-Intro" ex-formula) objs)))
		exintroop-type
		arity))))
    (make-const obj "Ex-Intro" 'constr
		exintroop-type empty-subst 1 'const ex-formula)))

(define (number-and-idpredconst-to-intro-const i idpc)
  (let* ((aconst (number-and-idpredconst-to-intro-aconst i idpc))
	 (formula (aconst-to-formula aconst))
	 (introop-type (nbe-formula-to-type formula))
	 (arity (length (arrow-form-to-arg-types introop-type)))
	 (nbe-alg-type (arrow-form-to-final-val-type introop-type))
	 (constr-value-name (list "Intro" i idpc))
	 (obj (nbe-make-object
	       introop-type
	       (if (zero? arity)
		   (nbe-make-constr-value constr-value-name '())
		   (nbe-curry (lambda objs
				(nbe-make-object
				 nbe-alg-type (nbe-make-constr-value
					       constr-value-name objs)))
		    introop-type
		    arity)))))
    (make-const obj "Intro" 'constr
		introop-type empty-subst 1 'const i idpc)))

;; Constants with user defined rules, i.e., program constants.

;; Format of PROGRAM-CONSTANTS
;; ((name pconst comprules rewrules
;;        ((tsubst1 obj1) ... (tsubst_n obj_n)) opt-external-code)
;;  ...)
;; where pconst comprules rewrules are for the uninstantiated type.
;; The last obligatory entry is an association list assigning to every
;; type substitution (restricted to the type parameters) the
;; corresponding object.  The optional final entry is code of an
;; external function mapping a type substitution and an object list to
;; either an object to be returned immediately, or else to #f, in which
;; case the rules are tried next.

(define PROGRAM-CONSTANTS '())

(define (pconst-name-to-pconst name)
  (let ((info (assoc name PROGRAM-CONSTANTS)))
    (if info
	(cadr info)
	(myerror "pconst-name-to-pconst" "pconst name expected" name))))

(define (pconst-name-to-comprules name)
  (let ((info (assoc name PROGRAM-CONSTANTS)))
    (if info
	(caddr info)
	(myerror "pconst-name-to-comprules" "pconst name expected" name))))

(define (pconst-name-to-rewrules name)
  (let ((info (assoc name PROGRAM-CONSTANTS)))
    (if info
	(cadddr info)
	(myerror "pconst-name-to-rewrules" "pconst name expected" name))))

(define (pconst-name-to-inst-objs name)
  (let ((info (assoc name PROGRAM-CONSTANTS)))
    (if info
	(car (cddddr info))
	(myerror "pconst-name-to-inst-objs" "pconst name expected" name))))

(define (pconst-name-and-tsubst-to-object name tsubst)
  (let ((info (assoc name PROGRAM-CONSTANTS)))
    (if info
	(let ((info1
	       (assoc-wrt substitution-equal? tsubst (car (cddddr info)))))
	  (if info1
	      (cadr info1)
	      (let ((pconst (pconst-name-to-pconst name)))
		(const-substitute pconst tsubst #f) ;updates PROGRAM-CONSTANTS
		(pconst-name-and-tsubst-to-object name tsubst))))
	(myerror "pconst-name-and-tsubst-to-object" "pconst name expected"
		 name))))

(define (pconst-name-to-object name)
  (pconst-name-and-tsubst-to-object name empty-subst))

(define (pconst-name-to-external-code name)
  (let ((info (assoc name PROGRAM-CONSTANTS)))
    (if info
	(let ((info1 (cdr (cddddr info))))
	  (if (pair? info1)
	      (car info1)
	      #f))
	(myerror "pconst-name-to-external-code" "pconst name expected" name))))

;; A display function for program constants:

(define (display-pconst . names)
  (if
   COMMENT-FLAG
   (for-each
    (lambda (name)
      (let* ((pconst (pconst-name-to-pconst name))
	     (comprules (pconst-name-to-comprules name))
	     (rewrules (pconst-name-to-rewrules name))
	     (external-code (pconst-name-to-external-code name)))
	(display name) (newline)
	(if (pair? comprules)
	    (begin
	      (display "  comprules") (newline)
	      (do ((lc comprules (cdr lc))
		   (n 0 (+ 1 n)))
		  ((null? lc))
		(begin (display n)
		       (display tab)
		       (dt (rule-to-lhs (car lc)))
		       (display tab)
		       (dt (term-to-eta-nf (rule-to-rhs (car lc))))
		       (newline)))))
	(if (pair? rewrules)
	    (begin
	      (display "  rewrules") (newline)
	      (do ((lr rewrules (cdr lr))
		   (n 0 (+ 1 n)))
		  ((null? lr))
		(begin (display n)
		       (display tab)
		       (dt (rule-to-lhs (car lr)))
		       (display tab)
		       (dt (term-to-eta-nf (rule-to-rhs (car lr))))
		       (newline)))))
	(if (pair? external-code)
	    (let* ((char-list (string->list name))
		   (lower-case-pconst-name
		    (list->string
		     (map char-downcase char-list)))
		   (code-name (string-append lower-case-pconst-name
					     "-code")))
	      (begin (display "  external code present: evaluate ")
		     (display code-name)
		     (newline))))))
    names)))

;; For backwards compatibility we keep

(define display-program-constant display-pconst)
(define display-program-constants display-pconst)

;; In the following rest consists of an initial segment of: t-deg
;; (default 0), token type (default const), arity (default maximal
;; number of argument types) and totality-flag indicating that no proof
;; of totality is needed.

(define (add-program-constant name uninst-type . rest)
  (define (add-program-constant-aux
	   name uninst-type t-deg token-type arity totality-flag)
    (if
     (is-used? name (list uninst-type t-deg token-type arity)
	       'program-constant)
     *the-non-printing-object*
     (cond
      ((not (string? name))
       (myerror "add-program-constant" "string expected" name))
      ((not (type? uninst-type))
       (myerror "add-program-constant" "type expected" uninst-type))
      ((not (t-deg? t-deg))
       (myerror "add-program-constant" "t-degree expected" t-deg))
      ((not (and (integer? arity)
		 (not (negative? arity))
		 (<= arity (length (arrow-form-to-arg-types uninst-type)))))
       (myerror "add-program-constant" "arity expected" arity))
      ((not (memq token-type
		  '(const postfix-op prefix-op binding-op add-op mul-op
			  rel-op and-op or-op imp-op pair-op)))
       (myerror "add-program-constant" "token type expected" token-type))
      (else
       (let* ((pconst (make-const arity name 'pconst uninst-type empty-subst
				  t-deg token-type))
	      (obj
	       (if (zero? arity)
		   (nbe-reflect
		    (nbe-make-termfam
		     uninst-type
		     (lambda (k) (make-term-in-const-form pconst))))
		   (nbe-make-object
		    uninst-type
		    (nbe-curry
		     (lambda objs ;arity many
		       (let* ((obj1 (nbe-reflect
				     (nbe-make-termfam
				      uninst-type
				      (lambda (k)
				       (make-term-in-const-form pconst)))))
			      (val (nbe-object-to-value obj1)))
			 (apply (nbe-uncurry val arity) objs)))
		     uninst-type
		     arity)))))
	 (set! PROGRAM-CONSTANTS
	       (cons (list name pconst '() '() (list (list empty-subst obj)))
		     PROGRAM-CONSTANTS))
	 (if (null? (type-to-tvars uninst-type))
	     (add-token name
			token-type
			(const-to-token-value pconst))
	     (add-token name
			'constscheme
			pconst))
	 (if (not (member name
			  (list "cEfqLog" "cStabLog" "cEfq" "cStab" "cId"
				"cIf" "Inhab"
				"AndConst" "ImpConst" "OrConst" "NegConst"
				"PairOne" "PairTwo")))
	     (begin
	       (comment
		"ok, program constant " name ": "
		(type-to-string uninst-type))
	       (if (not (eq? 'const token-type))
		   (comment "of token type " token-type " and"))
	       (comment "of t-degree " t-deg " and arity " arity
			" added")
	       (if (and (t-deg-one? t-deg)
			(not totality-flag)
			(not (assoc (string-append name "Total") THEOREMS)))
		   (comment "warning: theorem "
			    (string-append name "Total")
			    " stating totality missing")))))))))
  (let ((l (length (arrow-form-to-arg-types uninst-type))))
    (if
     (null? rest)
     (add-program-constant-aux name uninst-type 0 'const l #f)
     (let ((t-deg (car rest)))
       (if
	(null? (cdr rest))
	(add-program-constant-aux name uninst-type t-deg 'const l #f)
	(let ((token-type (cadr rest)))
	  (if
	   (null? (cddr rest))
	   (add-program-constant-aux name uninst-type t-deg token-type l #f)
	   (let ((arity (caddr rest)))
	     (if
	      (null? (cdddr rest))
	      (add-program-constant-aux
	       name uninst-type t-deg token-type arity #f)
	      (add-program-constant-aux
	       name uninst-type t-deg token-type arity (cadddr rest)))))))))))

(define apc add-program-constant)

;; To make program constants more readable we provide
;; add-prefix-display-string add-postfix-display-string
;; add-infix-display-string .

(define (add-prefix-display-string name1 name2)
  (let* ((const (cond ((constr-name? name1) (constr-name-to-constr name1))
		      ((pconst-name? name1) (pconst-name-to-pconst name1))
		      (else (myerror "add-prefix-display-string"
				     "name of constructor or pconst expected"
				     name1))))
	 (uninst-type (const-to-uninst-type const))
	 (arity (cond ((constr-name? name1)
		       (length (arrow-form-to-arg-types uninst-type)))
		      ((pconst-name? name1)
		       (const-to-object-or-arity const))
		      (else (myerror "add-prefix-display-string"
				     "name of constructor or pconst expected"
				     name1)))))
    (if
     (not (= 1 arity))
     (myerror "add-prefix-display-string" "arity 1 expected for const" name1))
    (add-token
     name2 'prefix-op
     (lambda (x)
       (make-term-in-app-form
	(make-term-in-const-form
	 (let* ((const (cond
			((constr-name? name1) (constr-name-to-constr name1))
			((pconst-name? name1) (pconst-name-to-pconst name1))
			(else (myerror "add-prefix-display-string"
				       "name of constructor or pconst expected"
				       name1))))
		(uninst-type (const-to-uninst-type const))
		(pattern (arrow-form-to-arg-type uninst-type))
		(instance (term-to-type x))
		(tsubst (type-match pattern instance)))
	   (if tsubst
	       (const-substitute const tsubst #f)
	       (myerror "types do not match" pattern instance))))
	x)))
    (add-display
     (arrow-form-to-val-type uninst-type)
     (lambda (x)
       (if (term-in-app-form? x)
	   (let ((op (term-in-app-form-to-final-op x)))
	     (if
	      (and (term-in-const-form? op)
		   (string=? name1
			     (const-to-name (term-in-const-form-to-const op))))
	      (list 'prefix-op name2
		    (term-to-token-tree (term-in-app-form-to-arg x)))
	      #f))
	   #f)))))

(define (add-postfix-display-string name1 name2)
  (let* ((const (cond ((constr-name? name1) (constr-name-to-constr name1))
		      ((pconst-name? name1) (pconst-name-to-pconst name1))
		      (else (myerror "add-postfix-display-string"
				     "name of constructor or pconst expected"
				     name1))))
	 (uninst-type (const-to-uninst-type const))
	 (arity (cond ((constr-name? name1)
		       (length (arrow-form-to-arg-types uninst-type)))
		      ((pconst-name? name1)
		       (const-to-object-or-arity const))
		      (else (myerror "add-postfix-display-string"
				     "name of constructor or pconst expected"
				     name1)))))
    (if
     (not (= 1 arity))
     (myerror "add-postfix-display-string" "arity 1 expected for const" name1))
    (add-token
     name2 'postfix-op
     (lambda (x)
       (make-term-in-app-form
	(make-term-in-const-form
	 (let* ((const (cond
			((constr-name? name1) (constr-name-to-constr name1))
			((pconst-name? name1) (pconst-name-to-pconst name1))
			(else (myerror "add-postfix-display-string"
				       "name of constructor or pconst expected"
				       name1))))
		(uninst-type (const-to-uninst-type const))
		(pattern (arrow-form-to-arg-type uninst-type))
		(instance (term-to-type x))
		(tsubst (type-match pattern instance)))
	   (if tsubst
	       (const-substitute const tsubst #f)
	       (myerror "types do not match" pattern instance))))
	x)))
    (add-display
     (arrow-form-to-val-type uninst-type)
     (lambda (x)
       (if (term-in-app-form? x)
	   (let ((op (term-in-app-form-to-final-op x)))
	     (if
	      (and (term-in-const-form? op)
		   (string=? name1
			     (const-to-name (term-in-const-form-to-const op))))
	      (list 'postfix-op name2
		    (term-to-token-tree (term-in-app-form-to-arg x)))
	      #f))
	   #f)))))

(define (add-infix-display-string name1 name2 token-type)
  (let* ((const (cond ((constr-name? name1)
		       (constr-name-to-constr name1))
		      ((pconst-name? name1)
		       (pconst-name-to-pconst name1))
		      (else (myerror "add-infix-display-string"
				     "name of constructor or pconst expected"
				     name1))))
	 (uninst-type (const-to-uninst-type const)))
    (if (not (memq token-type
		  '(const add-op mul-op rel-op and-op or-op imp-op pair-op)))
	(myerror "add-infix-display-string" "token type expected" token-type))
    (if (not (<= 2 (length (arrow-form-to-arg-types uninst-type))))
	(myerror "add-infix-display-string" "arity >= 2 expected for const"
		 name1))
    (add-token
     name2 token-type
     (lambda (x y)
       (mk-term-in-app-form
	(make-term-in-const-form
	 (let* ((const
		 (cond ((constr-name? name1)
			(constr-name-to-constr name1))
		       ((pconst-name? name1)
			(pconst-name-to-pconst name1))
		       (else (myerror "add-infix-display-string"
				      "name of constructor or pconst expected"
				      name1))))
		(uninst-type (const-to-uninst-type const))
		(patterns (arrow-form-to-arg-types uninst-type 2))
		(instances (map term-to-type (list x y)))
		(tsubst (type-match-list patterns instances)))
	   (if tsubst
	       (const-substitute const tsubst #f)
	       (myerror "types do not match"
			(car patterns) (cadr patterns)
			(term-to-type x) (term-to-type y)))))
	x y)))
    (add-display
     (arrow-form-to-final-val-type uninst-type)
     (lambda (x)
       (if (term-in-app-form? x)
	   (let ((op (term-in-app-form-to-final-op x))
		 (args (term-in-app-form-to-args x)))
	     (if
	      (and (term-in-const-form? op)
		   (string=? name1
			     (const-to-name (term-in-const-form-to-const op)))
		   (= 2 (length args)))
	      (list token-type name2
		    (term-to-token-tree (car args))
		    (term-to-token-tree (cadr args)))
	      #f))
	   #f)))))

(define (remove-program-constant . strings)
  (define (rpc1 pconst-name)
    (if (assoc pconst-name PROGRAM-CONSTANTS)
	(begin
	  (do ((l PROGRAM-CONSTANTS (cdr l))
	       (res '() (if (string=? pconst-name (caar l))
			    res
			    (cons (car l) res))))
	      ((null? l) (set! PROGRAM-CONSTANTS (reverse res))))
	  
	  (set! THEOREMS
		(list-transform-positive THEOREMS
		  ;; remove those with string-to-first-name = name and
		  ;; string-to-last-name = CompRule or = RewRule
		  (lambda (x)
		    (let ((thm-name (car x)))
		      (or (not (member (string-to-last-name thm-name)
				       (list "CompRule" "RewRule")))
			  (not (string=? (string-to-first-name thm-name)
					 pconst-name)))))))
	  (remove-token pconst-name)
	  (comment "ok, program constant " pconst-name " removed"))
	(multiline-comment "remove-program-constant"
			   "program constant expected" pconst-name)))
  (for-each rpc1 strings))

(define rpc remove-program-constant)

;; Computation rules and rewrite rules are association lists associating
;; a rhs to a lhs.

(define rule-to-lhs car)
(define rule-to-rhs cadr)
(define (lhs-and-rhs-to-rule lhs rhs) (list lhs rhs))

(define (add-computation-rule x y)
  (let* ((lhs (if (string? x) (pt x) x))
	 (rhs (if (string? y) (pt y) y))
	 (type1 (term-to-type lhs))
	 (type2 (term-to-type rhs)))
    (if (not (term-form? lhs))
	(myerror "add-computation-rule" "term expected" x))
    (if (not (term-form? rhs))
	(myerror "add-computation-rule" "term expected" y))
    (if (not (type-le? type2 type1))
	(myerror
	 "add-computation-rule" "unexpected types.  Lhs:"
	 lhs "with type" type1
	 "Rhs:" rhs "of type" type2))
    (let* ((op (term-in-app-form-to-final-op lhs))
	   (args (term-in-app-form-to-args lhs))
	   (lhsfree (term-to-free lhs))
	   (embedded-rhs ((types-to-embedding type2 type1) rhs)))
      (if (not (and (term-in-const-form? op)
		    (eq? 'pconst
			 (const-to-kind (term-in-const-form-to-const op)))))
	  (myerror "add-computation-rule" "program constant expected" op))
      (if (and (pair? (const-to-tsubst (term-in-const-form-to-const op)))
	       (positive? (const-to-object-or-arity
			   (term-in-const-form-to-const op))))
	  (myerror "add-computation-rule" "expected type variables are"
		   (term-in-const-form-to-string
		    (make-term-in-const-form
		     (pconst-name-to-pconst
		      (const-to-name (term-in-const-form-to-const op)))))))
      (if (not (= (length args) (const-to-object-or-arity
				 (term-in-const-form-to-const op))))
	  (myerror "add-computation-rule" "number of args should be"
		   (const-to-object-or-arity
		    (term-in-const-form-to-const op))))
      (do ((l args (cdr l))
	   (free '() (union (term-to-free (car l)) free)))
	  ((null? l) #f)
	(if (not (nbe-constructor-pattern? (car l)))
	    (myerror "add-computation-rule" "constructor pattern expected"
		     (car l))
	    (if (not (null? (intersection free (term-to-free (car l)))))
		(myerror "add-computation-rule"
			 "left linear lhs expected" lhs))))
      (if (not (null? (set-minus (term-to-free rhs) lhsfree)))
	  (apply myerror
		 "add-computation-rule" "new free vars in rhs"
		 (set-minus (term-to-free rhs) lhsfree)))
      (let* ((pconst (term-in-const-form-to-const op))
	     (name (const-to-name pconst))
	     (comprules (pconst-name-to-comprules name))
	     (rewrules (pconst-name-to-rewrules name))
	     (arity (const-to-object-or-arity pconst))
	     (renamed-lhs-and-rhs
	      (if (zero? arity)
		  (let* ((lhs-tvars (const-to-tvars pconst))
			 (new-tvars (map (lambda (x) (new-tvar)) lhs-tvars))
			 (new-tsubst
			  (map list lhs-tvars new-tvars)))
		    (list (term-substitute lhs new-tsubst)
			  (term-substitute embedded-rhs new-tsubst)))
		  (let* ((newvars (map (lambda (x) (make-term-in-var-form
						    (var-to-new-var x)))
				       lhsfree))
			 (subst (map list lhsfree newvars)))
		    (list (term-substitute lhs subst)
			  (term-substitute embedded-rhs subst)))))
	     (renamed-lhs (car renamed-lhs-and-rhs))
	     (renamed-rhs (cadr renamed-lhs-and-rhs)))
	(for-each ;of comprules
	 (lambda (cr)
	   (let ((old-lhs (car cr))
		 (old-rhs (cadr cr)))
	     (if
	      (if (zero? arity)
		  (let ((tunif (type-unify (term-to-type old-lhs)
					   (term-to-type renamed-lhs))))
		    (and tunif
			 (not (term=? (term-substitute old-rhs tunif)
				      (term-substitute renamed-rhs tunif)))))
		  (let ((unif (unify old-lhs renamed-lhs)))
		    (and unif
			 (not (term=? (term-substitute old-rhs unif)
				      (term-substitute renamed-rhs unif))))))
	      (myerror
	       "add-computation-rule" lhs "->" rhs
	       "is in conflict with already existing computation rule"
	       old-lhs "->" old-rhs))))
	 comprules)
	(let*
	    ((new-comprules
	      (append
	       comprules
	       (list
		(list
		 lhs
		 (term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs
		  embedded-rhs)))))
	     (tsubst-obj-alist (pconst-name-to-inst-objs name))
	     (external-code (pconst-name-to-external-code name))
	     (new-tsubst-obj-alist
	      (if
	       (zero? arity)
	       (let* ((internal-tsubst (const-to-tsubst pconst))
		      (reduced-tsubst-obj-alist
		       (list-transform-positive
			   tsubst-obj-alist
			 (lambda (p)
			   (not (tsubst-match internal-tsubst (car p)))))))
		 (cons (list internal-tsubst
			     (nbe-term-to-object
			      embedded-rhs (nbe-make-bindings '() '())))
		       reduced-tsubst-obj-alist))
					;map nbe-... through tsubst-obj-alist
	       (map (lambda (x)
		      (list
		       (car x)
		       (if
			external-code
			(nbe-pconst-and-tsubst-and-rules-to-object
			 pconst (car x) new-comprules rewrules external-code)
			(nbe-pconst-and-tsubst-and-rules-to-object
			 pconst (car x) new-comprules rewrules))))
		    tsubst-obj-alist)))
	     (uninst-pconst (pconst-name-to-pconst name))
	     (pconsts-except-name
	      (do ((l PROGRAM-CONSTANTS (cdr l))
		   (res '() (if (string=? (caar l) name)
				res
				(cons (car l) res))))
		  ((null? l) (reverse res)))))
	  (set! PROGRAM-CONSTANTS
		(cons (if external-code
			  (list name uninst-pconst new-comprules rewrules
				new-tsubst-obj-alist external-code)
			  (list name uninst-pconst new-comprules rewrules
				new-tsubst-obj-alist))
		      pconsts-except-name))
	  (let* ((n (length comprules))
		 (proof (pconst-name-and-number-to-comprule-proof name n))
		 (thm-name
		  (string-append name (number-to-string n) "CompRule")))
	    (set! OLD-COMMENT-FLAG COMMENT-FLAG)
	    (set! COMMENT-FLAG #f)
	    (add-theorem thm-name proof)
	    (set! COMMENT-FLAG OLD-COMMENT-FLAG)
	    (if (not (member name (list "Inhab" "AndConst" "ImpConst"
					"OrConst" "NegConst"
					"PairOne" "PairTwo")))
		(comment
		 "ok, computation rule " (term-to-string lhs) " -> "
		 (term-to-string embedded-rhs) " added"))))))))

(define (constr-type-to-constr-param-types constr-type)
  (let* ((alg-name (alg-form-to-name
		    (arrow-form-to-final-val-type constr-type)))
	 (simalg-names (alg-name-to-simalg-names alg-name))
	 (argtypes (arrow-form-to-arg-types constr-type)))
    (list-transform-positive argtypes
      (lambda (argtype)
	(let ((valtype (arrow-form-to-final-val-type argtype)))
	  (not (and (alg-form? valtype)
		    (member (alg-form-to-name valtype) simalg-names))))))))

(define (add-computation-rules . x)
  (if (odd? (length x))
      (myerror "add-computation-rules" "even number of arguments expected"))
  (if (null? x)
      (myerror "add-computation-rules" "arguments expected"))
  (letrec ((acr (lambda (ts)
                  (if (< 3 (length ts))
                      (begin
                        (add-computation-rule (car ts) (cadr ts))
                        (acr (cddr ts)))
                      (add-computation-rule (car ts) (cadr ts))))))
    (acr x)))

(define acrs add-computation-rules)

(define (add-rewrite-rule x y . opt-proof)
  (let* ((lhs (if (string? x) (pt x) x))
	 (rhs (if (string? y) (pt y) y))
	 (type1 (term-to-type lhs))
	 (type2 (term-to-type rhs))
	 (proof (if (null? opt-proof)
		    (pproof-state-to-proof)
		    (let ((p (car opt-proof)))
		      (if (string? p)
			  (theorem-name-to-proof p)
			  p)))))
    (if (not (term-in-app-form? lhs))
	(myerror "add-rewrite-rule" "term in app form expected" lhs))
    (if (not (type-le? type2 type1))
	(myerror
	 "add-rewrite-rule" "unexpected types.  Lhs:"
	 lhs "with type" type1
	 "Rhs:" rhs "of type" type2))
    (let ((op (term-in-app-form-to-final-op lhs))
	  (args (term-in-app-form-to-args lhs))
	  (embedded-rhs ((types-to-embedding type2 type1) rhs)))
      (if (and (term-in-const-form? op)
	       (eq? 'constr (const-to-kind (term-in-const-form-to-const op))))
	  (myerror "add-rewrite-rule" "non-constructor expected" op))
      (if (not (and (term-in-const-form? op)
		    (eq? 'pconst
			 (const-to-kind (term-in-const-form-to-const op)))))
	  (myerror "add-rewrite-rule" "program constant expected" op))
      (if (pair? (const-to-tsubst (term-in-const-form-to-const op)))
	  (myerror
	   "add-rewrite-rule"
	   "arguments in lhs need to fit the *unsubstituted* type of op"
	   (const-to-type
	    (pconst-name-to-pconst
	     (const-to-name (term-in-const-form-to-const op))))))
      (if (not (= (length args) (const-to-object-or-arity
				 (term-in-const-form-to-const op))))
	  (myerror
	   "add-rewrite-rule" "number of args should be"
	   (const-to-object-or-arity (term-in-const-form-to-const op))))
      (if (not (null? (set-minus (term-to-free rhs) (term-to-free lhs))))
	  (apply myerror
		 "add-rewrite-rule" "new free vars in rhs"
		 (set-minus (term-to-free rhs) (term-to-free lhs))))
      (let ((rewrite-flas
	     (if (and (term-in-const-form? rhs)
		      (string=? "True" (const-to-name
					(term-in-const-form-to-const rhs))))
		 (list (make-atomic-formula lhs))
		 (if (finalg? (term-to-type lhs))
		     (list (make-= lhs rhs))
		     (list (make-eqd lhs rhs))))))
	(if (or (not (proof-form? proof))
		(pair? (proof-to-free-avars proof))
		(not (member-wrt formula=?
				 (cadr (all-allnc-form-to-vars-and-final-kernel
					(proof-to-formula proof)))
				 rewrite-flas)))
	    (add-global-assumption
	     (new-global-assumption-name "RewriteGA")
	     (apply mk-all (append (formula-to-free (car rewrite-flas))
				   (list (car rewrite-flas)))))))
      (let* ((pconst (term-in-const-form-to-const op))
	     (name (const-to-name pconst))
	     (comprules (pconst-name-to-comprules name))
	     (rewrules (pconst-name-to-rewrules name))
	     (new-rewrules
	      (append
	       rewrules
	       (list
		(list
		 lhs
		 (term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs
		  embedded-rhs)))))
	     (tsubst-obj-alist (pconst-name-to-inst-objs name))
	     (external-code (pconst-name-to-external-code name))
	     (pconsts-except-name
	      (do ((l PROGRAM-CONSTANTS (cdr l))
		   (res '() (if (string=? (caar l) name)
				res
				(cons (car l) res))))
		  ((null? l) (reverse res))))
	     (new-alist-for-name
	      (map (lambda (x)
		     (list
		      (car x)
		      (if external-code
			  (nbe-pconst-and-tsubst-and-rules-to-object
			   pconst (car x) comprules new-rewrules external-code)
			  (nbe-pconst-and-tsubst-and-rules-to-object
			   pconst (car x) comprules new-rewrules))))
		   tsubst-obj-alist))
	     (uninst-pconst (pconst-name-to-pconst name)))
	(set! PROGRAM-CONSTANTS
	      (cons (if external-code
			(list name uninst-pconst comprules new-rewrules
			      new-alist-for-name external-code)
			(list name uninst-pconst comprules new-rewrules
			      new-alist-for-name))
		    pconsts-except-name))
	(let* ((n (length rewrules))
	       (proof (pconst-name-and-number-to-rewrule-proof name n))
	       (thm-name
		(string-append name (number-to-string n) "RewRule")))
	  (set! OLD-COMMENT-FLAG COMMENT-FLAG)
	  (set! COMMENT-FLAG #f)
	  (add-theorem thm-name proof)
	  (set! COMMENT-FLAG OLD-COMMENT-FLAG)
	  (if (not (member name
			   (list "AndConst" "ImpConst" "OrConst" "NegConst")))
	      (comment "ok, rewrite rule " (term-to-string lhs) " -> "
		       (term-to-string embedded-rhs) " added")))))))

;; change-t-deg-to-one takes a list of pconst-names as arguments.
;; This is necessary to have all these pconsts in the stored totality
;; theorems with t-deg one.

(define (change-t-deg-to-one . names)
  (for-each (lambda (name)
	      (if (not (assoc name PROGRAM-CONSTANTS))
		  (myerror "change-t-deg-to-one"
			   "name of program constant expected" name)))
	    names)
  (let* ((pconsts (map pconst-name-to-pconst names))
	 (comprules ;for all pconsts
	  (apply append (map pconst-name-to-comprules names)))
	 (rewrules ;for all pconsts
	  (apply append (map pconst-name-to-rewrules names)))
	 (codes ;some may be #f
	  (map pconst-name-to-external-code names))
	 (arities (map const-to-object-or-arity pconsts))
	 (uninst-types (map const-to-uninst-type pconsts))
	 (token-types (map const-to-token-type pconsts))
	 (new-pconsts ;now with t-deg-one
	  (map (lambda (arity name uninst-type token-type)
		 (make-const arity name 'pconst uninst-type empty-subst
			     t-deg-one token-type))
	       arities names uninst-types token-types))
	 (new-objs
	  (map (lambda (arity uninst-type new-pconst)
		 (if (zero? arity)
		     (nbe-reflect
		      (nbe-make-termfam
		       uninst-type
		       (lambda (k) (make-term-in-const-form new-pconst))))
		     (nbe-make-object
		      uninst-type
		      (nbe-curry
		       (lambda objs ;arity many
			 (let* ((obj1 (nbe-reflect
				       (nbe-make-termfam
					uninst-type
					(lambda (k)
					  (make-term-in-const-form
					   new-pconst)))))
				(val (nbe-object-to-value obj1)))
			   (apply (nbe-uncurry val arity) objs)))
		       uninst-type
		       arity))))
	       arities uninst-types new-pconsts))
	 (inst-objs-list (map (lambda (new-obj)
				(list (list empty-subst new-obj)))
			      new-objs))
	 (new-pc-items ;to be added to PROGRAM-CONSTANTS
	  (map (lambda (name new-pconst inst-objs code)
		 (if code
		     (list name new-pconst '() '() inst-objs code)
		     (list name new-pconst '() '() inst-objs)))
	       names new-pconsts inst-objs-list codes))
	 (gen-subst (map list (map make-term-in-const-form pconsts)
			 (map make-term-in-const-form new-pconsts)))
	 (new-comprules ;with new-pconsts rather than pconsts
	  (map (lambda (comprule)
		 (lhs-and-rhs-to-rule
		  (term-gen-substitute (rule-to-lhs comprule) gen-subst)
		  (term-gen-substitute (rule-to-rhs comprule) gen-subst)))
	       comprules))
	 (new-rewrules ;with new-pconsts rather than pconsts
	  (map (lambda (rewrule)
		 (lhs-and-rhs-to-rule
		  (term-gen-substitute (rule-to-lhs rewrule) gen-subst)
		  (term-gen-substitute (rule-to-rhs rewrule) gen-subst)))
	       rewrules))
	 (pconsts-except-names
	  (do ((l PROGRAM-CONSTANTS (cdr l))
	       (res '() (if (member (caar l) names)
			    res
			    (cons (car l) res))))
	      ((null? l) (reverse res))))
	 (theorems-without-rules-for-names ;remove all with names NatPlus1...
	  (list-transform-positive THEOREMS
	    (lambda (x)
	      (let* ((thm-name (car x))
		     (first-name (string-to-first-name thm-name))
		     (l (string-length first-name)))
		(not (and (member first-name names)
			  (< l (string-length thm-name))
			  (char-numeric? (string-ref thm-name l)))))))))
    (for-each remove-token names)
    ;; add again the pconsts, now as new-pconsts with t-deg-one
    (set! PROGRAM-CONSTANTS (append new-pc-items pconsts-except-names))
    ;; add again names as tokens, now using the new-pconsts
    (for-each (lambda (uninst-type name pconst new-pconst)
		(if (null? (type-to-tvars uninst-type))
		    (add-token name
			       (const-to-token-type pconst)
			       (const-to-token-value new-pconst))
		    (add-token name
			       'constscheme
			       new-pconst)))
	      uninst-types names pconsts new-pconsts)
    ;; remove theorems with names like NatPlus1...
    (set! THEOREMS theorems-without-rules-for-names)
    ;; add again the previous comprules, now using the new-pconsts
    (for-each (lambda (new-comprule)
		(let* ((new-lhs (rule-to-lhs new-comprule))
		       (new-rhs (rule-to-rhs new-comprule))
		       (type1 (term-to-type new-lhs))
		       (type2 (term-to-type new-rhs)))
		  (add-computation-rule
		   new-lhs
		   ((types-to-embedding type2 type1) new-rhs))))
	      new-comprules)
    (for-each (lambda (new-rewrule)
		(let* ((new-lhs (rule-to-lhs new-rewrule))
		       (new-rhs (rule-to-rhs new-rewrule))
		       (type1 (term-to-type new-lhs))
		       (type2 (term-to-type new-rhs)))
		  (add-rewrite-rule
		   new-lhs
		   ((types-to-embedding type2 type1) new-rhs))))
	      new-rewrules)))

(define arw add-rewrite-rule)

(define (add-rewrite-rules . x)
  (if (odd? (length x))
      (myerror "add-rewrite-rules" "even number of arguments expected"))
  (if (null? x)
      (myerror "add-rewrite-rules" "arguments expected"))
  (letrec ((arr (lambda (ts)
                  (if (< 3 (length ts))
                      (begin
                        (add-rewrite-rule (car ts) (cadr ts))
                        (arr (cddr ts)))
                      (add-rewrite-rule (car ts) (cadr ts))))))
    (arr x)))

(define arws add-rewrite-rules)

(define (add-external-code name code)
  (let ((info (assoc name PROGRAM-CONSTANTS)))
    (if (not info)
	(myerror "add-external-code" "name of program constant expected" name))
    (let* ((comprules (pconst-name-to-comprules name))
	   (rewrules (pconst-name-to-rewrules name))
	   (tsubst-obj-alist (pconst-name-to-inst-objs name))
	   (pconsts-except-name
	    (do ((l PROGRAM-CONSTANTS (cdr l))
		 (res '() (if (string=? (caar l) name)
			      res
			      (cons (car l) res))))
		((null? l) (reverse res))))
	   (pconst (pconst-name-to-pconst name))
	   (new-alist-for-name
	    (map (lambda (x)
		   (list (car x) (nbe-pconst-and-tsubst-and-rules-to-object
				  pconst (car x) comprules rewrules code)))
		 tsubst-obj-alist)))
      (set! PROGRAM-CONSTANTS
	    (cons (list name pconst comprules rewrules new-alist-for-name code)
		  pconsts-except-name))
      (comment "ok, external code added for program constant " name))))

(define (remove-computation-rules-for lhs)
  (if (not (term-form? lhs))
      (myerror "remove-computation-rules-for" "term expected" lhs))
  (let* ((op (term-in-app-form-to-final-op lhs))
	 (args (term-in-app-form-to-args lhs)))
    (if (not (and (term-in-const-form? op)
		  (eq? 'pconst
		       (const-to-kind (term-in-const-form-to-const op)))))
	(myerror "remove-computation-rules-for"
		 "program constant expected" op))
    (if (not (= (length args) (const-to-object-or-arity
			       (term-in-const-form-to-const op))))
	(myerror "remove-computation-rules-for" "number of args should be"
		 (const-to-object-or-arity (term-in-const-form-to-const op))))
    (let* ((pconst (term-in-const-form-to-const op))
	   (name (const-to-name pconst))
	   (comprules (pconst-name-to-comprules name))
	   (rewrules (pconst-name-to-rewrules name))
	   (new-comprules
	    (list-transform-positive comprules
	      (lambda (comprule) (not (match lhs (car comprule))))))
	   (tsubst-obj-alist (pconst-name-to-inst-objs name))
	   (external-code (pconst-name-to-external-code name))
	   (pconsts-except-name
	    (do ((l PROGRAM-CONSTANTS (cdr l))
		 (res '() (if (string=? (caar l) name)
			      res
			      (cons (car l) res))))
		((null? l) (reverse res))))
	   (new-alist-for-name
	    (map (lambda (x)
		   (list
		    (car x)
		    (if external-code
			(nbe-pconst-and-tsubst-and-rules-to-object
			 pconst (car x) new-comprules rewrules external-code)
			(nbe-pconst-and-tsubst-and-rules-to-object
			 pconst (car x) new-comprules rewrules))))
		 tsubst-obj-alist))
	   (uninst-pconst (pconst-name-to-pconst name)))
      (set! PROGRAM-CONSTANTS
	    (cons (list name uninst-pconst new-comprules rewrules
			new-alist-for-name)
		  pconsts-except-name))
      (set! THEOREMS
	    (list-transform-positive THEOREMS
	      ;; remove those with string-to-first-name = name and
	      ;; string-to-last-name = CompRule
	      (lambda (x)
		(let ((thm-name (car x)))
		  (or (not (string=? (string-to-last-name thm-name) "CompRule"))
		      (not (string=? (string-to-first-name thm-name) name)))))))
      (comment "ok, computation rules of the form " (term-to-string lhs)
	       " removed"))))

(define (remove-rewrite-rules-for lhs)
  (let* ((op (term-in-app-form-to-final-op lhs))
	 (args (term-in-app-form-to-args lhs)))
    (if (not (and (term-in-const-form? op)
		  (eq? 'pconst
		       (const-to-kind (term-in-const-form-to-const op)))))
	(myerror "remove-rewrite-rules-for" "program constant expected" op))
    (if (not (= (length args) (const-to-object-or-arity
			       (term-in-const-form-to-const op))))
	(myerror "remove-rewrite-rules-for" "number of args should be"
		 (const-to-object-or-arity (term-in-const-form-to-const op))))
    (let* ((pconst (term-in-const-form-to-const op))
	   (name (const-to-name pconst))
	   (comprules (pconst-name-to-comprules name))
	   (rewrules (pconst-name-to-rewrules name))
	   (new-rewrules
	    (list-transform-positive rewrules
	      (lambda (rewrule) (not (match lhs (car rewrule))))))
	   (tsubst-obj-alist (pconst-name-to-inst-objs name))
	   (external-code (pconst-name-to-external-code name))
	   (pconsts-except-name
	    (do ((l PROGRAM-CONSTANTS (cdr l))
		 (res '() (if (string=? (caar l) name)
			      res
			      (cons (car l) res))))
		((null? l) (reverse res))))
	   (new-alist-for-name
	    (map (lambda (x)
		   (list
		    (car x)
		    (if external-code
			(nbe-pconst-and-tsubst-and-rules-to-object
			 pconst (car x) comprules new-rewrules external-code)
			(nbe-pconst-and-tsubst-and-rules-to-object
			 pconst (car x) comprules new-rewrules))))
		 tsubst-obj-alist))
	   (uninst-pconst (pconst-name-to-pconst name)))
      (set! PROGRAM-CONSTANTS
	    (cons (list name uninst-pconst comprules new-rewrules
			new-alist-for-name)
		  pconsts-except-name))
      (set! THEOREMS
	    (list-transform-positive THEOREMS
	      ;; remove those with string-to-first-name = name and
	      ;; string-to-last-name = CompRule
	      (lambda (x)
		(let ((thm-name (car x)))
		  (or (not (string=? (string-to-last-name thm-name) "RewRule"))
		      (not (string=? (string-to-first-name thm-name) name)))))))
      (comment "ok, rewrite rules with lhs of the form "
	       (term-to-string lhs)
	       " removed"))))

(define (remove-external-code name)
  (let ((info (assoc name PROGRAM-CONSTANTS)))
    (if (not info)
	(myerror "remove-external-code"
		 "name of program constant expected" name))
    (let* ((comprules (pconst-name-to-comprules name))
	   (rewrules (pconst-name-to-rewrules name))
	   (tsubst-obj-alist (pconst-name-to-inst-objs name))
	   (pconsts-except-name
	    (do ((l PROGRAM-CONSTANTS (cdr l))
		 (res '() (if (string=? (caar l) name)
			      res
			      (cons (car l) res))))
		((null? l) (reverse res))))
	   (pconst (pconst-name-to-pconst name))
	   (new-alist-for-name
	    (map (lambda (x)
		   (list (car x) (nbe-pconst-and-tsubst-and-rules-to-object
				  pconst (car x) comprules rewrules)))
		 tsubst-obj-alist)))
      (set! PROGRAM-CONSTANTS
	    (cons (list name pconst comprules rewrules new-alist-for-name)
		  pconsts-except-name))
      (comment "ok, external code removed for program constant " name))))

;; nbe-pconst-and-tsubst-and-rules-to-object instantiates the rules
;; with (given) tsubst (not the one from pconst) and then computes the
;; object.  It is assumed that tsubst is restricted to the tvars in the
;; type of pconst.

(define (nbe-pconst-and-tsubst-and-rules-to-object
	 pconst tsubst comprules rewrules . rest)
  (let* ((tsubst-obj-alist (pconst-name-to-inst-objs (const-to-name pconst)))
	 (info (assoc-wrt substitution-equal? tsubst tsubst-obj-alist))
	 (arity (const-to-object-or-arity pconst))
	 (uninst-type (const-to-uninst-type pconst))
	 (inst-type (type-substitute uninst-type tsubst))
	 (inst-pconst
	  (make-const arity (const-to-name pconst) 'pconst
		      uninst-type tsubst (const-to-t-deg pconst)
		      (const-to-token-type pconst)))
	 (rules (append comprules rewrules))
	 (rule-terms (append (map rule-to-lhs rules) (map rule-to-rhs rules)))
	 (vars (apply union (map term-to-free rule-terms)))
	 (critical-tvars (map car tsubst))
	 (critical-vars
	  (list-transform-positive vars
	    (lambda (var)
	      (pair? (intersection (type-to-tvars (var-to-type var))
				   critical-tvars)))))
	 (renaming-subst
	  (map (lambda (var)
		 (let* ((type (var-to-type var))
			(new-type (type-substitute type tsubst))
			(new-var
			 (if (t-deg-one? (var-to-t-deg var))
			     (type-to-new-var new-type var)
			     (type-to-new-partial-var new-type var))))
		   (list var (make-term-in-var-form new-var))))
	       critical-vars))
	 (tosubst (append tsubst renaming-subst))
	 (inst-comprules
	  (map (lambda (cr)
		 (let ((lhs (rule-to-lhs cr))
		       (rhs (rule-to-rhs cr)))
		   (lhs-and-rhs-to-rule
		    (term-substitute lhs tosubst)
		    (term-substitute rhs tosubst))))
	       comprules))
	 (inst-rewrules
	  (map (lambda (cr)
		 (let ((lhs (rule-to-lhs cr))
		       (rhs (rule-to-rhs cr)))
		   (lhs-and-rhs-to-rule
		    (term-substitute lhs tosubst)
		    (term-substitute rhs tosubst))))
	       rewrules))
	 (external-proc (if (pair? rest)
			    (ev (car rest))
			    (lambda (tsubst objs) #f))))
    (if
     (zero? arity)
     (let* ((repro-obj
	     (nbe-reflect (nbe-make-termfam
			   inst-type
			   (lambda (k)
			     (make-term-in-const-form inst-pconst)))))
	    (pattern (const-to-type pconst))
	    (subst-pconst (const-substitute pconst tsubst #t))
	    (instance (const-to-type subst-pconst))
	    (match-test (type-match pattern instance)))
       (if
	match-test ;else reproduce
	(or ;return externally provided object, if it exists, else try rules
	 (external-proc tsubst '())
	 (let comp-aux ((l inst-comprules)) ;search first matching rule
	   (if
	    (null? l) ;reproduce
	    repro-obj
	    (let* ((inst-rule (car l))
		   (lhs (rule-to-lhs inst-rule))
		   (rhs (rule-to-rhs inst-rule))
		   (empty-bindings (nbe-make-bindings '() '())))
	      (if (equal? instance (const-to-type
				    (term-in-const-form-to-const lhs)))
		  (nbe-term-to-object rhs empty-bindings)
		  (comp-aux (cdr l)))))))
	repro-obj))
     (nbe-make-object
      inst-type
      (nbe-curry
       (lambda objs ;arity many
	 (or ;return externally provided object, if it exists, else try rules
	  (external-proc tsubst objs)
	  (let comp-aux ((l1 inst-comprules)) ;search first matching comprule
	    (if
	     (null? l1) ;search for first matching rewrite rule
	     (let* ((reified-objs (map nbe-reify objs))
		    (extracted-terms
		     (map term-to-eta-nf (map nbe-extract reified-objs))))
	       (let rew-aux ((l2 inst-rewrules))
		 (if
		  (null? l2) ;reproduce
		  (let* ((obj (nbe-reflect (nbe-make-termfam
					    inst-type
					    (lambda (k)
					      (make-term-in-const-form
					       inst-pconst)))))
			 (val (nbe-object-to-value obj)))
		    (apply (nbe-uncurry val arity) objs))
		  (let* ((rewrule (car l2))
			 (lhs (rule-to-lhs rewrule))
			 (args (term-in-app-form-to-args lhs))
			 (subst (match-list args extracted-terms)))
		    (if
		     subst
		     (let* ((rhs (rule-to-rhs rewrule))
			    (vars (map car subst))
			    (terms (map cadr subst))
			    (objs (map (lambda (x)
					 (nbe-term-to-object x empty-subst))
				       terms))
			    (bindings (nbe-make-bindings vars objs)))
		       (nbe-term-to-object rhs bindings))
		     (rew-aux (cdr l2)))))))
	     (let* ((comprule (car l1))
		    (lhs (rule-to-lhs comprule))
		    (constr-patterns (term-in-app-form-to-args lhs)))
	       (if (apply and-op (map nbe-inst? constr-patterns objs))
		   (let* ((rhs (rule-to-rhs comprule))
			  (genargs
			   (apply append
				  (map nbe-genargs constr-patterns objs)))
			  (free (term-to-free lhs))
			  (bindings (nbe-make-bindings free genargs)))
		     (nbe-term-to-object rhs bindings))
		   (comp-aux (cdr l1))))))))
       inst-type
       arity)))))

;; Constants with fixed rules

;; Let rho(alphas) be a type with alphas strictly positive tvars.  For
;; gives argtypes sigmas and valtypes taus Map has type
;; rho(sigmas)=>(sigmas=>taus)=>rho(sigmas)

(define (make-map-const type tvars argtypes valtypes)
  (let* ((val-tvars (map (lambda (x) (new-tvar)) tvars))
	 (uninst-mapop-type
	  (apply mk-arrow
		 type
		 (append (map make-arrow tvars val-tvars)
			 (list (type-substitute
				type (make-substitution tvars val-tvars))))))
	 (tsubst (make-substitution (append tvars val-tvars)
				    (append argtypes valtypes)))
	 (inst-mapop-type (type-substitute uninst-mapop-type tsubst)))
    (type-etc-to-map-const type tvars argtypes valtypes val-tvars
			   uninst-mapop-type tsubst inst-mapop-type)))

(define (type-etc-to-map-const type tvars argtypes valtypes val-tvars
			       uninst-mapop-type tsubst inst-mapop-type)
  (make-const (map-at-intern type tvars argtypes valtypes val-tvars
			     uninst-mapop-type tsubst inst-mapop-type)
	      "Map" 'fixed-rules uninst-mapop-type tsubst t-deg-one 'const))

(define (map-at type tvars argtypes valtypes val-tvars)
  (let* ((uninst-mapop-type
	  (apply mk-arrow
		 type
		 (append (map make-arrow tvars val-tvars)
			 (list (type-substitute
				type (make-substitution tvars val-tvars))))))
	 (tsubst (make-substitution (append tvars val-tvars)
				    (append argtypes valtypes)))
	 (inst-mapop-type (type-substitute uninst-mapop-type tsubst)))
    (map-at-intern type tvars argtypes valtypes val-tvars
		   uninst-mapop-type tsubst inst-mapop-type)))

(define (map-at-intern type tvars argtypes valtypes val-tvars
		       uninst-mapop-type tsubst inst-mapop-type)
  (nbe-make-object
   inst-mapop-type
   (nbe-curry
    (lambda objs
      (let* ((maparg-obj (car objs))
	     (maparg-val (nbe-object-to-value maparg-obj))
	     (fct-objs (cdr objs)))
	(if
	 (null? (intersection (type-to-tvars type) tvars))
	 maparg-obj
	 (case (tag type)
	   ((tvar)
	    (do ((l1 tvars (cdr l1))
		 (l2 fct-objs (cdr l2))
		 (res #f (if (equal? type (car l1))
			     (let ((fct-obj (car l2)))
			       (nbe-object-apply fct-obj maparg-obj))
			     #f)))
		((or res (null? l1))
		 (if res res maparg-obj))))
	   ((alg)
	    (if
	     (not (equal? (alg-form-to-types type) tvars))
	     (let* ;first alg-mapobj
		 ((alg-name (alg-form-to-name type))
		  (param-tvars (alg-name-to-tvars alg-name))
		  (alg-argtypes (alg-form-to-types
				 (arrow-form-to-arg-type inst-mapop-type)))
		  (alg-valtypes (alg-form-to-types
				 (arrow-form-to-final-val-type
				  inst-mapop-type)))
		  (alg-mapobj
		   (map-at (apply make-alg alg-name param-tvars)
			   param-tvars alg-argtypes alg-valtypes
			   (map (lambda (x) (new-tvar)) param-tvars)))
					;next pd-mapobjs
		  (pd-types (alg-form-to-types type))
		  (pd-mapobjs
		   (map (lambda (pd-type)
			  (map-at pd-type tvars argtypes valtypes val-tvars))
			pd-types))
					;next pd-fct-objs
		  (inst-pd-types (alg-form-to-types
				  (arrow-form-to-arg-type inst-mapop-type)))
		  (inst-pd-valtypes (alg-form-to-types
				     (arrow-form-to-final-val-type
				      inst-mapop-type)))
		  (pd-fct-objs
		   (map (lambda (pd-mapobj inst-pd-type inst-pd-valtype)
			  (nbe-make-object
			   (make-arrow inst-pd-type inst-pd-valtype)
			   (lambda (arg)
			     (apply nbe-object-app pd-mapobj arg fct-objs))))
			pd-mapobjs inst-pd-types inst-pd-valtypes)))
	       (apply nbe-object-app alg-mapobj maparg-obj pd-fct-objs))
					;case types=tvars
	     (cond ;reproduction case
	      ((nbe-fam-value? maparg-val)
	       (nbe-reflect
		(nbe-make-termfam
		 (arrow-form-to-final-val-type inst-mapop-type (length objs))
		 (lambda (k)
		   (apply mk-term-in-app-form
			  (make-term-in-const-form ;map-const
			   (type-etc-to-map-const
			    type tvars argtypes valtypes val-tvars
			    uninst-mapop-type tsubst inst-mapop-type))
			  (map (lambda (x) (nbe-fam-apply (nbe-reify x) k))
			       objs))))))
	      ((nbe-constr-value? maparg-val)
	       (let*
		   ((name (nbe-constr-value-to-name maparg-val))
		    (args (nbe-constr-value-to-args maparg-val))
					;new constructor object
		    (alg-name (alg-form-to-name type))
		    (param-tvars (alg-name-to-tvars alg-name))
		    (constr (constr-name-to-constr name))
		    (new-constr
		     (const-substitute
		      constr (make-substitution param-tvars valtypes) #t))
		    (new-constr-obj (const-to-object-or-arity new-constr))
					;function objects for recursive calls
		    (simalg-names (alg-name-to-simalg-names alg-name))
		    (simalgs-with-tvars
		     (map (lambda (simalg-name)
			    (apply make-alg simalg-name tvars))
			  simalg-names))
		    (argalgs (map (lambda (simalg-name)
				    (apply make-alg simalg-name argtypes))
				  simalg-names))
		    (valalgs (map (lambda (simalg-name)
				    (apply make-alg simalg-name valtypes))
				  simalg-names))
		    (abstr-app-mapobjs
		     (map (lambda (simalg-with-tvars argalg valalg)
			    (nbe-make-object
			     (make-arrow argalg valalg)
			     (lambda (obj)
			       (apply nbe-object-app
				      (map-at simalg-with-tvars tvars
					      argtypes valtypes val-tvars)
				      obj
				      fct-objs))))
			  simalgs-with-tvars argalgs valalgs))
					;pd-mapobjs
		    (constr-type (const-to-uninst-type constr))
		    (alg-tvars (map (lambda (x) (new-tvar)) simalg-names))
		    (simalgs (map (lambda (simalg-name)
				    (apply make-alg simalg-name param-tvars))
				  simalg-names))
		    (constr-type-with-alg-tvars
		     (type-gen-substitute constr-type
					  (map list simalgs alg-tvars)))
		    (constr-arg-types-with-alg-tvars
		     (arrow-form-to-arg-types constr-type-with-alg-tvars))
		    (pd-mapobjs
		     (map (lambda (constr-arg-type-with-alg-tvar)
			    (map-at constr-arg-type-with-alg-tvar
				    (append param-tvars alg-tvars)
				    (append argtypes argalgs)
				    (append valtypes valalgs)
				    (map (lambda (x) (new-tvar))
					 (append param-tvars alg-tvars))))
			  constr-arg-types-with-alg-tvars))
					;finally the pd-objs
		    (pd-objs
		     (map (lambda (pd-mapobj arg)
			    (apply nbe-object-app
				   pd-mapobj arg
				   (append fct-objs abstr-app-mapobjs)))
			  pd-mapobjs args)))
		 (apply nbe-object-app new-constr-obj pd-objs)))
	      (else (myerror "map-at-intern" "value expected" maparg-val)))))
	   ((arrow)
	    (let* ;first pd-mapobj
		((pd-type (arrow-form-to-val-type type))
		 (pd-mapobj (map-at pd-type tvars argtypes valtypes val-tvars))
		 (inst-arg-type (arrow-form-to-arg-type
				 (arrow-form-to-arg-type inst-mapop-type)))
		 (inst-pd-valtype (arrow-form-to-final-val-type
				   inst-mapop-type (+ 2 (length tvars)))))
	      (nbe-make-object
	       (make-arrow inst-arg-type inst-pd-valtype)
	       (lambda (arg-obj)
		 (apply nbe-object-app
			pd-mapobj
			(nbe-object-apply maparg-obj arg-obj)
			fct-objs)))))
	   ((star)
	    (let* ;first left-mapobj and right-mapobj
		((uninst-left-type (star-form-to-left-type type))
		 (inst-left-valtype
		  (star-form-to-left-type
		   (arrow-form-to-arg-type inst-mapop-type)))
		 (left-mapobj
		  (map-at uninst-left-type tvars argtypes valtypes val-tvars))
		 (uninst-right-type (star-form-to-right-type type))
		 (inst-right-valtype
		  (star-form-to-right-type
		   (arrow-form-to-arg-type inst-mapop-type)))
		 (right-mapobj
		  (map-at uninst-right-type tvars argtypes valtypes val-tvars)))
	      (nbe-make-object
	       (make-star inst-left-valtype inst-right-valtype)
	       (nbe-mk-prod-obj
		(apply nbe-object-app
		       left-mapobj (nbe-object-car arg-obj) fct-objs)
		(apply nbe-object-app
		       right-mapobj (nbe-object-cdr arg-obj) fct-objs)))))))))
    inst-mapop-type
    (+ 1 (length tvars)))))

;; 2004-12-31.  =-at and e-at moved to boole.scm.  Reason: They need
;; AndConst, which requires the algebra boole.

;; In a recursion on simultaneously defined algebras one may need to
;; recur on some of those algebras only, called relevant.  Then we can
;; simplify the type of the recursion operator accordingly, as
;; described at arrow-types-to-uninst-recop-types-and-tsubst .

;; From the uninstantiated type of a recursion constant we can read off
;; the uninstantiated form of its arrow type iota_j -> tau_j, and also
;; the remaining uninstantiated arrow types, in some order.

(define (rec-const-to-uninst-arrow-types const)
  (let* ((uninst-type (const-to-uninst-type const))
	 (alg-and-step-types (arrow-form-to-arg-types uninst-type))
	 (val-tvar (arrow-form-to-final-val-type uninst-type))
	 (step-types (cdr alg-and-step-types))
	 (alg (car alg-and-step-types))
	 (alg-name (alg-form-to-name alg))
	 (simalg-names (alg-name-to-simalg-names alg-name))
	 (step-arg-types (apply append
				(map arrow-form-to-arg-types step-types)))
	 (alg-names (intersection
		     simalg-names
		     (apply union (map type-to-alg-names step-arg-types))))
	 (alg-types (alg-form-to-types alg))
	 (algs (map (lambda (name) (apply make-alg name alg-types))
		    alg-names))
	 (val-tvars (intersection
		     (map arrow-form-to-final-val-type step-types)
		     (apply union (map type-to-tvars step-arg-types))))
	 (prelim-arrow-types
	  (if (= (length algs) (length val-tvars))
	      (map make-arrow algs val-tvars)
	      (myerror "rec-const-to-uninst-arrow-types"
		       "alg-names and val-tvars differ in length"
		       alg-names val-tvars)))
	 (init-arrow-type (make-arrow alg val-tvar)))
    (cons init-arrow-type (remove init-arrow-type prelim-arrow-types))))

;; We define a procedure that takes arrow-types and returns the types
;; of the recursion constants, split into uninstantiated types and a
;; type substitution.

;; arrow-types is a list of types alg=>tau, where the left hand sides
;; make up the relevant algebras.  Then we can simplify the type of the
;; recursion operator accordingly, as follows.  (i) Only consider the
;; relevant constructors, i.e., those mapping into relevant algebras.
;; (ii) Shorten their types by omitting all argument types containing
;; irrelevant algebras.  (iii) For every shortened constructor type
;; $(\rho_{\nu}(\vec{\xi}\,))_{\nu < n} \typeTo \xi_j$ form a
;; simplified step type $(\rho_{\nu}(\vec{\iota} \typeProd
;; \vec{\tau}))_{\nu < n} \typeTo \tau_j$ where $\vec{\iota}$ are the
;; relevant algebras and $\vec{\tau}$ the assigned value types.

(define (arrow-types-to-uninst-recop-types-and-tsubst . arrow-types)
  (if
   (null? arrow-types)
   (list '() empty-subst)
   (let* ((rel-algs (map arrow-form-to-arg-type arrow-types))
	  (val-types (map arrow-form-to-val-type arrow-types))
	  (rel-alg-names
	   (map (lambda (alg)
		  (if (alg-form? alg)
		      (alg-form-to-name alg)
		      (myerror "arrow-types-to-uninst-recop-types-and-tsubst"
			       "alg expected" alg)))
		rel-algs))
	  (alg-name (car rel-alg-names))
	  (param-tvars (alg-name-to-tvars alg-name))
	  (types (alg-form-to-types (car rel-algs)))
	  (tsubst1 (make-substitution param-tvars types))
	  (simalg-names-to-alg-tvars-alist
	   (map (lambda (simalg-name) (list simalg-name (new-tvar)))
		(alg-name-to-simalg-names alg-name)))
	  ;; (simalg-names-to-alg-tvars-alist
	  ;;  (alg-name-to-simalg-names-to-alg-tvars-alist alg-name))
	  (rel-alg-tvars
	   (map cadr (list-transform-positive simalg-names-to-alg-tvars-alist
		       (lambda (p) (member (car p) rel-alg-names)))))
	  (tsubst2 (make-substitution rel-alg-tvars val-types))
	  (rel-algs-with-param-tvars
	   (map (lambda (x) (apply make-alg x param-tvars))
		rel-alg-names))
	  (uninst-arrow-types
	   (map make-arrow rel-algs-with-param-tvars rel-alg-tvars))
	  (rel-alg-names-to-rel-alg-tvars-alist
	   (map (lambda (rel-alg-name rel-alg-tvar)
		  (list rel-alg-name rel-alg-tvar))
		rel-alg-names rel-alg-tvars))
	  (simalg-names (alg-name-to-simalg-names alg-name)))
     (if (not (equal? rel-alg-names
		      (remove-duplicates rel-alg-names)))
	 (myerror "arrow-types-to-uninst-recop-types-and-tsubst"
		  "distinct algs expected" rel-alg-names))
     (if (pair? (set-minus rel-alg-names simalg-names))
	 (myerror "arrow-types-to-uninst-recop-types-and-tsubst"
		  "too many alg names"
		  (set-minus rel-alg-names simalg-names)))
     (if
      (< 1 (length (remove-duplicates (map alg-form-to-types rel-algs))))
      (apply myerror "arrow-types-to-uninst-recop-types-and-tsubst"
	     "equal type parameter lists expected" rel-algs))
     (let* ((rel-simalg-names
	     (list-transform-positive simalg-names
	       (lambda (x) (member x rel-alg-names))))
	    (typed-constr-names
	     (apply append (map alg-name-to-typed-constr-names
				rel-simalg-names)))
	    (constr-types (map typed-constr-name-to-type typed-constr-names))
	    (step-types
	     (map (lambda (x)
		    (constructor-type-to-step-type
		     x rel-alg-names-to-rel-alg-tvars-alist))
		  constr-types)))
       (list
	(map (lambda (alg rel-alg-tvar)
	       (apply mk-arrow alg (append step-types (list rel-alg-tvar))))
	     rel-algs-with-param-tvars rel-alg-tvars)
	(append tsubst1 tsubst2))))))

;; constructor-type-to-step-type works for constructor types with or
;; without substitution for its type parameters.  It is assumed that
;; the algebra to which constr-type belongs has a type associated
;; in rel-alg-names-to-types-alist.

(define (constructor-type-to-step-type constr-type rel-alg-names-to-types-alist)
  (let* ((alg-name (alg-form-to-name
		    (arrow-form-to-final-val-type constr-type)))
	 (type (let ((info (assoc alg-name rel-alg-names-to-types-alist)))
		 (if info (cadr info)
		     (myerror "constructor-type-to-step-type"
			      "type missing for alg-name" alg-name))))
	 (argtypes (arrow-form-to-arg-types constr-type))
	 (rel-simalg-names (map car rel-alg-names-to-types-alist))
	 (types (map cadr rel-alg-names-to-types-alist))
	 (simalg-names (alg-name-to-simalg-names alg-name))
	 (irrel-simalg-names (set-minus simalg-names rel-simalg-names))
	 (param-tvars (alg-name-to-tvars alg-name))
	 (rel-simalgs (map (lambda (name) (apply make-alg name param-tvars))
			   rel-simalg-names))
	 (rel-simalgs-times-types
	  (map (lambda (rel-simalg type) (make-alg "yprod" rel-simalg type))
	       rel-simalgs types))
	 (steptype-arg-lists
	  (map
	   (lambda (argtype)
	     (cond ;argtype has irrelevant alg names: no steptype arg
	      ((pair? (intersection (type-to-alg-names argtype)
				    irrel-simalg-names))
	       '())
	      ((and ;unnested argtype: duplication
		(alg-form? (arrow-form-to-final-val-type argtype))
		(member (alg-form-to-name
			 (arrow-form-to-final-val-type argtype))
			rel-simalg-names))
	       (list argtype
		     (apply
		      mk-arrow
		      (append
		       (arrow-form-to-arg-types argtype)
		       (list
			(cadr (assoc (alg-form-to-name
				      (arrow-form-to-final-val-type argtype))
				     rel-alg-names-to-types-alist)))))))
	      (else ;argtype tvar or nested (then substitute alg times type)
	       (list (type-gen-substitute
		      argtype
		      (map list rel-simalgs rel-simalgs-times-types))))))
	   argtypes))
	 (steptype-args (apply append steptype-arg-lists)))
    (apply mk-arrow (append steptype-args (list type)))))

(define (arrow-types-to-rec-const . arrow-types)
  (car (apply arrow-types-to-rec-consts arrow-types)))

(define (arrow-types-to-rec-consts . arrow-types)
  (let* ((uninst-recop-types-and-tsubst
	  (apply arrow-types-to-uninst-recop-types-and-tsubst arrow-types))
	 (uninst-recop-types (car uninst-recop-types-and-tsubst))
	 (tsubst (cadr uninst-recop-types-and-tsubst))
	 (alg-names-with-uninst-recop-types
	  (map (lambda (x y)
		 (list (alg-form-to-name (arrow-form-to-arg-type x)) y))
	       arrow-types uninst-recop-types))
	 (alg-names (map car alg-names-with-uninst-recop-types))
	 (simalg-names (if (pair? alg-names)
			   (alg-name-to-simalg-names (car alg-names))
			   '()))
	 (rel-simalg-names (list-transform-positive simalg-names
			     (lambda (x) (member x alg-names))))
	 (rel-typed-constr-names ;the relevant ones only
	  (apply append (map alg-name-to-typed-constr-names rel-simalg-names)))
	 (rel-constr-names (map typed-constr-name-to-name
				rel-typed-constr-names)))
    (map (lambda (x)
	   (let* ((uninst-recop-type
		   (cadr (assoc x alg-names-with-uninst-recop-types)))
		  (inst-recop-type (type-substitute uninst-recop-type tsubst)))
	     (alg-name-etc-to-rec-const
	      x uninst-recop-type tsubst inst-recop-type 0 rel-constr-names
	      alg-names-with-uninst-recop-types)))
	 alg-names)))

;; For backwards compatibility we keep

(define type-info-to-rec-consts arrow-types-to-rec-consts)

(define (type-info-to-rec-const . arrow-types)
  (car (apply arrow-types-to-rec-consts arrow-types)))

;; alg-name-etc-to-rec-const computes the required object, via rec-at.
;; Both are defined general enough to be usable for
;; all-formulas-to-rec-const as well, hence need to accommodate the f
;; free variables in the induction formulas.  We have to consider the
;; free variables in the scheme formulas, and let the type of the
;; rec-const depend on them.  This is necessary to have the
;; all-conversion be adequately represented in term normalization.

;; The arguments for rec-at are all those needed in the construction of
;; the object (for nbe), i.e. alg-name, tsubst, f, constr-names,
;; alg-names-with-uninst-recop-types and arrow-types-or-all-formulas.  In
;; the reproduction case the required term is formed using
;; alg-name-etc-to-rec-const, which takes the same arguments.  In this
;; setup these arguments need only be computed once, not repeatedly in
;; the loop where alg-name-etc-to-rec-const and rec-at call themselves.

;; repro-data are carried along, to allow construction of the original
;; induction or elimination scheme, in the reproduction case of proof
;; normalization.  They are either all-formulas or imp-formulas.

(define (alg-name-etc-to-rec-const
	 alg-name uninst-recop-type tsubst inst-recop-type
	 f rel-constr-names rel-simalg-names-with-uninst-recop-types .
	 repro-data)
  (apply make-const
	 (apply rec-at alg-name uninst-recop-type tsubst inst-recop-type f
		rel-constr-names rel-simalg-names-with-uninst-recop-types
		repro-data)
	 "Rec" 'fixed-rules uninst-recop-type tsubst 1 'const
	 repro-data))

;; While normalizing, the unfolding mechanism of the rec-operator
;; may be blocked by setting REC-UNFOLDING-FLAG to #f.

(define REC-UNFOLDING-FLAG #t)

(define (rec-at alg-name uninst-recop-type tsubst inst-recop-type
		f rel-constr-names rel-simalg-names-with-uninst-recop-types .
		repro-data)
  (let* ((f-plus-s ;number f of free variables plus number s of step types
	  (- (length (arrow-form-to-arg-types uninst-recop-type)) 1))
	 (s (- f-plus-s f))
	 (arity (+ f-plus-s 1))
	 (nbe-for-idps? (and (pair? repro-data)
			     (imp-form? (car repro-data)))))
    (nbe-make-object
     inst-recop-type
     (nbe-curry
      (lambda objs
	(let* ((rec-obj (list-ref objs f))
	       (rec-val (nbe-object-to-value rec-obj)))
	  (cond ;reproduction case
	   ((or (nbe-fam-value? rec-val) (not REC-UNFOLDING-FLAG))
	    (nbe-reflect
	     (nbe-make-termfam
	      (arrow-form-to-final-val-type inst-recop-type (length objs))
	      (lambda (k)
		(apply mk-term-in-app-form
		       (make-term-in-const-form ;rec-const
			(apply alg-name-etc-to-rec-const
			       alg-name uninst-recop-type tsubst
			       inst-recop-type f rel-constr-names
			       rel-simalg-names-with-uninst-recop-types
			       repro-data))
		       (map (lambda (x) (nbe-fam-apply (nbe-reify x) k))
			    objs))))))
	   ((and (nbe-constr-value? rec-val) (not nbe-for-idps?))
	    (let*
		((constr-name (nbe-constr-value-to-name rec-val))
		 (args (nbe-constr-value-to-args rec-val))
		 (free-objs (list-head objs f))
		 (step-objs (list-head (list-tail objs (+ f 1)) s))
		 (step-obj (do ((cs rel-constr-names (cdr cs))
				(objs step-objs (cdr objs))
				(res #f (if (string=? (car cs) constr-name)
					    (car objs)
					    res)))
			       ((null? cs) res)))
		 (rel-simalg-names
		  (map car rel-simalg-names-with-uninst-recop-types))
		 (uninst-recop-types
		  (map cadr rel-simalg-names-with-uninst-recop-types))
		 (inst-recop-types
		  (map (lambda (uninst-recop-type)
			 (type-substitute uninst-recop-type tsubst))
		       uninst-recop-types))
		 (algs (map arrow-form-to-arg-type inst-recop-types))
		 (valtypes (map arrow-form-to-final-val-type inst-recop-types))
		 (val-tvars
		  (map arrow-form-to-final-val-type uninst-recop-types))
		 (recobjs
		  (map (lambda (aname utype itype)
			 (apply rec-at
				aname utype tsubst itype f rel-constr-names
				rel-simalg-names-with-uninst-recop-types
				repro-data))
		       rel-simalg-names uninst-recop-types inst-recop-types))
		 (rel-simalg-names-to-recobjs-alist
		  (map list rel-simalg-names recobjs))
		 (val-tvars-to-recobjs-alist (map list val-tvars recobjs))
		 (constr (constr-name-to-constr constr-name))
		 (constr-type (const-to-uninst-type constr))
		 (constr-arg-types (arrow-form-to-arg-types constr-type))
		 (simalg-names (alg-name-to-simalg-names alg-name))
		 (irrel-simalg-names (set-minus simalg-names rel-simalg-names))
		 (rel-args
		  (do ((l1 args (cdr l1))
		       (l2 constr-arg-types (cdr l2))
		       (res
			'()
			(if (null? (intersection (type-to-alg-names (car l2))
						 irrel-simalg-names))
			    (cons (car l1) res)
			    res)))
		      ((null? l1) (reverse res))))
		 (rel-constr-arg-types (map nbe-object-to-type rel-args))
		 (step-arg-lists
		  (map
		   (lambda (rel-arg rel-constr-arg-type)
		     (cond
		      (;param-arg-type: take original arg
		       (null?
			(intersection (type-to-alg-names rel-constr-arg-type)
				      rel-simalg-names))
		       (list rel-arg))
		      (;unnested recarg-type: take original arg and rec call
					;(duplication)
		       (and (alg-form? (arrow-form-to-final-val-type
					rel-constr-arg-type))
			    (member (alg-form-to-name
				     (arrow-form-to-final-val-type
				      rel-constr-arg-type))
				    rel-simalg-names))
		       (list
			rel-arg
			(nbe-object-rec-compose ;first (recobj free-objs)
			 (apply
			  nbe-object-app
			  (cadr (assoc (alg-form-to-name
					(arrow-form-to-final-val-type
					 rel-constr-arg-type))
				       rel-simalg-names-to-recobjs-alist))
			  free-objs)
			 step-objs
			 rel-arg)))
		      (else ;nested recarg-type: use mapop
		       (let*
			   ((new-tvars (map (lambda(x) (new-tvar))
					    rel-simalg-names))
			    (param-tvars (alg-name-to-tvars alg-name))
			    (rel-simalgs-with-param-tvars
			     (map (lambda (rel-simalg-name)
				    (apply make-alg rel-simalg-name
					   param-tvars))
				  rel-simalg-names))
			    (rel-constr-arg-type-with-tvars
			     (type-gen-substitute
			      rel-constr-arg-type
			      (map list
				   rel-simalgs-with-param-tvars new-tvars)))
			    (rel-simalgs (map (lambda (x)
						(type-substitute x tsubst))
					      rel-simalgs-with-param-tvars))
			    (rel-simalgs-times-valtypes
			     (map (lambda (rel-simalg valtype)
				    (make-alg "yprod" rel-simalg valtype))
				  rel-simalgs valtypes))
			    (ih-fctobjs
			     (map
			      (lambda (alg valtype val-tvar)
				(let*
				    ((pairconstr
				      (const-substitute
				       (constr-name-to-constr "PairConstr")
				       (make-substitution
					(alg-name-to-tvars "yprod")
					(list alg valtype))
				       #f))
				     (pairconstrobj
				      (const-to-object-or-arity pairconstr))
				     (recobj
				      (cadr
				       (assoc val-tvar
					      val-tvars-to-recobjs-alist))))
				  (nbe-make-object
				   (make-arrow
				    alg (make-alg "yprod" alg valtype))
				   (lambda (arg)
				     (nbe-object-app
				      pairconstrobj
				      arg (apply nbe-object-app
						 recobj arg step-objs))))))
			      algs valtypes val-tvars))
			    (new-val-tvars
			     (map (lambda (x) (new-tvar)) new-tvars))
			    (mapobj
			     (map-at
			      rel-constr-arg-type-with-tvars new-tvars
			      rel-simalgs rel-simalgs-times-valtypes
			      new-val-tvars)))
			 (list
			  (apply nbe-object-app mapobj rel-arg ih-fctobjs))))))
		   rel-args rel-constr-arg-types))
		 (step-args (apply append step-arg-lists)))
	      (apply nbe-object-app step-obj step-args)))
	   ((and (nbe-constr-value? rec-val) nbe-for-idps?)
					;to be extended to nested idpcs
	    (let*
		((name (nbe-constr-value-to-name rec-val))
		 (i (if (and (pair? name) (string=? "Intro" (car name))
			     (pair? (cdr name)))
			(cadr name)
			(myerror "rec-at" "name expected" name)))
		 (idpc (if (pair? (cddr name))
			   (caddr name)
			   (myerror "rec-at" "name expected" name)))
		 (idpc-name (idpredconst-to-name idpc))
		 (number-string (number-to-alphabetic-string i))
		 (name-string (string-append number-string idpc-name))
		 (args (nbe-constr-value-to-args rec-val))
		 (idpc-params (idpredconst-to-free idpc))
		 (args-wo-idpc-params (list-tail args (length idpc-params)))
		 (free-objs (list-head objs f))
		 (step-objs (list-head (list-tail objs (+ f 1)) s))
		 (step-obj (do ((cs rel-constr-names (cdr cs))
				(objs step-objs (cdr objs))
				(res #f (if (string=? (car cs) name-string)
					    (car objs)
					    res)))
			       ((null? cs) res)))
		 (aconst (number-and-idpredconst-to-intro-aconst i idpc))
		 (vars-and-prems
		  (imp-impnc-all-allnc-form-to-vars-and-premises
		   (aconst-to-formula aconst)))
		 (preceding-args-list
		  (map (lambda (l) (list-head l (- (length l) 1)))
		       (nonnil-init-segments args)))
		 (idpc-pvar (idpredconst-name-to-pvar idpc-name))
		 (idpc-args-length
		  (length (arity-to-types (predicate-to-arity idpc-pvar))))
		 (idpc-param-objs (list-head args (length idpc-params)))
		 (compet-param-objs
		  (list-tail free-objs (+ idpc-args-length
					  (length idpc-params))))
		 (simidpc-names (idpredconst-name-to-simidpc-names idpc-name))
		 (step-arg-lists ;of length 1 or 2
		  (map
		   (lambda (arg preceding-args var-or-prem)
		     (cond
		      (;param-arg-type: take original arg
		       (or (var-form? var-or-prem)
			   (null?
			    (intersection
			     (formula-to-idpredconst-names var-or-prem)
			     simidpc-names)))
		       (list arg))
		      (;unnested recarg-type: take original arg	and rec. call
					;(duplication)
		       (and (predicate-form? var-or-prem)
			    (let ((pred (predicate-form-to-predicate
					 var-or-prem)))
			      (and (idpredconst-form? pred)
				   (member (idpredconst-to-name pred)
					   simidpc-names))))
		       (list
			arg ;now the rec call
			(let*
			    ((argtype (nbe-object-to-type arg))
			     (argvaltype
			      (arrow-form-to-final-val-type argtype))
			     (pd-alg-name (alg-form-to-name argvaltype))
			     (pd-uninst-recop-type
			      (cadr (assoc
				     pd-alg-name
				     rel-simalg-names-with-uninst-recop-types)))
			     (pd-inst-recop-type
			      (type-substitute pd-uninst-recop-type tsubst))
			     (arg-args (list-tail preceding-args
						  (- (length preceding-args)
						     idpc-args-length)))
			     (pd-free-objs (append arg-args
						   idpc-param-objs
						   compet-param-objs))
			     (pd-f (length pd-free-objs)))
			  (apply
			   nbe-object-app
			   (apply
			    rec-at
			    pd-alg-name pd-uninst-recop-type
			    tsubst pd-inst-recop-type pd-f
			    rel-constr-names
			    rel-simalg-names-with-uninst-recop-types
			    repro-data)
			   (append pd-free-objs (cons arg step-objs))))))
		      (else ;nested case
		       (myerror "rec-at"
				"not implemented for nested idpredconsts"))))
		   args preceding-args-list vars-and-prems))
		 (step-args (list-tail (apply append step-arg-lists)
				       (length idpc-params))))
	      (apply nbe-object-app step-obj step-args)))
	   (else (myerror "rec-at" "value expected" rec-val)))))
      inst-recop-type
      arity))))

;; We assume that recobj-at-free-objs has no free parameters (needed
;; to calculate the correct type).  Note that recobj-at-free-objs can
;; be of an arrow type, since it comes from an intro aconst depending
;; on the free parameters as well.

(define (nbe-object-rec-compose recobj-at-free-objs stepobjs obj)
  (let* ((k (length stepobjs))
         (rectype (nbe-object-to-type recobj-at-free-objs))
         (objtype (nbe-object-to-type obj))
         (valtype (arrow-form-to-final-val-type rectype (+ k 1)))
         (argtypes (arrow-form-to-arg-types objtype)) ;objtype?
         (l (length argtypes))
         (type (apply mk-arrow (append argtypes (list valtype)))))
    (if (zero? l)
        (apply nbe-object-app recobj-at-free-objs obj stepobjs)
        (nbe-make-object
         type
         (nbe-curry
          (lambda arg-objs
            (apply nbe-object-app
		   recobj-at-free-objs
		   (apply (nbe-uncurry (nbe-object-to-value obj) l) arg-objs)
		   stepobjs))
	  type
          l)))))

;; Similarly to arrow-types-to-rec-const we now define
;; all-formulas-to-rec-const , again using alg-name-etc-to-rec-const .
;; all-formulas-to-rec-const will be used in proof.scm to achieve
;; normalization of proofs via translating them in terms, to translate
;; an ind-aconst.

(define (all-formulas-to-rec-const . all-formulas)
  (if (nested-alg-name?
       (alg-form-to-name (var-to-type (all-form-to-var (car all-formulas)))))
      (myerror "all-formulas-to-rec-const"
	       "all-formula for an unnested algebra expected"
	       (car all-formulas)
	       "unfold all-formula and use imp-formulas-to-rec-const"))
  (let* ((uninst-imp-formulas-and-tpsubst
	  (apply all-formulas-to-uninst-imp-formulas-and-tpsubst all-formulas))
	 (uninst-imp-formulas (car uninst-imp-formulas-and-tpsubst))
	 (tpsubst (cadr uninst-imp-formulas-and-tpsubst))
	 (tsubst (list-transform-positive tpsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (psubst (list-transform-positive tpsubst
		   (lambda (x) (pvar-form? (car x)))))
	 (pvars (map car psubst))
	 (cterms (map cadr psubst))
	 (new-tvars (map PVAR-TO-TVAR pvars))
	 (nbe-types (map (lambda (x)
			   (nbe-formula-to-type (cterm-to-formula x)))
			 cterms))
	 (new-tsubst (make-substitution new-tvars nbe-types))
	 (free (formula-to-free (apply mk-and all-formulas)))
	 (free-types (map var-to-type free))
	 (uninst-recop-types
	  (map (lambda (x) ;uninst-imp-formula
		 (apply mk-arrow (append free-types
					 (list (nbe-formula-to-type x)))))
	       uninst-imp-formulas))
	 (vars (map all-form-to-var all-formulas))
	 (types (map var-to-type vars))
	 (alg-names
	  (map (lambda (type)
		 (if (alg-form? type)
		     (alg-form-to-name type)
		     (myerror
		      "all-formulas-to-rec-const" "alg expected" type)))
	       types))
	 (alg-names-with-uninst-recop-types
	  (map list alg-names uninst-recop-types))
	 (simalg-names (alg-name-to-simalg-names (car alg-names)))
	 (sorted-alg-names (list-transform-positive simalg-names
			     (lambda (x) (member x alg-names))))
	 (typed-constr-names
	  (apply append
		 (map alg-name-to-typed-constr-names sorted-alg-names)))
	 (constr-names (map typed-constr-name-to-name typed-constr-names))
	 (alg-name (car alg-names))
	 (uninst-recop-type
	  (cadr (assoc alg-name alg-names-with-uninst-recop-types)))
	 (inst-recop-type (type-substitute uninst-recop-type
					   (append tsubst new-tsubst))))
    (apply alg-name-etc-to-rec-const
	   (append (list alg-name uninst-recop-type (append tsubst new-tsubst)
			 inst-recop-type (length free) constr-names
			 alg-names-with-uninst-recop-types)
		   all-formulas))))

;; Cases is similar to recursion/induction, but somewhat simpler: there
;; are no recursive calls, and only one all-formula is involved.

;; We begin by defining arrow-type-to-cases-const, which uses
;;    arrow-type-to-uninst-casesop-type-and-tsubst
;;    alg-name-etc-to-cases-const
;;    cases-at
;; The simplification compared to recursion/induction lies in the fact
;; that alg-name-etc-to-cases-const calls cases-at, but not conversely.

(define (arrow-type-to-uninst-casesop-type-and-tsubst arrow-type)
  (let* ((arg-type (arrow-form-to-arg-type arrow-type))
	 (val-type (arrow-form-to-val-type arrow-type))
	 (alg-name
	  (if (alg-form? arg-type)
	      (alg-form-to-name arg-type)
	      (myerror "arrow-type-to-uninst-casesop-type-and-tsubst"
		       "alg expected" arg-type)))
	 (alg-tvars (alg-name-to-tvars alg-name))
	 (tparams (alg-form-to-types arg-type))
	 (tsubst1 (make-substitution alg-tvars tparams))
	 (tsubst2 (list (list (new-tvar) val-type)))
	 (new-val-tvar ;new tvar, to be substituted by val-type
	  (caar tsubst2))
         (uninst-arg-type (apply make-alg alg-name alg-tvars))
	 (typed-constr-names ;only those for the present alg-name
	  (alg-name-to-typed-constr-names alg-name))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (uninst-step-types
	  (map (lambda (x)
		 (apply mk-arrow (append (arrow-form-to-arg-types x)
					 (list new-val-tvar))))
	       constr-types)))
    (list (apply mk-arrow
		 uninst-arg-type
		 (append uninst-step-types (list new-val-tvar)))
	  (append tsubst1 tsubst2))))

(define (constructor-type-to-cases-step-type type alg-names-with-arrow-types)
  (let* ((alg-name (alg-form-to-name (arrow-form-to-final-val-type type)))
	 (arrow-type (cadr (assoc alg-name alg-names-with-arrow-types)))
	 (valtype (arrow-form-to-val-type arrow-type))
	 (argtypes (arrow-form-to-arg-types type)))
    (apply mk-arrow (append argtypes (list valtype)))))

(define (arrow-type-to-cases-const arrow-type)
  (let* ((uninst-casesop-type-and-tsubst
	  (arrow-type-to-uninst-casesop-type-and-tsubst arrow-type))
	 (uninst-casesop-type (car uninst-casesop-type-and-tsubst))
	 (tsubst (cadr uninst-casesop-type-and-tsubst))
	 (alg-name (alg-form-to-name (arrow-form-to-arg-type arrow-type)))
	 (typed-constr-names ;only those for the present alg-name
	  (alg-name-to-typed-constr-names alg-name))
	 (constr-names (map typed-constr-name-to-name typed-constr-names)))
    (alg-name-etc-to-cases-const
     alg-name tsubst 0 constr-names uninst-casesop-type)))

;; alg-name-etc-to-cases-const computes the required object, via
;; cases-at.  Both are defined general enough to be usable for
;; all-formula-to-cases-const as well, hence need to accommodate the f
;; free variables in all-formula.  We have to consider the free variables
;; in all-formula, and let the type of the cases-const depend on them.
;; This is necessary to have the all-conversion be adequately represented
;; in term normalization.

;; The arguments for cases-at are all those needed in the construction of
;; the object (for nbe), i.e. alg-name, tsubst, f, constr-names,
;; uninst-casesop-type and type-info-or-all-formula.  In the reproduction
;; case the required term is formed using alg-name-etc-to-cases-const,
;; which takes the same arguments.

;; The all-formula is carried along, to allow construction of the
;; original cases scheme, in the reproduction case of normalization.

(define (alg-name-etc-to-cases-const
	 alg-name tsubst f constr-names uninst-casesop-type .
	 opt-all-formula)
  (apply
   make-const
   (append (list (apply cases-at (append (list alg-name tsubst f constr-names
					       uninst-casesop-type)
					 opt-all-formula))
		 "Cases" 'fixed-rules uninst-casesop-type tsubst 1 'const)
	   opt-all-formula)))

(define (cases-at alg-name tsubst f constr-names uninst-casesop-type .
		  opt-all-formula)
  (let* ((f-plus-s ;number f of free variables plus number s of step types
	  (- (length (arrow-form-to-arg-types uninst-casesop-type)) 1))
	 (s (- f-plus-s f))
	 (arity (+ f-plus-s 1))
	 (inst-casesop-type (type-substitute uninst-casesop-type tsubst)))
    (nbe-make-object
     inst-casesop-type
     (nbe-curry
      (lambda objs
	(let* ((free-objs (list-head objs f))
	       (step-objs (list-head (list-tail objs (+ f 1)) s))
	       (cases-obj (list-ref objs f))
	       (cases-val (nbe-object-to-value cases-obj)))
	  (cond
	   ((nbe-fam-value? cases-val) ;reproduce
	    (let* ((obj (nbe-reflect
			 (nbe-make-termfam
			  inst-casesop-type
			  (lambda (k)
			    (make-term-in-const-form
			     (apply alg-name-etc-to-cases-const
				    (append
				     (list alg-name tsubst f constr-names
					   uninst-casesop-type)
				     opt-all-formula)))))))
		   (val (nbe-object-to-value obj)))
	      (apply (nbe-uncurry val arity) objs)))
	   ((nbe-constr-value? cases-val)
	    (let* ((name (nbe-constr-value-to-name cases-val))
		   (args (nbe-constr-value-to-args cases-val))
		   (step-obj (do ((cs constr-names (cdr cs))
				  (objs step-objs (cdr objs))
				  (res #f (if (string=? (car cs) name)
					      (car objs)
					      res)))
				 ((null? cs) res))))
	      (apply nbe-object-app (cons step-obj args))))
	   (else (myerror "cases-at" "value expected" cases-val)))))
      inst-casesop-type
      arity))))

;; Similarly to arrow-type-to-cases-const we now define
;; all-formula-to-cases-const, again using
;; alg-name-etc-to-cases-const.  all-formula-to-cases-const
;; will be used in proof.scm to achieve normalization of proofs via
;; translating them in terms, to translate a cases-aconst.

(define (all-formula-to-cases-const all-formula)
  (if (nested-alg-name?
       (alg-form-to-name (var-to-type (all-form-to-var all-formula))))
      (myerror "all-formula-to-cases-const"
	       "all-formula for an unnested algebra expected"
	       all-formula
	       "unfold all-formula"))
  (let* ((uninst-imp-formula-and-tpsubst
	  (all-formula-to-uninst-cases-imp-formula-and-tpsubst all-formula))
	 (uninst-imp-formula (car uninst-imp-formula-and-tpsubst))
	 (tpsubst (cadr uninst-imp-formula-and-tpsubst))
	 (tsubst (list-transform-positive tpsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (psubst (list-transform-positive tpsubst
		   (lambda (x) (pvar-form? (car x)))))
	 (pvars (map car psubst))
	 (cterms (map cadr psubst))
	 (new-tvars (map PVAR-TO-TVAR pvars))
	 (nbe-types (map (lambda (x)
			   (nbe-formula-to-type (cterm-to-formula x)))
			 cterms))
	 (new-tsubst (make-substitution new-tvars nbe-types))
	 (free (formula-to-free all-formula))
	 (free-types (map var-to-type free))
	 (uninst-casesop-type
	  (apply mk-arrow
		 (append free-types
			 (list (nbe-formula-to-type uninst-imp-formula)))))
	 (var (all-form-to-var all-formula))
	 (type (var-to-type var))
	 (alg-name (if (alg-form? type)
		       (alg-form-to-name type)
		       (myerror
			"all-formula-to-cases-const" "alg expected" type)))
	 (typed-constr-names (alg-name-to-typed-constr-names alg-name))
	 (constr-names (map typed-constr-name-to-name typed-constr-names)))
    (alg-name-etc-to-cases-const
     alg-name (append tsubst new-tsubst) (length free) constr-names
     uninst-casesop-type all-formula)))

(define (imp-formulas-to-rec-const . imp-formulas)
  (let* ((unfolded-imp-formulas (map unfold-totality imp-formulas))
	 (prelim-uninst-elim-formulas-etc
	  (apply imp-formulas-to-uninst-elim-formulas-etc
		 unfolded-imp-formulas))
	 (prelim-uninst-elim-formulas (car prelim-uninst-elim-formulas-etc))
	 (prelim-tsubst (cadr prelim-uninst-elim-formulas-etc))
	 (psubst-for-param-pvars (caddr prelim-uninst-elim-formulas-etc))
	 (psubst-for-pvars (cadddr prelim-uninst-elim-formulas-etc))
	 (prelim-tpsubst (apply append (cdr prelim-uninst-elim-formulas-etc)))
	 (prelim-elim-aconsts
	  (map (lambda (uninst-elim-fla)
		 (apply make-aconst
			"Elim" 'axiom uninst-elim-fla prelim-tpsubst
			unfolded-imp-formulas))
	       prelim-uninst-elim-formulas))
	 (tvar-clash?
	  (pair? (intersection
		  (apply union
			 (map type-to-tvars
			      (map var-to-type
				   (apply union
					  (map formula-to-free
					       (map aconst-to-inst-formula
						    prelim-elim-aconsts))))))
		  (map car prelim-tsubst))))
	 (elim-aconsts
	  (if tvar-clash?
	      (map (lambda (prelim-elim-aconst)
		     (aconst-rename prelim-elim-aconst (map car prelim-tsubst)))
		   prelim-elim-aconsts)
	      prelim-elim-aconsts))
	 (free (formula-to-free (aconst-to-inst-formula (car elim-aconsts))))
	 (free-types (map var-to-type free))
	 (uninst-recop-types
	  (map (lambda (x) ;x uninst-elim-formula
		 (apply mk-arrow (append free-types
					 (list (nbe-formula-to-type x)))))
	       (map aconst-to-uninst-formula elim-aconsts)))
	 (prems (map (lambda (x)
		       (if (imp-form? x) (imp-form-to-premise x)
			   (myerror "imp-formulas-to-rec-const"
				    "imp form expected" x)))
		     unfolded-imp-formulas))
	 (idpcs
	  (map (lambda (prem)
		 (if (and
		      (predicate-form? prem)
		      (idpredconst-form? (predicate-form-to-predicate prem)))
		     (predicate-form-to-predicate prem)
		     (myerror "imp-formulas-to-rec-const"
			      "idpredconst expected" prem)))
	       prems))
	 (idpc-names (map idpredconst-to-name idpcs))
	 (alg-names (map idpredconst-name-to-nbe-alg-name idpc-names))
	 (alg-names-with-uninst-recop-types
	  (map list alg-names uninst-recop-types))
	 (simalg-names (alg-name-to-simalg-names (car alg-names)))
	 (sorted-alg-names (list-transform-positive simalg-names
			     (lambda (x) (member x alg-names))))
	 (typed-constr-names
	  (apply append
		 (map alg-name-to-typed-constr-names sorted-alg-names)))
	 (constr-names (map typed-constr-name-to-name typed-constr-names))
	 (alg-name (car alg-names))
	 (uninst-recop-type
	  (cadr (assoc alg-name alg-names-with-uninst-recop-types)))
	 (tsubst
	  (map (lambda (x)
		 (if (tvar-form? (car x))
		     x
		     (list (PVAR-TO-TVAR (car x))
			   (nbe-formula-to-type
			    (cterm-to-formula (cadr x))))))
	       (aconst-to-tpsubst (car elim-aconsts))))
	 (inst-recop-type
	  (type-substitute uninst-recop-type tsubst)))
    (apply alg-name-etc-to-rec-const
	   alg-name uninst-recop-type
	   tsubst
	   inst-recop-type (length free) constr-names
	   alg-names-with-uninst-recop-types
	   unfolded-imp-formulas)))

;; General recursion and induction (work of Simon Huber)

;; (GRecGuard rhos tau) :
;; (rhos=>nat)=>rhos=>(rhos=>(rhos=>tau)=>tau)=>boole=>tau
;; GRecGuard mu xs G True -> G xs([ys]GRecGuard mu ys G(mu ys<mu xs))
;; GRecGuard mu xs G False -> Inhab
;; For convenience we add GRec with GRec mu xs G -> GRecGuard mu xs G True

;; (GRecGuard m alphas rhos tau) :
;; alphas=>(rhos=>nat)=>rhos=>(rhos=>(rhos=>atomic=>tau)=>tau)=>
;; boole=>atomic=>tau
;; GRecGuard ts mu xs G True u ->
;; G xs ([ys,atomic]GRecGuard ts mu ys G (mu ys<mu xs) atomic)
;; GRecGuard ts mu xs G False u -> Efq u
;; Note that this variant is only used to normalize proofs.  Here we need
;; that Efq is a constant.

;; Induction
;; GInd : allnc zs all mu,xs(Prog_mu{xs|A(xs)} ->
;;          all boole(atom(boole) -> A(xs))), where
;; Prog_mu{xs|A(xs)} = all xs(all ys(mu ys<mu xs -> A(ys)) -> A(xs))
;; We get the ordinary general induction GInd' by:
;; GInd' ts mu xs M = GInd ts mu xs M True Truth-Axiom

(define (type-etc-to-efq-const f uninst-type inst-type tsubst . repro-formula)
  (apply
   make-const
   (append (list (apply efq-at (append (list f uninst-type inst-type tsubst)
                                       repro-formula))
                 "Efq" 'fixed-rules uninst-type tsubst t-deg-one 'const)
           repro-formula)))

;; formula-to-efq-const will be used in proof.scm to achieve
;; normalization of proofs via translating them in terms, to translate
;; an efq-aconst.  In addition we need the number m of quantifiers used
;; for the axioms.

(define (formula-to-efq-const formula)
  (let* ((efqaconst (global-assumption-name-to-aconst "Efq"))
         (efq-uninst-formula (aconst-to-uninst-formula efqaconst))
         (pvar (predicate-form-to-predicate
                (imp-form-to-conclusion efq-uninst-formula)))
         (tvar (PVAR-TO-TVAR pvar))
         (nbe-type (nbe-formula-to-type formula))
         (tsubst (make-subst tvar nbe-type))
         (free (formula-to-free formula))
         (param-types (map var-to-type free))
         (f (length free))
         (uninst-type (apply mk-arrow
                             (append param-types
                                     (list (make-tconst "atomic") tvar))))
         (inst-type (type-substitute uninst-type tsubst)))
    (type-etc-to-efq-const f uninst-type inst-type tsubst formula)))

(define (efq-at f uninst-type inst-type tsubst . repro-formula)
  (nbe-make-object
   inst-type
   (nbe-curry
    (lambda objs
      (nbe-reflect ;reproduce
       (nbe-make-termfam
        (arrow-form-to-final-val-type inst-type (+ f 1))
        (lambda (k)
          (apply mk-term-in-app-form
                 (make-term-in-const-form
		  (type-etc-to-efq-const f uninst-type inst-type
					 tsubst (car repro-formula)))
                  (map (lambda (x) (nbe-fam-apply (nbe-reify x) k)) objs))))))
    inst-type (+ f 1))))

;; From the uninstantiated type of a grecguard or grec constant we can
;; read off the uninstantiated form of type-info (rho1 ... rhon tau).
;; Recall that the type of (GRecGuard rhos tau) is
;; (rhos=>nat)=>rhos=>(rhos=>(rhos=>tau)=>tau)=>boole=>tau, and the
;; type of (GRec rhos tau) is
;; (rhos=>nat)=>rhos=>(rhos=>(rhos=>tau)=>tau)=>tau.

(define (grecguard-const-to-uninst-type-info const)
  (let* ((uninst-type (const-to-uninst-type const))
	 (alphas (arrow-form-to-arg-types
		  (arrow-form-to-arg-type uninst-type)))
	 (beta (arrow-form-to-final-val-type uninst-type)))
    (append alphas (list beta))))

(define (grec-const-to-uninst-type-info const)
  (let* ((uninst-type (const-to-uninst-type const))
	 (alphas (arrow-form-to-arg-types
		  (arrow-form-to-arg-type uninst-type)))
	 (beta (arrow-form-to-final-val-type uninst-type)))
    (append alphas (list beta))))

;; Let rhos be the argument types of a measure function mu of type
;; rhos=>tau, and tau be the value type of the general recursion.  From
;; (rho1 ... rhon tau) we generate uninst-grecguardop-type and tsubst.

(define (type-info-to-uninst-grecguardop-type-and-tsubst type-info)
  (let* ((m (- (length type-info) 1))
	 (mu-arg-types (list-head type-info m))
	 (val-type (car (last-pair type-info)))
	 (tsubst (map (lambda (y) (list (new-tvar) y)) type-info))
	 (tvars (map car tsubst)) ;new tvars for type-info
	 (mu-arg-tvars (list-head tvars m))
	 (val-tvar (car (last-pair tvars)))
	 (mu-type
	  (apply mk-arrow (append mu-arg-tvars (list (make-alg "nat")))))
	 (uninst-grecguard-step-type
	  (apply mk-arrow
		 (append mu-arg-tvars
			 (list (apply mk-arrow
				      (append mu-arg-tvars (list val-tvar)))
			       val-tvar))))
	 (uninst-grecguardop-type
	  (apply mk-arrow mu-type (append
				   mu-arg-tvars
				   (list uninst-grecguard-step-type
					 (make-alg "boole")
					 val-tvar)))))
    (list uninst-grecguardop-type tsubst)))

(define (type-info-to-uninst-grecop-type-and-tsubst type-info)
  (let* ((m (- (length type-info) 1))
	 (mu-arg-types (list-head type-info m))
	 (val-type (car (last-pair type-info)))
	 (tsubst (map (lambda (y) (list (new-tvar) y)) type-info))
	 (tvars (map car tsubst)) ;new tvars for type-info
	 (mu-arg-tvars (list-head tvars m))
	 (val-tvar (car (last-pair tvars)))
	 (mu-type
	  (apply mk-arrow (append mu-arg-tvars (list (make-alg "nat")))))
	 (uninst-grec-step-type
	  (apply mk-arrow
		 (append mu-arg-tvars
			 (list (apply mk-arrow
				      (append mu-arg-tvars (list val-tvar)))
			       val-tvar))))
	 (uninst-grecop-type
	  (apply mk-arrow mu-type (append
				   mu-arg-tvars
				   (list uninst-grec-step-type val-tvar)))))
    (list uninst-grecop-type tsubst)))

(define (type-info-to-grecguard-const type-info)
  (let* ((uninst-grecguardop-type-and-tsubst
	  (type-info-to-uninst-grecguardop-type-and-tsubst type-info))
	 (uninst-grecguardop-type (car uninst-grecguardop-type-and-tsubst))
	 (tsubst (cadr uninst-grecguardop-type-and-tsubst))
	 (inst-grecguardop-type
	  (type-substitute uninst-grecguardop-type tsubst))
	 (m (- (length type-info) 1)))
    (uninst-grecguardop-type-etc-to-grecguard-const
     uninst-grecguardop-type tsubst inst-grecguardop-type 0 m)))

;; uninst-grecguardop-type-etc-to-grecguard-const computes the required
;; object, via grecguard-at.  Both are defined general enough to be
;; usable for all-formula-and-number-to-grecguard-const as well, hence
;; need to accommodate the f free variables in the induction formula.
;; We have to consider the free variables in the scheme formula, and
;; let the type of the grecguard-const depend on them.  This is
;; necessary to have all-conversion be adequately represented in term
;; normalization.

;; The arguments for grecguard-at are all those needed in the
;; construction of the object (for nbe), i.e., uninst-grecguardop-type,
;; tsubst, inst-grecguardop-type, f, m and type-info-or-all-formula.
;; In the reproduction case the required term is formed using
;; uninst-grecguardop-type-etc-to-grecguard-const, which takes the same
;; arguments.  In this setup these arguments need only be computed
;; once, not repeatedly in the loop where
;; uninst-grecguardop-type-etc-to-grecguard-const and grecguard-at call
;; themselves.

;; opt-all-formula is carried along, to allow construction of the
;; original grecguard constant or induction scheme, in the reproduction
;; case of normalization.  To have in the term (or proof) something
;; close to what was given to the parser (or in the interactive proof),
;; we take opt-all-formula.

(define (uninst-grecguardop-type-etc-to-grecguard-const
	 uninst-grecguardop-type tsubst inst-grecguardop-type f m .
	 opt-all-formula)
  (apply
   make-const
   (apply grecguard-at
	  uninst-grecguardop-type tsubst inst-grecguardop-type f m
	  opt-all-formula)
   "GRecGuard" 'fixed-rules uninst-grecguardop-type tsubst t-deg-one 'const
   opt-all-formula))

;; While normalizing, the unfolding mechanism of the grecguard-operator
;; may be blocked by setting GRECGUARD-UNFOLDING-FLAG to #f.

(define GRECGUARD-UNFOLDING-FLAG #t)

(define (grecguard-at uninst-grecguardop-type tsubst inst-grecguardop-type
		      f m . opt-all-formula)
  (let* ((gind-type? (pair? opt-all-formula))
         (arity (if gind-type? (+ f m 4) (+ m 3))))
    (nbe-make-object
     inst-grecguardop-type
     (nbe-curry
      (lambda objs
        (let* ((test-obj (list-ref objs (+ f m 2))) ;b
               (test-val (nbe-object-to-value test-obj))
               (param-objs (list-head objs f))
               (measure-obj (list-ref objs f)) ;mu
               (step-obj (list-ref objs (+ f m 1))) ;G
               (arg-objs (list-head (list-tail objs (+ f 1)) m)) ;xs
               (arg-types (map nbe-object-to-type arg-objs))
               (val-type ;tau
                (arrow-form-to-final-val-type inst-grecguardop-type arity)))
          (cond
           ((or (nbe-fam-value? test-val)
		(not GRECGUARD-UNFOLDING-FLAG)) ;reproduce
	    (nbe-reflect
	     (nbe-make-termfam
	      val-type
	      (lambda (k)
		(apply
		 mk-term-in-app-form
		 (make-term-in-const-form ;grecguard-const
		  (apply
		   uninst-grecguardop-type-etc-to-grecguard-const
		   uninst-grecguardop-type tsubst inst-grecguardop-type f m
		   opt-all-formula))
		 (map (lambda (x) (nbe-fam-apply (nbe-reify x) k))
		      objs))))))
	   ((nbe-constr-value? test-val)
            (let ((name (nbe-constr-value-to-name test-val)))
              (cond
               ((string=? name "True")
                (let*
		    ((pd-type (apply mk-arrow
				     (append
				      arg-types
				      (if gind-type?
					  (list (make-tconst "atomic"))
					  '())
				      (list val-type))))
		     (pd-obj ;([ys]GRecGuard mu ys G(mu ys<mu xs))
					;or ([ys,atomic] ...)
		      (nbe-make-object
		       pd-type
		       (nbe-curry
			(lambda objs2
			  (let*
			      ((ys (list-head objs2 m))
			       (muys (apply nbe-object-app
					    (cons measure-obj ys)))
			       (muxs (apply nbe-object-app
					    (cons measure-obj arg-objs)))
			       (test-obj ;mu ys<mu xs
				(nbe-object-app natlt-obj muys muxs))
			       (grecguard-const
				(apply
				 uninst-grecguardop-type-etc-to-grecguard-const
				 (append (list uninst-grecguardop-type tsubst
					       inst-grecguardop-type f m)
					 opt-all-formula)))
			       (grecguard-obj (const-to-object-or-arity
					       grecguard-const)))
			    (apply
			     nbe-object-app
			     grecguard-obj
			     (append param-objs (cons measure-obj ys)
				     (list step-obj test-obj)
				     (if gind-type?
					 (list (list-ref objs2 m))
					 '())))))
			pd-type
			(if gind-type? (+ m 1) m)))))
                  (apply nbe-object-app
                         step-obj (append arg-objs (list pd-obj)))))
	       ((string=? name "False")
                (if gind-type?
                    (let* ((all-formula (car opt-all-formula))
			   (vars (all-form-to-vars all-formula m))
                           (kernel (all-form-to-final-kernel all-formula m))
                           (free (formula-to-free all-formula))
                           (arg-terms (map (lambda (obj)
                                             (nbe-extract (nbe-reify obj)))
                                           arg-objs))
                           (subst (make-substitution vars arg-terms))
                           (inst-formula (formula-substitute kernel subst))
                           (subst-all-formula
                            (apply mk-all (append free (list inst-formula))))
                           (new-free (formula-to-free subst-all-formula))
                           (new-free-objs
                            (map (lambda (x)
                                   (nbe-reflect
                                    (nbe-term-to-termfam
                                     (make-term-in-var-form x))))
                                 new-free))
                           (new-all-formula
                            (apply mk-all (append
                                           new-free
                                           (list subst-all-formula)))) ;closed
                           (efqconst (formula-to-efq-const new-all-formula))
                           (efqobj (const-to-object-or-arity efqconst))
                           (falsum-obj (list-ref objs (+ f m 3))))
                      (apply
                       nbe-object-app
		       efqobj falsum-obj
		       (append new-free-objs param-objs)))
		    (let ((canon-term ;eps
                           (type-to-canonical-inhabitant val-type)))
                      (nbe-term-to-object canon-term '()))))
               (else (myerror "grecguard-at" "True or False expected"
			      test-name)))))
	   (else (myerror "grecguard-at" "value expected" test-val)))))
      inst-grecguardop-type
      arity))))

;; We define GRec in terms of GRecGuard.

(define (grec-at type-info)
  (let* ((uninst-grecop-type-and-tsubst
	  (type-info-to-uninst-grecop-type-and-tsubst type-info))
	 (uninst-grecop-type (car uninst-grecop-type-and-tsubst))
	 (tsubst (cadr uninst-grecop-type-and-tsubst))
	 (inst-grecop-type (type-substitute uninst-grecop-type tsubst))
	 (m (- (length type-info) 1)))
    (nbe-make-object
     inst-grecop-type
     (nbe-curry
      (lambda objs
	(let* ((trueobj (nbe-term-to-object (pt "True") '()))
	       (grecguard-const (type-info-to-grecguard-const type-info))
	       (grecguard-obj (const-to-object-or-arity grecguard-const)))
	  (apply nbe-object-app grecguard-obj (append objs (list trueobj)))))
      inst-grecop-type
      (+ m 2)))))

(define (type-info-to-grec-const type-info)
  (let* ((uninst-grecop-type-and-tsubst
	  (type-info-to-uninst-grecop-type-and-tsubst type-info))
	 (uninst-grecop-type (car uninst-grecop-type-and-tsubst))
	 (tsubst (cadr uninst-grecop-type-and-tsubst)))
    (make-const
     (grec-at type-info)
     "GRec" 'fixed-rules uninst-grecop-type tsubst t-deg-one 'const)))

;; all-formula-and-number-to-grecguard-const will be used in proof.scm
;; to achieve normalization of proofs via translating them in terms, to
;; translate a gind-aconst.  In addition we need the number m of
;; quantifiers used for the axioms.

(define (all-formula-and-number-to-grecguard-const all-formula m)
  (let* ((uninst-gind-formula-and-tpsubst
          (all-formula-to-uninst-gind-formula-and-tpsubst all-formula m))
	 (uninst-gind-formula (car uninst-gind-formula-and-tpsubst))
	 (tpsubst (cadr uninst-gind-formula-and-tpsubst))
	 (tsubst (list-transform-positive tpsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (psubst (list-transform-positive tpsubst
		   (lambda (x) (pvar-form? (car x)))))
	 (pvar (caar psubst)) ;there is only one pvar (gind is not simult.)
	 (cterm (cadar psubst))
	 (new-tvar (PVAR-TO-TVAR pvar))
	 (nbe-type (nbe-formula-to-type (cterm-to-formula cterm)))
	 (new-tsubst (make-subst new-tvar nbe-type))
	 (free (formula-to-free all-formula))
	 (param-types (map var-to-type free)) ;alphas
	 (uninst-grecguardop-type
	  (apply mk-arrow (append param-types (list (nbe-formula-to-type
						     uninst-gind-formula)))))
	 (inst-grecguardop-type (type-substitute uninst-grecguardop-type
						 (append tsubst new-tsubst))))
    (uninst-grecguardop-type-etc-to-grecguard-const
     uninst-grecguardop-type (append tsubst new-tsubst) inst-grecguardop-type
     (length free) m all-formula)))

;; We define a procedure that takes alg-or-arrow-types and returns the
;; types of the corecursion constants, split into uninstantiated types
;; and a type substitution.

;; alg-or-arrow-types is a list of types alg or tau=>alg, where all
;; algs are simultaneously defined.  Then corecop-type is for instance
;; tau=>(tau=>uysum^m(product-type1 ysum .. ysum product-typek))=>alg
;; with as many uysum's as there are nullary constructors for alg (to
;; avoid unit ysum ..).  In the alg-case (chosen if tau is nulltype or
;; unit) take uysum^m(product-type1 ysum .. ysum product-typek)=>alg.

;; 2017-03-07 default for prim-prod-flag changed to #f 
(define (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
	 . alg-or-arrow-types-and-opt-prim-prod-flag)
  (let* ((last (car (last-pair alg-or-arrow-types-and-opt-prim-prod-flag)))
	 (prim-prod-flag (if (or (alg-form? last) (arrow-form? last)) #f last))
	 (alg-or-arrow-types
	  (if (or (alg-form? last) (arrow-form? last))
	      alg-or-arrow-types-and-opt-prim-prod-flag
	      (list-head
	       alg-or-arrow-types-and-opt-prim-prod-flag
	       (- (length alg-or-arrow-types-and-opt-prim-prod-flag) 1))))
	 (rel-algs (map (lambda (type)
			  (if (arrow-form? type)
			      (arrow-form-to-val-type type)
			      type))
			alg-or-arrow-types))
	 (f-or-types (map (lambda (type)
			    (if (arrow-form? type)
				(arrow-form-to-arg-type type)
				#f))
			  alg-or-arrow-types))
	 (f-or-tvars (map (lambda (type)
			    (if (arrow-form? type)
				(new-tvar)
				#f))
			  alg-or-arrow-types))
	 (types (list-transform-positive f-or-types (lambda (x) x)))
	 (tvars (list-transform-positive f-or-tvars (lambda (x) x)))
	 (rel-alg-names
	  (map (lambda (alg)
		 (if (alg-form? alg)
		     (alg-form-to-name alg)
		     (myerror
		      "alg-or-arrow-types-to-uninst-corecop-types-and-tsubst"
		      "alg expected" alg)))
	       rel-algs))
	 (alg-name (car rel-alg-names))
	 (alg-tvars (alg-name-to-tvars alg-name))
	 (tparam-lists (map alg-form-to-types rel-algs))
	 (tparams (car tparam-lists))
	 (tsubst1 (map list alg-tvars tparams))
	 (tsubst2 (make-substitution tvars types))
	 (uninst-algs (map (lambda (x) (apply make-alg x alg-tvars))
			   rel-alg-names))
	 (uninst-alg-or-arrow-types
	  (map (lambda (f-or-tvar uninst-alg)
		 (if f-or-tvar
		     (make-arrow f-or-tvar uninst-alg)
		     uninst-alg))
	       f-or-tvars uninst-algs))
	 (rel-alg-name-to-f-or-type-alist
	  (map (lambda (alg-name alg-or-arrow-type)
		 (list alg-name
		       (if (arrow-form? alg-or-arrow-type)
			   (arrow-form-to-arg-type alg-or-arrow-type)
			   #f)))
	       rel-alg-names uninst-alg-or-arrow-types))
	 (simalg-names (alg-name-to-simalg-names alg-name)))
    (if (not (equal? rel-alg-names (remove-duplicates rel-alg-names)))
	(myerror "alg-or-arrow-types-to-uninst-corecop-types-and-tsubst"
		 "distinct algs expected" rel-alg-names))
    (if (pair? (set-minus rel-alg-names simalg-names))
	(myerror "alg-or-arrow-types-to-uninst-corecop-types-and-tsubst"
		 "too many alg names" (set-minus rel-alg-names simalg-names)))
    (if (< 1 (length (remove-duplicates tparam-lists)))
	(myerror "alg-or-arrow-types-to-uninst-corecop-types-and-tsubst"
		 "equal type parameter lists expected" tparam-lists))
    (let* ((typed-constr-names-list
	    (map alg-name-to-typed-constr-names rel-alg-names))
	   (constr-types-list
	    (map (lambda (typed-constr-names)
		   (map typed-constr-name-to-type typed-constr-names))
		 typed-constr-names-list))
	   (product-types-list
	    (map (lambda (constr-types)
		   (map (lambda (constr-type)
			  (constructor-type-to-product-type
			   constr-type rel-alg-name-to-f-or-type-alist
			   prim-prod-flag))
			constr-types))
		 constr-types-list))
	   (sum-of-product-types-list
	    (map (lambda (product-types)
		   (apply mk-ysum-without-unit product-types))
		 product-types-list))
	   (uninst-step-types
	    (map (lambda (f-or-tvar sum-of-product-types)
		   (if f-or-tvar
		       (make-arrow f-or-tvar sum-of-product-types)
		       sum-of-product-types))
		 f-or-tvars sum-of-product-types-list))
	   (orig-ordered-uninst-step-types
	    (map (lambda (name)
		   (list-ref uninst-step-types
			     (- (length rel-alg-names)
				(length (member name rel-alg-names)))))
		 (list-transform-positive simalg-names
		   (lambda (name) (member name rel-alg-names))))))
      (list (map (lambda (uninst-alg f-or-tvar)
		   (if
		    f-or-tvar
		    (apply
		     mk-arrow (append (list f-or-tvar)
				      orig-ordered-uninst-step-types
				      (list uninst-alg)))
		    (apply
		     mk-arrow (append orig-ordered-uninst-step-types
				      (list uninst-alg)))))
		 uninst-algs f-or-tvars)
	    (append tsubst1 tsubst2)))))

;(pp (caar (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst (py "nat"))))
;; uysum nat ysumu=>nat

;; In constructor-type-to-product-type we assume that constr-type has
;; uninstantiated parameter types (to ensure that mk-ysum-without-unit
;; does not go wrong in case unit is a parameter type).  We also assume
;; that alg-names-with-f-or-type assigns #f or a type to every
;; simalg-name.  The result is a product type consisting of the
;; parameter types and for each predecessor type the sum of it and the
;; associated type, if there is any, and unit otherwise.

(define (constructor-type-to-product-type
	 constr-type rel-alg-name-to-f-or-type-alist . opt-prim-prod-flag)
  (let* ((alg-name (alg-form-to-name
		    (arrow-form-to-final-val-type constr-type)))
	 (argtypes (arrow-form-to-arg-types constr-type))
	 (rel-simalg-names (map car rel-alg-name-to-f-or-type-alist))
	 (f-or-types (map cadr rel-alg-name-to-f-or-type-alist))
	 (simalg-names (alg-name-to-simalg-names alg-name))
	 (irrel-simalg-names (set-minus simalg-names rel-simalg-names))
	 (param-tvars (alg-name-to-tvars alg-name))
	 (rel-simalgs (map (lambda (name) (apply make-alg name param-tvars))
			   rel-simalg-names))
	 (rel-simalgs-plus-types
	  (map (lambda (rel-simalg f-or-type)
		 (if f-or-type
		     (make-alg "ysum" rel-simalg f-or-type)
		     (make-alg "ysumu" rel-simalg)))
	       rel-simalgs f-or-types))
	 (argtypes-without-irrel-alg-names
	  (list-transform-positive argtypes
	    (lambda (argtype) (null? (intersection (type-to-alg-names argtype)
						   irrel-simalg-names)))))
	 (steptype-factors
	  (map (lambda (argtype)
		 (type-gen-substitute
		  argtype
		  (map list rel-simalgs rel-simalgs-plus-types)))
	       argtypes-without-irrel-alg-names))
	 (prim-prod? (and (pair? opt-prim-prod-flag) (car opt-prim-prod-flag))))
    (apply (if prim-prod? mk-star mk-yprod) steptype-factors)))

(define (alg-or-arrow-types-to-corec-consts . alg-or-arrow-types)
  (let* ((uninst-corecop-types-and-tsubst
	  (apply alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
		 alg-or-arrow-types))
	 (uninst-corecop-types (car uninst-corecop-types-and-tsubst))
	 (tsubst (cadr uninst-corecop-types-and-tsubst)))
    (map (lambda (uninst-corecop-type)
	   (make-const
	    (corec-at uninst-corecop-type tsubst)
	    "CoRec" 'fixed-rules uninst-corecop-type tsubst t-deg-zero 'const))
	 uninst-corecop-types)))

(define (alg-or-arrow-types-to-corec-const . alg-or-arrow-types)
  (car (apply alg-or-arrow-types-to-corec-consts alg-or-arrow-types)))

(define (corec-at uninst-corecop-type tsubst)
  (let* ((inst-corecop-type (type-substitute uninst-corecop-type tsubst))
	 (arity (length (arrow-form-to-arg-types inst-corecop-type))))
    (nbe-make-object
     inst-corecop-type
     (nbe-curry
      (lambda objs ;arity many
	(nbe-reflect ;reproduce
	 (nbe-make-termfam
	  (arrow-form-to-final-val-type inst-corecop-type arity)
	  (lambda (k)
	    (apply mk-term-in-app-form
		   (make-term-in-const-form ;corec-const
		    (make-const
		     (corec-at uninst-corecop-type tsubst)
		     "CoRec" 'fixed-rules uninst-corecop-type tsubst
		     t-deg-one 'const))
		   (map (lambda (x) (nbe-fam-apply (nbe-reify x) k))
			objs))))))
      inst-corecop-type
      arity))))

;; We now aim at a bounded reduction of corec constants.  First we
;; construct all simultaneously defined corec-consts from a given one
;; (for the base case of (Rec nat=>sigma_0 yprod ... yprod sigma_n).
;; This can be done as in alg-or-arrow-types-to-corec-consts, from
;; tsubst and uninst-corecop-types.  The objs are constructed via
;; corec-at.

(define (corec-const-to-uninst-corecop-types corec-const)
  (let* ((uninst-corecop-type (const-to-uninst-type corec-const))
	 (uninst-alg (arrow-form-to-final-val-type uninst-corecop-type))
	 (alg-name (alg-form-to-name uninst-alg))
	 (alg-types (alg-form-to-types uninst-alg))
	 (simalg-names (alg-name-to-simalg-names alg-name))
	 (arg-types (arrow-form-to-arg-types uninst-corecop-type))
	 (improper-corec? (= (length simalg-names) (length arg-types)))
	 (uninst-step-types (if improper-corec? arg-types (cdr arg-types)))
	 (f-or-tvars (map (lambda (type)
			    (if (arrow-form? type)
				(arrow-form-to-arg-type type)
				#f))
			  uninst-step-types)))
    (map (lambda (f-or-tvar simalg-name)
	   (if f-or-tvar
	       (apply mk-arrow
		      (append (list f-or-tvar)
			      uninst-step-types
			      (list (apply make-alg
					   (cons simalg-name alg-types)))))
	       (apply mk-arrow
		      (append uninst-step-types
			      (list (apply make-alg
					   (cons simalg-name alg-types)))))))
	 f-or-tvars simalg-names)))

(define (corec-const-to-corec-consts corec-const)
  (let* ((tsubst (const-to-tsubst corec-const))
	 (uninst-corecop-types
	  (corec-const-to-uninst-corecop-types corec-const)))
    (map (lambda (uninst-corecop-type)
	   (make-const
	    (corec-at uninst-corecop-type tsubst)
	    "CoRec" 'fixed-rules uninst-corecop-type tsubst t-deg-one 'const))
	 uninst-corecop-types)))

(define (corec-const-to-uninst-alg-or-arrow-types corec-const)
  (let* ((uninst-corecop-type (const-to-uninst-type corec-const))
	 (uninst-alg (arrow-form-to-final-val-type uninst-corecop-type))
	 (alg-name (alg-form-to-name uninst-alg))
	 (alg-types (alg-form-to-types uninst-alg))
	 (simalg-names (alg-name-to-simalg-names alg-name))
	 (arg-types (arrow-form-to-arg-types uninst-corecop-type))
	 (improper-corec? (= (length simalg-names) (length arg-types)))
	 (uninst-step-types (if improper-corec? arg-types (cdr arg-types)))
	 (f-or-tvars (map (lambda (type)
			    (if (arrow-form? type)
				(arrow-form-to-arg-type type)
				#f))
			  uninst-step-types))
	 (prelim-arrow-types
	  (map (lambda (f-or-tvar simalg-name)
		 (if f-or-tvar
		     (make-arrow f-or-tvar
				 (apply make-alg simalg-name alg-types))
		     (apply make-alg simalg-name alg-types)))
	       f-or-tvars simalg-names))
	 (init-arrow-type
	  (if (cadr (assoc alg-name (map list simalg-names f-or-tvars)))
	      (make-arrow (car arg-types) uninst-alg)
	      uninst-alg)))
    (cons init-arrow-type (remove init-arrow-type prelim-arrow-types))))

;; In corec-const-and-bound-to-bcorec-term we first construct
;; corec-consts (as in corec-const-to-corec-consts above), for the base
;; case of the bcorec-term.  The product of their types is the value
;; type of the recursion operator (over nat).  Next the step-term
;; lambda (n prev) (abstr-if-term1 pair .. pair abstr-if-termN) is
;; built.  We need variables us for the covals and vs for the steps.
;; Hence each (vi ui) has type ysum-without-unit-of-product-types.  For
;; each product type we introduce a product-variable y.  From the
;; components of the term corresponding to y and the argument-types of
;; the constructors we can build the abstr-constr-terms for the
;; constructors of algi, and using these the i-th if-term is
;; constructed via corec-test-and-abstr-constr-terms-to-if-term.

(define (corec-const-and-bound-to-bcorec-term corec-const bound)
  (let* ((tsubst (const-to-tsubst corec-const))
	 (uninst-corecop-type (const-to-uninst-type corec-const))
	 (uninst-alg (arrow-form-to-final-val-type uninst-corecop-type))
	 (alg-name (alg-form-to-name uninst-alg))
	 (simalg-names (alg-name-to-simalg-names alg-name))
					;corec-consts for the base case
	 (corec-consts (corec-const-to-corec-consts corec-const))
					;recursion constant
	 (types-of-corec-consts (map const-to-type corec-consts))
	 (product-type (apply mk-yprod types-of-corec-consts))
	 (rec-const (arrow-types-to-rec-const
		     (make-arrow (make-alg "nat") product-type)))
					;the step term:	constrs-list
	 (typed-constr-names-list
	  (map alg-name-to-typed-constr-names simalg-names))
	 (constr-names-list
	  (map (lambda (typed-constr-names)
		 (map typed-constr-name-to-name typed-constr-names))
	       typed-constr-names-list))
	 (uninst-constrs-list (map (lambda (constr-names)
				     (map constr-name-to-constr constr-names))
				   constr-names-list))
	 (constrs-list (map (lambda (constrs)
			      (map (lambda (constr)
				     (const-substitute constr tsubst #f))
				   constrs))
			    uninst-constrs-list))
	 (arg-types-list-list
	  (map (lambda (constrs)
		 (map arrow-form-to-arg-types (map const-to-type constrs)))
	       constrs-list))
					;abstr-constr-terms-list
	 (step-types
	  (let ((arg-types
		 (arrow-form-to-arg-types (const-to-type corec-const))))
	    (if (< (length simalg-names) (length arg-types))
		(cdr arg-types)
		arg-types)))
	 (f-or-types (map (lambda (step-type)
			    (if (arrow-form? step-type)
				(arrow-form-to-arg-type step-type)
				#f))
			  step-types))
	 (f-or-us (map (lambda (f-or-type)
			 (if f-or-type
			     (type-to-new-partial-var f-or-type)
			     #f))
		       f-or-types))
	 (vs (map type-to-new-partial-var step-types))
	 (product-types-list (map (lambda (step-type arg-types-list)
				    (ysum-without-unit-to-components
				     (if (arrow-form? step-type)
					 (arrow-form-to-val-type step-type)
					 step-type)
				     (length arg-types-list)))
				  step-types arg-types-list-list))
	 (ys-list ;each ys is a list of new vars of product types
	  (map (lambda (product-types)
		 (map type-to-new-partial-var product-types))
	       product-types-list))
					;variables n and prev
	 (n (type-to-new-partial-var (make-alg "nat")))
	 (prev (type-to-new-partial-var product-type))
					;step term
	 (prev-comps (term-to-components (make-term-in-var-form prev)))
	 (alg-names-with-prev-comps
	  (map (lambda (alg-name prev-comp) (list alg-name prev-comp))
	       simalg-names prev-comps))
	 (y-comps-list-list
	  (map (lambda (ys arg-types-list)
		 (map (lambda (y arg-types)
			(term-to-components (make-term-in-var-form y)
					    (length arg-types)))
		      ys arg-types-list))
	       ys-list arg-types-list-list))
	 (param-tvars (alg-form-to-types uninst-alg))
	 (simalgs (map (lambda (simalg-name)
			 (apply make-alg simalg-name
				(map (lambda (param-tvar)
				       (type-substitute param-tvar tsubst))
				     param-tvars)))
		       simalg-names))
	 (new-tvars (map (lambda (x) (new-tvar)) simalg-names))
	 (maps
	  (map (lambda (alg f-or-type prev-comp)
		 (if
		  f-or-type
		  (let ((test-var (type-to-new-partial-var (make-ysum alg f-or-type)))
			(alg-var (type-to-new-partial-var alg))
			(pd-var (type-to-new-partial-var f-or-type)))
		    (make-term-in-abst-form
		     test-var
		     (make-term-in-if-form
		      (make-term-in-var-form test-var)
		      (list (make-term-in-abst-form
			     alg-var (make-term-in-var-form alg-var))
			    (make-term-in-abst-form
			     pd-var ;recursive call
			     (apply mk-term-in-app-form
				    prev-comp (make-term-in-var-form pd-var)
				    (map make-term-in-var-form vs)))))))
		  (let ((test-var (type-to-new-partial-var (make-ysumu alg)))
			(alg-var (type-to-new-partial-var alg)))
		    (make-term-in-abst-form
		     test-var
		     (make-term-in-if-form
		      (make-term-in-var-form test-var)
		      (list (make-term-in-abst-form
			     alg-var (make-term-in-var-form alg-var))
					;recursive call
			    (apply mk-term-in-app-form
				   prev-comp
				   (map make-term-in-var-form vs))))))))
	       simalgs f-or-types prev-comps))
	 (args-list-list
	  (map
	   (lambda (y-comps-list arg-types-list)
	     (map
	      (lambda (y-comps arg-types)
		(map
		 (lambda (y-comp arg-type)
		   (apply
		    mk-term-in-app-form
		    (make-term-in-const-form
		     (make-map-const
		      (type-gen-substitute
		       arg-type (map list simalgs new-tvars))
		      new-tvars
		      (map (lambda (alg f-or-type)
			     (if f-or-type
				 (make-ysum alg f-or-type)
				 (make-ysumu alg)))
			   simalgs f-or-types)
		      simalgs))
		    y-comp maps))
		 y-comps arg-types))
	      y-comps-list arg-types-list))
	   y-comps-list-list arg-types-list-list))
	 (constr-terms-list
	  (map (lambda (constrs args-list)
		 (map (lambda (constr args)
			(apply mk-term-in-app-form
			       (make-term-in-const-form constr) args))
		      constrs args-list))
	       constrs-list args-list-list))
	 (abstr-constr-terms-list
	  (map (lambda (constr-terms arg-types-list ys)
		 (map (lambda (constr-term arg-types y)
			(if (null? arg-types)	;nullary constructor
			    constr-term
			    (make-term-in-abst-form y constr-term)))
		      constr-terms arg-types-list ys))
	       constr-terms-list arg-types-list-list ys-list))
	 (tests (map (lambda (f-or-u v)
		       (if f-or-u
			   (make-term-in-app-form
			    (make-term-in-var-form v)
			    (make-term-in-var-form f-or-u))
			   (make-term-in-var-form v)))
		     f-or-us vs))
	 (if-terms (map (lambda (test abstr-constr-terms)
			  (if
			   (= 1 (length abstr-constr-terms))
			   (if (arrow-form?
				(term-to-type (car abstr-constr-terms)))
			       (make-term-in-app-form
				(car abstr-constr-terms) test)
			       (car abstr-constr-terms))
			   (apply corec-test-and-abstr-constr-terms-to-if-term
				  test abstr-constr-terms)))
			tests abstr-constr-terms-list))
	 (abstr-if-terms
	  (map (lambda (f-or-u if-term)
		 (if f-or-u
		     (apply mk-term-in-abst-form
			    f-or-u (append vs (list if-term)))
		     (apply mk-term-in-abst-form (append vs (list if-term)))))
	       f-or-us if-terms))
	 (step-term (mk-term-in-abst-form
		     n prev (apply mk-term-in-cons-form abstr-if-terms))))
    (list-ref
     (term-to-components
      (mk-term-in-app-form
       (make-term-in-const-form rec-const)
       bound
       (apply mk-term-in-cons-form (map make-term-in-const-form corec-consts))
       step-term))
     (- (length simalg-names) (length (member alg-name simalg-names))))))

;; corec-test-and-abstr-constr-terms-to-if-term takes test whose type
;; is the ysum (without unit) of the costep-types for the constructors
;; of one of the simultaneously defined algebras.  It assumes that
;; there are at least two constructors for this algebra (otherwise no
;; if-term is necessary).

(define (corec-test-and-abstr-constr-terms-to-if-term test term1 term2 . terms)
  (if
   (null? terms)
   (make-term-in-if-form test (list term1 term2))
   (let* ((alg (term-to-type test))
	  (alg-name (if (alg-form? alg) (alg-form-to-name alg)
			(myerror "corec-test-and-abstr-constr-terms-to-if-term"
				 "term of alg type expected" test)))
	  (types (alg-form-to-types alg))
	  (type (cond ((string=? "uysum" alg-name) (car types))
		      ((string=? "ysumu" alg-name) (car types))
		      ((string=? "ysum" alg-name) (cadr types))
		      (else (myerror
			     "corec-test-and-abstr-constr-terms-to-if-term"
			     "term of uysum or ysum type expected" test))))
	  (var (type-to-new-var type)))
     (make-term-in-if-form
      test
      (list term1
	    (make-term-in-abst-form
	     var (apply
		  corec-test-and-abstr-constr-terms-to-if-term
		  (append (list (make-term-in-var-form var)
				term2 (car terms))
			  (cdr terms)))))))))

(define (bcorec-term-and-alg-name-to-component bcorec-term alg-name)
  (let ((simalg-names (alg-name-to-simalg-names alg-name)))
    (bcorec-term-and-alg-name-to-component-aux
     bcorec-term alg-name simalg-names)))

(define (bcorec-term-and-alg-name-to-component-aux term name names)
  (if (= 1 (length names))
      term
      (if (string=? name (car names))
	  (term-in-cons-form-to-left term)
	  (bcorec-term-and-alg-name-to-component-aux
	   (term-in-cons-form-to-right term) name (cdr names)))))

;; (undelay-delayed-corec term bound) replaces every corec constant
;; in term by the result of (corec-const-and-bound-to-bcorec-term
;; corec-const bound).

(define (undelay-delayed-corec term bound)
  (if (not (and (integer? bound) (not (negative? bound))))
      (myerror "undelay-delayed-corec" "non-negative integer expected" bound))
  (case (tag term)
    ((term-in-var-form) term)
    ((term-in-const-form)
     (let ((const (term-in-const-form-to-const term)))
       (if (string=? "CoRec" (const-to-name const))
	   (corec-const-and-bound-to-bcorec-term
	    const (make-numeric-term-wrt-nat bound))
	   term)))
    ((term-in-app-form)
     (let ((terms (term-in-app-form-to-final-op-and-args term)))
       (apply mk-term-in-app-form
	      (map (lambda (t) (undelay-delayed-corec t bound))
		   terms))))
    ((term-in-abst-form)
     (let ((vars (term-in-abst-form-to-vars term))
	   (kernel (term-in-abst-form-to-final-kernel term)))
       (apply mk-term-in-abst-form
	      (append vars
		      (list (undelay-delayed-corec kernel bound))))))
    ((term-in-pair-form)
     (let ((left-term (term-in-pair-form-to-left term))
	   (right-term (term-in-pair-form-to-right term)))
       (make-term-in-pair-form
	(undelay-delayed-corec left-term bound)
	(undelay-delayed-corec right-term bound))))
    ((term-in-lcomp-form)
     (let ((kernel (term-in-lcomp-form-to-kernel term)))
       (make-term-in-lcomp-form (undelay-delayed-corec kernel bound))))
    ((term-in-rcomp-form)
     (let ((kernel (term-in-rcomp-form-to-kernel term)))
       (make-term-in-rcomp-form (undelay-delayed-corec kernel bound))))
    ((term-in-if-form)
     (let ((test (term-in-if-form-to-test term))
	   (alts (term-in-if-form-to-alts term))
	   (rest (term-in-if-form-to-rest term)))
       (make-term-in-if-form
	(undelay-delayed-corec test bound)
	(map (lambda (alt)
	       (undelay-delayed-corec alt bound))
	     alts)
	rest)))
    (else (myerror "undelay-delayed-corec" "term expected" term))))

;; Temporarily we add for instance ListCoRecRule as global assumption.
;; It should be an axiom.

(define (alg-name-to-corec-rule-ga alg-name)
  (let* ((simalg-names (alg-name-to-simalg-names alg-name))
	 (tvars (cond ((= 1 (alg-name-to-arity alg-name))
		       (list (make-tvar -1 "beta")))
		      ((= 2 (alg-name-to-arity alg-name))
		       (list (make-tvar -1 "beta") (make-tvar -1 "gamma")))
		      (else (alg-name-to-tvars alg-name))))
	 (simalgs (map (lambda (simalg-name)
			 (apply make-alg simalg-name tvars))
		       simalg-names))
	 (arg-tvars (cond
		     ((= 1 (length simalg-names))
		      (list (make-tvar -1 "alpha")))
		     ((= 2 (length simalg-names))
		      (list (make-tvar -1 "alpha1") (make-tvar -1 "alpha2")))
		     (else (map (lambda (x) (new-tvar)) simalg-names))))
	 (arrow-types (map (lambda (arg-tvar simalg)
			     (make-arrow arg-tvar simalg))
			   arg-tvars simalgs))
	 (corec-consts (apply alg-or-arrow-types-to-corec-consts
			      arrow-types))
	 (corec-const (car corec-consts))
	 (bcorec-term (corec-const-and-bound-to-bcorec-term
		       corec-const (pt "Succ Zero")))
	 (corec-type (const-to-type corec-const))
	 (arg-type (arrow-form-to-arg-type corec-type))
	 (step-type (arrow-form-to-arg-type
		     (arrow-form-to-val-type corec-type)))
	 (arg-var (make-var arg-type -1 t-deg-zero (default-var-name arg-type)))
	 (step-var
	   (make-var step-type -1 t-deg-zero (default-var-name step-type)))
	 (applied-corec-term (mk-term-in-app-form
			      (make-term-in-const-form corec-const)
			      (make-term-in-var-form arg-var)
			      (make-term-in-var-form step-var)))
	 (applied-bcorec-term (mk-term-in-app-form
			       bcorec-term
			       (make-term-in-var-form arg-var)
			       (make-term-in-var-form step-var)))
	 (eq-fla (make-eqd applied-corec-term applied-bcorec-term))
	 (neq-fla (rename-variables (nf eq-fla)))
	 (gen-neq-fla (mk-allnc arg-var step-var neq-fla))
	 (ga-name (string-append (string-capitalize-first alg-name)
				 "CoRecRule")))
    (add-global-assumption ga-name gen-neq-fla)))

;; Now for destructors.

(define (alg-to-uninst-destr-type-and-tsubst alg . opt-prim-prod-flag)
  (let* ((alg-name (if (alg-form? alg)
		       (alg-form-to-name alg)
		       (myerror "alg-to-uninst-destr-type-and-tsubst"
				"algebra expected" alg)))
	 (alg-tvars (alg-name-to-tvars alg-name))
	 (tparams (alg-form-to-types alg))
	 (tsubst (make-substitution alg-tvars tparams))
	 (arg-type (apply make-alg alg-name alg-tvars))
	 (typed-constr-names ;only those for the present alg-name
	  (alg-name-to-typed-constr-names alg-name))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (prim-prod? (and (pair? opt-prim-prod-flag) (car opt-prim-prod-flag)))
	 (product-types
	  (map (lambda (constr-type)
		 (apply (if prim-prod? mk-star mk-yprod)
			(arrow-form-to-arg-types constr-type)))
	       constr-types))
	 (val-type (apply mk-ysum-without-unit product-types)))
    (list (make-arrow arg-type val-type) tsubst)))

(define (alg-to-destr-const alg . opt-prim-prod-flag)
  (let* ((uninst-destr-type-and-tsubst
	  (apply alg-to-uninst-destr-type-and-tsubst alg opt-prim-prod-flag))
	 (uninst-destr-type (car uninst-destr-type-and-tsubst))
	 (tsubst (cadr uninst-destr-type-and-tsubst)))
    (make-const
     (apply destruct-at uninst-destr-type tsubst opt-prim-prod-flag)
     "Destr" 'fixed-rules uninst-destr-type tsubst t-deg-one 'const)))

(define (destr-const-to-alg const)
  (let* ((uninst-type (const-to-uninst-type const))
	 (alg-type-and-step-types (arrow-form-to-arg-types uninst-type)))
    (car alg-type-and-step-types)))

(define (destruct-at uninst-destr-type tsubst . opt-prim-prod-flag)
  (let ((inst-destr-type (type-substitute uninst-destr-type tsubst)))
    (nbe-make-object
     inst-destr-type
     (nbe-curry
      (lambda objs ;arity (that is 1) many
	(let* ((obj (car objs))
	       (val (nbe-object-to-value obj)))
	  (cond
	   ((nbe-fam-value? val) ;reproduce
	    (nbe-reflect
	     (nbe-make-termfam
	      (arrow-form-to-val-type inst-destr-type)
	      (lambda (k)
		(make-term-in-app-form
		 (make-term-in-const-form
		  (make-const
		   (destruct-at uninst-destr-type tsubst) "Destr" 'fixed-rules
		   uninst-destr-type tsubst t-deg-one 'const))
		 (nbe-fam-apply (nbe-reify obj) k))))))
	   ((nbe-constr-value? val)
	    (let* ((constr-name (nbe-constr-value-to-name val))
		   (alg (arrow-form-to-arg-type uninst-destr-type))
		   (alg-name (alg-form-to-name alg))
		   (typed-constr-names ;only those for the present alg-name
		    (alg-name-to-typed-constr-names alg-name))
		   (constr-names
		    (map typed-constr-name-to-name typed-constr-names))
		   (n (do ((i 0 (+ 1 i))
			   (names constr-names (cdr names)))
			  ((string=? (car names) constr-name) i)))
		   (ysum-without-unit (arrow-form-to-val-type inst-destr-type))
		   (injection-or-f
		    (cond
		     ((and (alg-form? ysum-without-unit)
			   (member (alg-form-to-name ysum-without-unit)
				   (list "ysum" "uysum" "ysumu" "boole")))
		      (make-injection ysum-without-unit n))
		     ((member (alg-form-to-name ysum-without-unit)
			      (list "unit"))
		      (make-term-in-const-form (constr-name-to-constr "Dummy")))
		     (else #f)))
		   (constr-args (nbe-constr-value-to-args val)))
	      (if
	       (null? constr-args)
	       (nbe-term-to-object injection-or-f '())
	       (let* ((prim-prod? (and (pair? opt-prim-prod-flag)
				       (car opt-prim-prod-flag)))
		      (prod-obj
		       (if
			prim-prod?
			(apply nbe-mk-prod-obj constr-args)
			(let* ((constr (constr-name-to-constr constr-name))
			       (type (const-to-uninst-type constr))
			       (arg-types (arrow-form-to-arg-types type))
			       (inst-arg-types
				(map (lambda (type)
				       (type-substitute type tsubst))
				     arg-types))
			       (vars (map type-to-new-partial-var
					  inst-arg-types))
			       (varterms (map make-term-in-var-form vars))
			       (product-generator-term
				(apply
				 mk-term-in-abst-form
				 (append
				  vars (list (apply mk-term-in-cons-form
						    varterms)))))
			       (product-generator-obj
				(nbe-term-to-object
				 product-generator-term '())))
			  (apply nbe-object-app
				 product-generator-obj
				 constr-args)))))
		 (if injection-or-f
		     (nbe-object-apply
		      (nbe-term-to-object injection-or-f '()) prod-obj)
		     prod-obj)))))
	   (else (myerror "destruct-at" "value expected" val)))))
      inst-destr-type
      1))))

;; ex-elim: allnc zs(ex z A -> all z(A -> B) -> B)

(define (ex-formula-and-concl-to-ex-elim-const ex-formula concl)
  (let* ((free (union (formula-to-free ex-formula) (formula-to-free concl)))
	 (free-types (map var-to-type free))
	 (f (length free))
         (var (ex-form-to-var ex-formula))
	 (inst-type (var-to-type var))
         (kernel (ex-form-to-kernel ex-formula))
	 (side-formula (mk-all var (mk-imp kernel concl)))
	 (side-type (nbe-formula-to-type side-formula))
	 (concl-type (nbe-formula-to-type concl))
	 (arity (+ f 2))
	 (exelimop-type
	  (apply mk-arrow (append free-types (list (make-tconst "existential")
						   side-type concl-type)))))
    (ex-formula-and-concl-to-ex-elim-const-aux
     ex-formula concl f arity exelimop-type)))

(define (ex-formula-and-concl-to-ex-elim-const-aux
	 ex-formula concl f arity exelimop-type)
  (make-const (ex-formula-and-concl-to-ex-elim-const-obj
	       ex-formula concl f arity exelimop-type)
	      "Ex-Elim" 'fixed-rules exelimop-type empty-subst
	      1 'const ex-formula concl))

(define (ex-formula-and-concl-to-ex-elim-const-obj
	 ex-formula concl f arity exelimop-type)
  (nbe-make-object
   exelimop-type
   (nbe-curry
    (lambda objs
      (let* ((ex-obj (list-ref objs f))
	     (ex-value (nbe-object-to-value ex-obj)))
	(cond
	 ((nbe-fam-value? ex-value) ;then reproduce
	  (let* ((refl-term-obj
		  (nbe-reflect
		   (nbe-make-termfam
		    exelimop-type
		    (lambda (k)
		      (make-term-in-const-form
		       (ex-formula-and-concl-to-ex-elim-const-aux
			ex-formula concl f arity exelimop-type))))))
		 (val (nbe-object-to-value refl-term-obj)))
	    (apply (nbe-uncurry val arity) objs)))
	 ((nbe-constr-value? ex-value)
	  (let* ((args (nbe-constr-value-to-args ex-value))
		 (f1 (- (length args) 2))
		 (inst-obj (list-ref args f1))
		 (kernel-obj (list-ref args (+ f1 1)))
		 (side-obj (list-ref objs (+ f 1))))
	    (nbe-object-app side-obj inst-obj kernel-obj)))
	 (else
	  (myerror
	   "ex-formula-and-concl-to-ex-elim-const-obj" "ex-value expected"
	   ex-value)))))
    exelimop-type
    arity)))

(define (nbe-curry f type n)
  (if (= 1 n)
      f
      (lambda (obj)
	(let ((valtype (arrow-form-to-val-type type)))
	  (nbe-make-object
	   valtype
	   (nbe-curry (lambda objs
			(apply f obj objs)) valtype (- n 1)))))))

(define (nbe-uncurry g n)
  (if (= 1 n)
      g
      (lambda objs
	(apply (nbe-uncurry (nbe-object-to-value (g (car objs))) (- n 1))
	       (cdr objs)))))

;; Type substitution in constants.  In const-substitute we assume that
;; the constant is a proper one, i.e., not one of those used during
;; proof normalization.

(define (const-substitute const tsubst update-of-program-constants-done?)
  (if
   (null? tsubst)
   const
   (let* ((obj-or-arity (const-to-object-or-arity const))
	  (name (const-to-name const))
	  (uninst-type (const-to-uninst-type const))
	  (orig-tsubst (const-to-tsubst const))
	  (t-deg (const-to-t-deg const))
	  (token-type (const-to-token-type const))
	  (repro-data (const-to-repro-data const))
	  (composed-tsubst (compose-substitutions orig-tsubst tsubst))
	  (restricted-tsubst (restrict-substitution-to-args
			      composed-tsubst (const-to-tvars const))))
     (case (const-to-kind const)
       ((constr)
	(if
	 (or (string=? "Ex-Intro" (const-to-name const))
 	     (string=? "Intro" (const-to-name const)))
	 const
         ;else form new-constr with restricted-subst.  If not yet done,
         ;update CONSTRUCTORS, via computing for all simalgs and all of
         ;their constructors the new object, type etc.  Return new-constr
	 (let* ((val-type (arrow-form-to-final-val-type uninst-type))
		(alg-name (alg-form-to-name val-type))
		(alg-names (alg-name-to-simalg-names alg-name))
		(alg-names-with-typed-constr-names
		 (map (lambda (x)
			(cons x (alg-name-to-typed-constr-names x)))
		      alg-names))
		(assoc-list (constr-name-to-inst-constructors name))
		(info (assoc-wrt substitution-equal?
				 restricted-tsubst assoc-list)))
	   (if
	    info
	    (cadr info) ;else update CONSTRUCTORS, return new-constr
	    (begin
	      (for-each ;of alg-names-with-typed-constr-names
	       (lambda (item)
		 (let ((typed-constr-names (cdr item)))
		   (for-each ;of typed-constr-names, update CONSTRUCTORS
		    (lambda (y)
		      (let* ((constr-name (typed-constr-name-to-name y))
			     (type (typed-constr-name-to-type y))
			     (optional-token-type1
			      (typed-constr-name-to-optional-token-type y))
			     (token-type1 (if (pair? optional-token-type1)
					      (car optional-token-type1)
					      'const))
			     (argtypes (arrow-form-to-arg-types type))
			     (arity (length argtypes))
			     (new-type
			      (type-substitute type restricted-tsubst))
			     (new-valtype
			      (arrow-form-to-final-val-type new-type))
			     (delayed-constr
			      (eval-once (lambda ()
					   (constr-name-and-tsubst-to-constr
					    constr-name restricted-tsubst))))
			     (obj (nbe-make-object
				   new-type
				   (if (zero? arity)
				       (nbe-make-constr-value
					constr-name '() delayed-constr)
				       (nbe-curry
					(lambda objs ;as many as argtypes
					  (nbe-make-object
					   new-valtype
					   (nbe-make-constr-value
					    constr-name objs delayed-constr)))
					new-type
					arity))))
			     (constr
			      (make-const obj constr-name 'constr type
					  restricted-tsubst t-deg-one
					  token-type1))
			     (constrs-except-name
			      (do ((l CONSTRUCTORS (cdr l))
				   (res '() (if (string=? (caar l) constr-name)
						res
						(cons (car l) res))))
				  ((null? l) (reverse res))))
			     (prev-alist-for-name
			      (let ((info (assoc constr-name CONSTRUCTORS)))
				(if info
				    (cadr info)
				    (myerror "const-substitute"
					     "constr expected"
					     constr-name))))
			     (new-alist-for-name
			      (cons (list restricted-tsubst constr)
				    prev-alist-for-name)))
			(set! CONSTRUCTORS
			      (cons (list constr-name new-alist-for-name)
				    constrs-except-name))))
		    typed-constr-names)))
	       alg-names-with-typed-constr-names)
	      (constr-name-and-tsubst-to-constr name restricted-tsubst))))))
       ((pconst)
        ;form new-pconst with restricted-tsubst.  If not yet done, update
        ;PROGRAM-CONSTANTS with new object for restricted-tsubst,
        ;return new-pconst.
	(let* ((new-pconst (make-const obj-or-arity
				       name
				       'pconst
				       uninst-type
				       restricted-tsubst
				       t-deg
				       token-type))
	       (tsubst-obj-alist (pconst-name-to-inst-objs name))
	       (info (assoc-wrt substitution-equal?
				restricted-tsubst tsubst-obj-alist)))
	  (if
	   (or update-of-program-constants-done? info)
	   new-pconst ;else update PROGRAM-CONSTANTS, then return new-pconst
	   (let* ((uninst-const (pconst-name-to-pconst name))
		  (comprules (pconst-name-to-comprules name))
		  (rewrules (pconst-name-to-rewrules name))
		  (external-code (pconst-name-to-external-code name))
		  (obj (if external-code
			   (nbe-pconst-and-tsubst-and-rules-to-object
			    const restricted-tsubst comprules rewrules
			    external-code)
			   (nbe-pconst-and-tsubst-and-rules-to-object
			    const restricted-tsubst comprules rewrules)))
		  (pconsts-except-name
		   (do ((l PROGRAM-CONSTANTS (cdr l))
			(res '() (if (string=? (caar l) name)
				     res
				     (cons (car l) res))))
		       ((null? l) (reverse res))))
		  (prev-alist-for-name (pconst-name-to-inst-objs name))
		  (new-alist-for-name (cons (list restricted-tsubst obj)
					    prev-alist-for-name)))
	     (set! PROGRAM-CONSTANTS
		   (cons (list name uninst-const comprules rewrules
			       new-alist-for-name)
			 pconsts-except-name))
	     new-pconst))))
       ((fixed-rules)
	(cond
	 ((string=? "Rec" name)
	  (let* ((uninst-arrow-types (rec-const-to-uninst-arrow-types const))
		 (inst-arrow-types
		  (map (lambda (x) (type-substitute x restricted-tsubst))
		       uninst-arrow-types)))
	    (car (apply arrow-types-to-rec-consts inst-arrow-types))))
	 ((string=? "Cases" name)
	  (let* ((alg-type (arrow-form-to-arg-type uninst-type))
		 (val-type (arrow-form-to-final-val-type uninst-type))
		 (uninst-arrow-type (make-arrow alg-type val-type))
		 (inst-arrow-type
		  (type-substitute uninst-arrow-type restricted-tsubst)))
	    (arrow-type-to-cases-const inst-arrow-type)))
	 ((string=? "GRecGuard" name)
	  (let* ((uninst-type-info (grecguard-const-to-uninst-type-info const))
		 (m (- (length uninst-type-info) 1)))
	    (uninst-grecguardop-type-etc-to-grecguard-const
	     uninst-type restricted-tsubst
	   (type-substitute uninst-type restricted-tsubst) 0 m)))
	 ((string=? "CoRec" name)
	  (let* ((uninst-alg-or-arrow-types
		  (corec-const-to-uninst-alg-or-arrow-types const))
		 (inst-alg-or-arrow-types
		  (map (lambda (x) (type-substitute x restricted-tsubst))
		       uninst-alg-or-arrow-types)))
	    (car (apply alg-or-arrow-types-to-corec-consts
			inst-alg-or-arrow-types))))
	 ((string=? "Destr" name)
	  (let* ((val-type (arrow-form-to-val-type uninst-type))
		 (components (ysum-without-unit-to-components val-type))
		 (prim-prod-flag
		  (if (pair? components)
		      (cond
		       ((alg-form? (car components)) #f)
		       ((star-form? (car components)) #t)
		       (else (myerror "const-substitute"
				      "alg or star form expected at Destr"
				      (car components))))
		      (myerror "const-substitute"
			       "components expected in Destr val-type"
			       val-type)))
		 (alg (destr-const-to-alg const))
		 (inst-alg (type-substitute alg restricted-tsubst)))
	    (alg-to-destr-const inst-alg prim-prod-flag)))
	 ((string=? "Map" name)
	  (let* ((inst-mapop-type ;rho(sigmas)=>(sigmas=>taus)=>rho(taus)
	  	  (const-to-type const))
		 (inst-arrow-types ;sigmas=>taus
	  	  (arrow-form-to-arg-types
	  	   (arrow-form-to-val-type inst-mapop-type)))
		 (argtypes ;sigmas
	  	  (map arrow-form-to-arg-type inst-arrow-types))
		 (valtypes ;taus
	  	  (map arrow-form-to-val-type inst-arrow-types))
		 (subst-argtypes
		  (map (lambda (type) (type-substitute type tsubst))
		       argtypes))
		 (subst-valtypes
		  (map (lambda (type) (type-substitute type tsubst))
		       valtypes))
		 (uninst-mapop-type ;rho(alphas)=>(alphas=>xis)=>rho(xis)
		  (const-to-uninst-type const))
		 (uninst-maparg-type ;rho(alphas)
		  (arrow-form-to-arg-type uninst-type))
		 (uninst-arrow-types ;alphas=>xis
		  (arrow-form-to-arg-types
		   (arrow-form-to-val-type uninst-type)))
		 (bound-tvars ;alphas
		  (map arrow-form-to-arg-type uninst-arrow-types))
		 (val-tvars ;xis
		  (map arrow-form-to-val-type uninst-arrow-types))
		 (no-clash?
		  (null? (intersection
			  (append bound-tvars val-tvars)
			  (apply append
				 (map car tsubst)
				 (map type-to-tvars (map cadr tsubst)))))))
	    (if
	     no-clash?
	     (make-map-const
	      (type-substitute uninst-maparg-type tsubst)
					;(rho(alphas))theta
	      bound-tvars subst-argtypes subst-valtypes)
					;else clash: use new tvars
	     (let* ((new-bound-tvars ;betas
		     (map (lambda (x) (new-tvar)) bound-tvars))
		    (new-val-tvars ;zetas
		     (map (lambda (x) (new-tvar)) val-tvars))
		    (renaming-tsubst (make-substitution
				      (append bound-tvars val-tvars)
				      (append new-bound-tvars new-val-tvars)))
		    (new-uninst-maparg-type ;(rho(betas))
		     (type-substitute uninst-maparg-type renaming-tsubst)))
	       (make-map-const
		(type-substitute new-uninst-maparg-type tsubst)
					;(rho(betas))theta
		new-bound-tvars subst-argtypes subst-valtypes)))))
	 ((string=? "SE" name)
	  (let* ((inst-type (type-substitute uninst-type restricted-tsubst))
		 (sfinalg (arrow-form-to-arg-type inst-type)))
	    (make-const (se-at sfinalg)
			"SE" 'fixed-rules
			(make-arrow sfinalg (make-alg "boole")) empty-subst
			1 'prefix-op)))
	 ((string=? "=" name) const)
	 ((string=? "E" name) const)
	 (else (myerror "const-substitute" "fixed rule name expected" name))))
       (else (myerror "const-substitute" "unknown kind"
		      (const-to-kind const)))))))



