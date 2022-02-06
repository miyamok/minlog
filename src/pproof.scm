;; 2022-02-06.  pproof.scm
;; 11. Partial proofs
;; ==================

;; A partial proof is a proof with holes, i.e. special assumption
;; variables (called goal variables) ?_1, ?_2,... whose formulas must
;; be closed.  We assume that every goal variable ? has at most one
;; occurrence in the partial proof.  A goal is a (not necessarily
;; maximal) subproof ? x_1 ... x_n with distinct object or assumption
;; variables x_1...x_n, called its context.  Note that the goal
;; variable ? is not considered part of its context.  When
;; interactively developing a partial proof, a goal ? x_1...x_n is
;; replaced by another partial proof, with zero or more new goals
;; whose contexts are extensions of the original context x_1...x_n.
;; An object or assumption variable used later for allnc-intro or
;; impnc-intro is marked a n.c. variable in the goal.

;; To gain some flexibility when working on our goals, we do not at each
;; step of an interactive proof development traverse the partial proof
;; searching for the remaining goals, but rather keep a list of all open
;; goals together with their numbers as we go along.  We maintain a
;; global variable PPROOF-STATE, which holds a list of three elements:
;; - num-goals:
;;   an alist of entries (number goal drop-info hypname-info ignore-deco-flag)
;; - proof
;; - maxgoal

;; We include the context (for efficiency reasons) and also the ncvars
;; in a goal.

(define (make-goal-in-avar-form avar)
  (list 'proof-in-avar-form (avar-to-formula avar) avar (list avar) '()))

(define (make-goal-in-all-elim-form goal uservar)
  (let* ((formula (proof-to-formula goal))
	 (var (all-form-to-var formula))
	 (kernel (all-form-to-kernel formula))
	 (uservar-term (make-term-in-var-form uservar)))
    (list 'proof-in-all-elim-form
	  (if (equal? var (term-in-var-form-to-var uservar-term))
	      kernel
	      (formula-subst kernel var uservar-term))
	  goal
	  uservar-term
	  (append (proof-with-context-to-context goal) (list uservar))
	  (goal-to-ncvars goal))))

(define (make-goal-in-allnc-elim-form goal uservar)
  (let* ((formula (proof-to-formula goal))
	 (var (allnc-form-to-var formula))
	 (kernel (allnc-form-to-kernel formula))
	 (uservar-term (make-term-in-var-form uservar)))
    (list 'proof-in-allnc-elim-form
	  (if (equal? var (term-in-var-form-to-var uservar-term))
	      kernel
	      (formula-subst kernel var uservar-term))
	  goal
	  uservar-term
	  (append (proof-with-context-to-context goal) (list uservar))
	  (goal-to-ncvars goal))))

(define (make-goal-in-allnc-elim-form-with-new-ncvar goal uservar)
  (let* ((formula (proof-to-formula goal))
	 (var (allnc-form-to-var formula))
	 (kernel (allnc-form-to-kernel formula))
	 (uservar-term (make-term-in-var-form uservar)))
    (list 'proof-in-allnc-elim-form
	  (if (equal? var (term-in-var-form-to-var uservar-term))
	      kernel
	      (formula-subst kernel var uservar-term))
	  goal
	  uservar-term
	  (append (proof-with-context-to-context goal) (list uservar))
	  (append (goal-to-ncvars goal) (list uservar)))))

(define (make-goal-in-imp-elim-form goal avar)
  (list 'proof-in-imp-elim-form
	(imp-form-to-conclusion (proof-to-formula goal))
	goal
	(make-proof-in-avar-form avar)
	(append (proof-with-context-to-context goal) (list avar))
	(goal-to-ncvars goal)))

(define (make-goal-in-impnc-elim-form goal avar)
  (list 'proof-in-impnc-elim-form
	(impnc-form-to-conclusion (proof-to-formula goal))
	goal
	(make-proof-in-avar-form avar)
	(append (proof-with-context-to-context goal) (list avar))
	(goal-to-ncvars goal)))

(define (make-goal-in-impnc-elim-form-with-new-ncvar goal avar)
  (list 'proof-in-impnc-elim-form
	(impnc-form-to-conclusion (proof-to-formula goal))
	goal
	(make-proof-in-avar-form avar)
	(append (proof-with-context-to-context goal) (list avar))
	(append (goal-to-ncvars goal) (list avar))))

(define (mk-goal-in-elim-form goal . elim-items)
  (if
   (null? elim-items)
   goal
   (let ((formula (unfold-formula (proof-to-formula goal))))
     (case (tag formula)
       ((atom predicate ex)
	(myerror "mk-goal-in-elim-form" "applicable formula expected" formula))
       ((imp)
	(apply mk-goal-in-elim-form
	       (make-goal-in-imp-elim-form goal (car elim-items))
	       (cdr elim-items)))
       ((impnc)
	(apply mk-goal-in-elim-form
	       (make-goal-in-impnc-elim-form-with-new-ncvar
		goal (car elim-items))
	       (cdr elim-items)))
       ((all)
	(apply mk-goal-in-elim-form
	       (make-goal-in-all-elim-form goal (car elim-items))
	       (cdr elim-items)))
       ((allnc)
	(apply mk-goal-in-elim-form
	       (make-goal-in-allnc-elim-form-with-new-ncvar
		goal (car elim-items))
	       (cdr elim-items)))
       (else (myerror "mk-goal-in-elim-form" "formula expected" formula))))))

(define (goal-to-goalvar goal)
  (car (proof-with-context-to-context goal)))

(define (goal-to-context goal)
  (cdr (proof-with-context-to-context goal)))

(define (goal-to-ncvars goal)
  (case (tag goal)
    ((proof-in-avar-form
      proof-in-aconst-form
      proof-in-and-elim-left-form
      proof-in-and-elim-right-form)
     (car (cddddr goal)))
    ((proof-in-imp-intro-form
      proof-in-imp-elim-form
      proof-in-impnc-intro-form
      proof-in-impnc-elim-form
      proof-in-and-intro-form
      proof-in-all-intro-form
      proof-in-all-elim-form
      proof-in-allnc-intro-form
      proof-in-allnc-elim-form)
     (cadr (cddddr goal)))
    (else (myerror "goal-to-ncvars" "proof tag expected"
		   (tag goal)))))

(define (goal-to-formula goal) (proof-to-formula goal))

;; For interactively building proofs we will need goal=? and goal-subst

(define (goal=? proof goal)
  (and
   (or (proof-in-avar-form? proof)
       (proof-in-imp-elim-form? proof)
       (proof-in-impnc-elim-form? proof)
       (proof-in-all-elim-form? proof)
       (proof-in-allnc-elim-form? proof))
   (let ((op (proof-in-elim-form-to-final-op proof)))
     (and
      (proof-in-avar-form? op)
      (let ((goalvar (goal-to-goalvar goal)))
	(and
	 (avar=? (proof-in-avar-form-to-avar op) goalvar)
	 (let ((args (proof-in-elim-form-to-args proof))
	       (context (goal-to-context goal)))
	   (and
	    (= (length args) (length context))
	    (do ((l1 args (cdr l1))
		 (l2 context (cdr l2))
		 (res
		  #t
		  (and res
		       (or (and (proof-in-avar-form? (car l1))
				(avar=? (proof-in-avar-form-to-avar (car l1))
					(car l2)))
			   (and (term-in-var-form? (car l1))
				(equal? (term-in-var-form-to-var (car l1))
					(car l2)))))))
		((null? l1) res))))))))))

(define (goal-subst proof goal proof1)
  (case (tag proof)
    ((proof-in-avar-form)
     (if (goal=? proof goal) ;then proof1 with the original formula of proof
	 (append (list (tag proof1)
		       (proof-to-formula proof))
		 (cddr proof1))
	 proof))
    ((proof-in-aconst-form) proof)
    ((proof-in-imp-intro-form)
     (list 'proof-in-imp-intro-form
	   (proof-to-formula proof)
	   (proof-in-imp-intro-form-to-avar proof)
	   (goal-subst (proof-in-imp-intro-form-to-kernel proof) goal proof1)))
    ((proof-in-imp-elim-form)
     (if (goal=? proof goal)
	 (append (list (tag proof1)
		       (proof-to-formula proof))
		 (cddr proof1))
	 (list
	  'proof-in-imp-elim-form
	  (proof-to-formula proof)
	  (goal-subst (proof-in-imp-elim-form-to-op proof) goal proof1)
	  (goal-subst (proof-in-imp-elim-form-to-arg proof) goal proof1))))
    ((proof-in-impnc-intro-form)
     (list 'proof-in-impnc-intro-form
	   (proof-to-formula proof)
	   (proof-in-impnc-intro-form-to-avar proof)
	   (goal-subst
	    (proof-in-impnc-intro-form-to-kernel proof) goal proof1)))
    ((proof-in-impnc-elim-form)
     (if (goal=? proof goal)
	 (append (list (tag proof1)
		       (proof-to-formula proof))
		 (cddr proof1))
	 (list
	  'proof-in-impnc-elim-form
	  (proof-to-formula proof)
	  (goal-subst (proof-in-impnc-elim-form-to-op proof) goal proof1)
	  (goal-subst (proof-in-impnc-elim-form-to-arg proof) goal proof1))))
    ((proof-in-and-intro-form)
     (list 'proof-in-and-intro-form
	   (proof-to-formula proof)
	   (goal-subst (proof-in-and-intro-form-to-left proof) goal proof1)
	   (goal-subst (proof-in-and-intro-form-to-right proof) goal proof1)))
    ((proof-in-and-elim-left-form)
     (list 'proof-in-and-elim-left-form
	   (proof-to-formula proof)
	   (goal-subst
	    (proof-in-and-elim-left-form-to-kernel proof) goal proof1)))
    ((proof-in-and-elim-right-form)
     (list 'proof-in-and-elim-right-form
	   (proof-to-formula proof)
	   (goal-subst
	    (proof-in-and-elim-right-form-to-kernel proof) goal proof1)))
    ((proof-in-all-intro-form)
     (list 'proof-in-all-intro-form
	   (proof-to-formula proof)
	   (proof-in-all-intro-form-to-var proof)
	   (goal-subst (proof-in-all-intro-form-to-kernel proof) goal proof1)))
    ((proof-in-all-elim-form)
     (if (goal=? proof goal)
	 (append (list (tag proof1)
		       (proof-to-formula proof))
		 (cddr proof1))
	 (list 'proof-in-all-elim-form
	       (proof-to-formula proof)
	       (goal-subst (proof-in-all-elim-form-to-op proof) goal proof1)
	       (proof-in-all-elim-form-to-arg proof))))
    ((proof-in-allnc-intro-form)
     (list 'proof-in-allnc-intro-form
	   (proof-to-formula proof)
	   (proof-in-allnc-intro-form-to-var proof)
	   (goal-subst
	    (proof-in-allnc-intro-form-to-kernel proof) goal proof1)))
    ((proof-in-allnc-elim-form)
     (if (goal=? proof goal)
	 (append (list (tag proof1)
		       (proof-to-formula proof))
		 (cddr proof1))
	 (list 'proof-in-allnc-elim-form
	       (proof-to-formula proof)
	       (goal-subst (proof-in-allnc-elim-form-to-op proof) goal proof1)
	       (proof-in-allnc-elim-form-to-arg proof))))
    (else (myerror "goal-subst" "proof expected" proof))))

;; Initialization of global variables:

(define (make-pproof-state num-goals proof maxgoal)
  (list num-goals proof maxgoal))

(define PPROOF-STATE (make-pproof-state '() '() 1))
(define PPROOF-STATE-HISTORY '())
(define PPROOF-STATE-HISTORY-LENGTH 0)

(define (pproof-state-to-num-goals . x)
  (if (null? x) (car PPROOF-STATE) (car (car x))))

(define (pproof-state-to-proof . x)
  (if (null? x) (cadr PPROOF-STATE) (cadr (car x))))

(define (pproof-state-to-maxgoal . x)
  (if (null? x) (caddr PPROOF-STATE) (caddr (car x))))

(define (pproof-state-to-formula . x)
  (proof-to-formula (apply pproof-state-to-proof x)))

(define (current-proof) (cadr PPROOF-STATE))

(define (current-goal)
  (let ((num-goals (car PPROOF-STATE)))
    (if (null? num-goals)
	(begin (display-comment "Proof finished.")
	       (if COMMENT-STRING (newline)))
	(num-goal-to-goal (car num-goals)))))

(define (pproof-state-history-clear)
  (set! PPROOF-STATE-HISTORY '())
  (set! PPROOF-STATE-HISTORY-LENGTH 0))

(define (pproof-state-history-push state)
  (set! PPROOF-STATE-HISTORY (cons state PPROOF-STATE-HISTORY))
  (set! PPROOF-STATE-HISTORY-LENGTH (+ PPROOF-STATE-HISTORY-LENGTH 1)))

(define (pproof-state-history-head)
  (car PPROOF-STATE-HISTORY))

(define (pproof-state-history-pop n)
  (set! PPROOF-STATE-HISTORY (list-tail PPROOF-STATE-HISTORY n))
  (set! PPROOF-STATE-HISTORY-LENGTH
	(max (- PPROOF-STATE-HISTORY-LENGTH n) 0)))

;; An interactive proof begins with setting an initial goal.  If the
;; formula is not closed, the free variables are generalized.

(define (make-num-goal number goal drop-info hypname-info ignore-deco-flag)
  (list number goal drop-info hypname-info ignore-deco-flag))

(define num-goal-to-number car)
(define num-goal-to-goal cadr)
(define num-goal-to-drop-info caddr)
(define num-goal-to-hypname-info cadddr)
(define (num-goal-to-ignore-deco-flag num-goal)
  (car (cddddr num-goal)))

(define empty-drop-info '())
(define empty-hypname-info '())

(define (set-goal string-or-formula)
  (let ((formula (if (string? string-or-formula)
		     (pf string-or-formula)
		     string-or-formula)))
    (if (not (formula-form? formula))
	(myerror "set-goal" "formula expected" formula))
    (let* ((unfolded-formula (unfold-formula formula))
	   (free (formula-to-free unfolded-formula))
	   (closed-formula
	    (apply mk-all (append free (list unfolded-formula))))
	   (avar (formula-to-new-avar closed-formula DEFAULT-AVAR-NAME))
	   (goal (make-goal-in-avar-form avar))
	   (init-num-goal
	    (make-num-goal 1 goal empty-drop-info empty-hypname-info
			   (formula-of-nulltype? unfolded-formula))))
      (if (formula-with-illegal-tensor? unfolded-formula)
	  (myerror "tensor ! should be used with excl or exca only"
		   formula))
      (set! PPROOF-STATE (make-pproof-state (list init-num-goal) goal 1))
      (pproof-state-history-clear)
      (pproof-state-history-push PPROOF-STATE)
      (display-num-goal init-num-goal fold-formula))))

;; An abbreviation for (set-goal (pf .)).  (sg .) expects as argument a
;; list of strings.  This list will be concatenated and given
;; (set-goal (pf .)) as argument.

(define (sg . formulastringlist)
  (for-each (lambda (item)
	      (if (not (string? item))
		  (myerror "sg" "string expected" item)))
	    formulastringlist)
  (letrec
      ((formel
        (lambda (fm)
          (cond ((= (length fm) 0) "F")
                ((= (length fm) 1) (car fm))
                (else (formel
		       (append
			(list (string-append (car fm) (cadr fm)))
			(cddr fm))))))))
    (set-goal (pf (formel formulastringlist)))))

;; (set-totality-goal . strings) and (set-unfolded-totality-goal . strings)
;; added.  The latter is only used if unfolding is necessary.  After
;; finishing the proof the result is saved by (save-totality).

(define (set-totality-goal . pconst-names)
  (let* ((pconsts (map pconst-name-to-pconst pconst-names))
	 (terms (map make-term-in-const-form pconsts))
	 (totality-formulas (map term-to-totality-formula terms))
	 (renamed-totality-formulas (map rename-variables totality-formulas)))
    (set-goal (apply mk-and renamed-totality-formulas))))

(define (set-unfolded-totality-goal . pconst-names)
  (let* ((pconsts (map pconst-name-to-pconst pconst-names))
	 (terms (map make-term-in-const-form pconsts))
	 (unfolded-totality-formulas
	  (map term-to-unfolded-totality-formula terms))
	 (renamed-unfolded-totality-formulas
	  (map rename-variables unfolded-totality-formulas)))
    (set-goal (apply mk-and renamed-unfolded-totality-formulas))))

;; We initially supply our axioms as theorems, and also
;; AtomTrue: all boole(boole -> boole=True)
;; AtomFalse: all boole((boole -> F) -> boole=False)
;; EfqAtom: all boole(F -> boole) ;use in examples/ordinals obsolete

;; atom-true-proof moved to ets.scm because it uses EqD

;; To display a numbered goal we use display-num-goal.

(define DEFAULT-GOAL-NAME "?")

;; For display purposes a num-goal has additional entries drop-info and
;; hypname-info.

;; Format of drop-info: list of indices of hypotheses to be dropped
;; Format of hypname-info: association list index - name

(define (add-hypname-info i string hypname-info)
  (if (is-used? string '() '())
      (myerror "add-hypname-info" "new string expected" string)
      (if (assoc string (map reverse hypname-info))
	  (myerror "add-hypname-info" "already a hypname" string)
	  (cons (list i string) hypname-info))))

(define (index-and-hypname-info-to-name i hypname-info)
  (let ((info (assoc i hypname-info)))
    (if info
	(cadr info)
	(myerror "index-and-hypname-info-to-name" "no name provided for "
		 i " in " hypname-info))))

(define (name-and-hypname-info-to-index string hypname-info)
  (let ((info (assoc string (map reverse hypname-info))))
    (if info
	(cadr info)
	(myerror "name-and-hypname-info-to-index" "no index provided for "
		 string " in " hypname-info))))

(define (hypname-info-to-indices hypname-info) (map car hypname-info))
(define (hypname-info-to-names hypname-info) (map cadr hypname-info))

;; display-num-goal takes an optional argument as display function.
;; The default is (lambda (fla) (rename-variables (fold-formula fla))).

(define (display-num-goal num-goal . x)
  (let ((f (if (null? x)
	       (lambda (fla) (rename-variables (fold-formula fla)))
	       (car x))))
    (display-num-goal-aux num-goal f)))

(define COQ-GOAL-DISPLAY #t)

(define (display-num-goal-aux num-goal f)
  (if
   COMMENT-FLAG
   (let* ((number (num-goal-to-number num-goal))
	  (goal (num-goal-to-goal num-goal))
	  (drop-info (num-goal-to-drop-info num-goal))
	  (hypname-info (num-goal-to-hypname-info num-goal))
	  (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	  (indices (hypname-info-to-indices hypname-info))
	  (context (goal-to-context goal))
	  (ncvars (goal-to-ncvars goal))
	  (formula (goal-to-formula goal))
	  (goal-name (string-append DEFAULT-GOAL-NAME
				    (if ignore-deco-flag "^" "_")
				    (number-to-string number)))
	  (prefix (string-append goal-name ": ")))
     (if COQ-GOAL-DISPLAY (newline))
     (if (not COQ-GOAL-DISPLAY)
	 (begin
	   (display-comment
	    prefix
	    (pretty-print-string (string-length prefix)
				 (- PP-WIDTH (string-length COMMENT-STRING))
				 (f formula)))
	   (if (not (null? context))
	       (display " from"))
	   (newline)))
     (do ((c context (cdr c))
	  (i 1 (if (avar-form? (car c)) (+ 1 i) i))
	  (line "" line))
	 ((null? c) (if (> (string-length line) 0)
			(begin (display-comment line) (newline))))
       (if (avar-form? (car c))
	   (if (not (member i drop-info))
	       (let* ((info (member i indices))
		      (string
		       (if info
			   (index-and-hypname-info-to-name i hypname-info)
			   (number-to-string i)))
		      (ncvar? (member-wrt avar=? (car c) ncvars))
		      (nc? (formula-of-nulltype? (avar-to-formula (car c))))
		      (modstring
		       (if (and ncvar? (not nc?))
			   (string-append "{" string "}")
			   string)))
		 (set! line (string-append line "  " modstring ":"))
		 (if (> (* 3 (string-length line)) PP-WIDTH)
		     (begin (display-comment line)
			    (newline)
			    (set! line "    ")))
		 (set! line (string-append
			     line
			     (pretty-print-string
			      (string-length line)
			      (- PP-WIDTH (string-length COMMENT-STRING))
			      (f (avar-to-formula (car c))))))
		 (if (pair? (cdr c))
		     (begin (display-comment line) (newline)
			    (set! line "")))))
	   (let* ((var (car c))
		  (varstring (var-to-string var))
		  (ncvar? (member var ncvars))
		  (mod-varstring
		   (if ncvar? (string-append "{" varstring "}") varstring)))
	     (set! line (string-append line "  " mod-varstring)))))
     (if COQ-GOAL-DISPLAY
	 (begin
	   (display-comment
	    "-----------------------------------------------------------------------------")
	   (newline)
	   (display-comment
            (string-append goal-name ":"
                           (pretty-print-string
			    (+ (string-length goal-name) 1)
			    (- PP-WIDTH (string-length COMMENT-STRING))
			    (f formula))))
	   (newline) (newline))))))

(define (display-current-goal)
  (if COMMENT-FLAG
      (if (null? (pproof-state-to-num-goals))
	  (begin (display-comment "Proof finished.") (newline))
	  (begin (display-comment "The current goal is ") (newline)
		 (display-num-goal (car (pproof-state-to-num-goals)))))))

(define (display-current-goal-with-original-variables)
  (if COMMENT-FLAG
      (if (null? (pproof-state-to-num-goals))
	  (begin (display-comment "Proof finished.") (newline))
	  (begin
	    (display-comment "The current goal with renamed variables is ")
	    (newline)
	    (display-num-goal
	     (car (pproof-state-to-num-goals))
	     fold-formula)))))

(define dcgo display-current-goal-with-original-variables)

(define (display-current-goal-with-normalized-formulas)
  (if COMMENT-FLAG
      (if (null? (pproof-state-to-num-goals))
	  (begin (display-comment "Proof finished.") (newline))
	  (begin
	    (display-comment "The current goal with normalized formulas is ")
	    (newline)
	    (display-num-goal (car (pproof-state-to-num-goals))
			      normalize-formula)))))

(define dcg display-current-goal)
(define dcgnf display-current-goal-with-normalized-formulas)

(define (display-current-pproof-state . x)
  (if COMMENT-FLAG
      (let ((num-goals (apply pproof-state-to-num-goals x))
	    (formula (apply pproof-state-to-formula x)))
	(do ((c (reverse num-goals) (cdr c)))
	    ((null? c)
	     (display-comment (make-string 76 #\-)) (newline)
	     (display-comment) (dff formula) (newline))
	  (display-num-goal (car c))))))

(define (display-new-goals num-goals number)
  (if COMMENT-FLAG
      (let* ((l1 (length num-goals))
	     (l2 (length (pproof-state-to-num-goals)))
	     (new-num-goals
	      (list-head (pproof-state-to-num-goals) (- (+ l2 1) l1))))
	(if (pair? new-num-goals)
	    (begin (display-comment "ok, goal "
				    (number-to-string number)
				    " can be obtained from")
		   (for-each (lambda (g) (newline) (display-num-goal g))
			     (reverse new-num-goals)))
	    (begin
	      (display-comment "ok, " DEFAULT-GOAL-NAME "_"
			       (number-to-string number) " is proved.")
	      (if (null? (pproof-state-to-num-goals))
		  (begin (display "  Proof finished.") (newline))
		  (begin (display "  The active goal now is") (newline)
			 (display-num-goal
			  (car (pproof-state-to-num-goals))))))))))

;; normalize-goal takes optional arguments.  If there are none, the
;; goal formula and all hypotheses are normalized.  Otherwise exactly
;; those among the hypotheses and the goal formula are normalized whose
;; numbers (or names, or just #t for the goal formula) are listed as
;; additional arguments.

;; normalization of a goal is split into an internal and an external
;; procedure.  The internal one receives the parts of a pproof-state
;; and returns a new pproof-state.  The external one reads off these
;; parts from PPROOF-STATE, and updates PPROOF-STATE as well as
;; PPROOF-STATE-HISTORY.

(define (normalize-goal . ng-info)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal)))
    (set! PPROOF-STATE
	  (apply normalize-goal-intern num-goals proof maxgoal ng-info))
    (pproof-state-history-push PPROOF-STATE)
    (display-comment "ok, the normalized goal is")
    (if COMMENT-FLAG (newline))
    (display-num-goal (car (pproof-state-to-num-goals)))))

(define (normalize-goal-intern num-goals proof maxgoal . ng-info)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (indices (hypname-info-to-indices hypname-info))
	 (names (hypname-info-to-names hypname-info))
	 (goalvar (goal-to-goalvar goal))
	 (context (goal-to-context goal))
	 (normalized-context
	  (do ((l context (cdr l))
	       (i 1 (if (avar-form? (car l)) (+ 1 i) i))
	       (res '() (if (and
			     (avar-form? (car l))
			     (or (null? ng-info)
				 (member i ng-info)
				 (and (member i indices)
				      (member (index-and-hypname-info-to-name
					       i hypname-info)
					      ng-info))))
			    (cons (normalize-avar (car l)) res)
			    (cons (car l) res))))
	      ((null? l) (reverse res))))
	 (new-goal
	  (apply mk-goal-in-elim-form
		 (make-goal-in-avar-form
		  (if (or (null? ng-info)
			  (pair? (intersection ng-info (list number #t))))
		      (normalize-avar goalvar)
		      goalvar))
		 normalized-context))
	 (new-num-goal
	  (make-num-goal (+ 1 maxgoal) new-goal drop-info hypname-info
			 ignore-deco-flag)))
    (make-pproof-state (cons new-num-goal (cdr num-goals))
		       proof
		       (+ 1 maxgoal))))

(define ng normalize-goal)

;; bpe-ng (or beta-pi-eta-normalize-goal) only applies beta, pi and
;; eta normalization.

(define (beta-pi-eta-normalize-goal . ng-info)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal)))
    (set! PPROOF-STATE
	  (apply beta-pi-eta-normalize-goal-intern
		 num-goals proof maxgoal ng-info))
    (pproof-state-history-push PPROOF-STATE)
    (display-comment "ok, the normalized goal is")
    (if COMMENT-FLAG (newline))
    (display-num-goal (car (pproof-state-to-num-goals)))))

(define (beta-pi-eta-normalize-goal-intern num-goals proof maxgoal . ng-info)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (indices (hypname-info-to-indices hypname-info))
	 (names (hypname-info-to-names hypname-info))
	 (goalvar (goal-to-goalvar goal))
	 (context (goal-to-context goal))
	 (normalized-context
	  (do ((l context (cdr l))
	       (i 1 (if (avar-form? (car l)) (+ 1 i) i))
	       (res '() (if (and
			     (avar-form? (car l))
			     (or (null? ng-info)
				 (member i ng-info)
				 (and (member i indices)
				      (member (index-and-hypname-info-to-name
					       i hypname-info)
					      ng-info))))
			    (cons (beta-pi-eta-normalize-avar (car l)) res)
			    (cons (car l) res))))
	      ((null? l) (reverse res))))
	 (new-goal
	  (apply mk-goal-in-elim-form
		 (make-goal-in-avar-form
		  (if (or (null? ng-info)
			  (pair? (intersection ng-info (list number #t))))
		      (beta-pi-eta-normalize-avar goalvar)
		      goalvar))
		 normalized-context))
	 (new-num-goal
	  (make-num-goal (+ 1 maxgoal) new-goal drop-info hypname-info
			 ignore-deco-flag)))
    (make-pproof-state (cons new-num-goal (cdr num-goals))
		       proof
		       (+ 1 maxgoal))))

(define bpe-ng beta-pi-eta-normalize-goal)

;; With (assume x1 ...) we can move universally quantified variables and
;; hypotheses into the context.  The variables must be given names (known
;; to the parser as valid variable names for the given type), and the
;; hypotheses should be identified by numbers or strings.

;; Internally, assume extends the partial proof under construction by
;; intros.  To every quantifier all x (resp. allnc y) in the present
;; goal corresponds an application of an all-intro (resp. allnc-intro)
;; rule.  To every implication A -> (resp. B -->) in the present goal
;; corresponds an application of an imp-intro (resp. impnc-intro)
;; rule.  To meet the variable condition for allnc-intro and
;; impnc-intro rules, the abstracted object or assumption variable in
;; the assumed context is kept in the ncvars field.  This means that
;; it is not admitted as a computational variable in a future proof of
;; the present goal.  Therefore it is displayed in braces ({y}, {u}).

(define (assume . x-list)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal)))
    (set! PPROOF-STATE (apply assume-intern num-goals proof maxgoal x-list))
    (pproof-state-history-push PPROOF-STATE)
    (display-comment "ok, we now have the new goal ")
    (if COMMENT-FLAG (newline))
    (display-num-goal (car (pproof-state-to-num-goals)))))

(define (assume-intern num-goals proof maxgoal . x-list)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (formula (goal-to-formula goal)))
    (do ((l x-list (cdr l))
	 (nc-and-np-and-ng-and-nh
	  (list '() goal goal hypname-info ncvars)
	  (let* ((x1 (car l))
		 (nc (car nc-and-np-and-ng-and-nh)) ;new context
		 (np (cadr nc-and-np-and-ng-and-nh)) ;new proof
		 (ng (caddr nc-and-np-and-ng-and-nh)) ;new goal
		 (nh (cadddr nc-and-np-and-ng-and-nh)) ;new hypname-info
		 (nf (proof-to-formula ng)))
	    (case (tag nf)
	      ((all)
	       (let* ((var (all-form-to-var nf))
		      (type (var-to-type var))
		      (t-deg (var-to-t-deg var))
		      (userstring
		       (if (string? x1) x1
			   (myerror "assume" "string expected" x1)))
		      (userterm (pt x1))
		      (uservar (if (term-in-var-form? userterm)
				   (term-in-var-form-to-var userterm)
				   (myerror "assume" "variable expected"
					    x1)))
		      (usertype (var-to-type uservar))
		      (user-t-deg (var-to-t-deg uservar)))
		 (cond
		  ((not (equal? type usertype))
		   (myerror "assume" "variables of the same type expected"
			    uservar var))
		  ((not (equal? t-deg user-t-deg))
		   (myerror "assume" "variables of the same t-deg expected"
			    uservar var))
		  ((or (member uservar (context-to-vars context))
		       (member uservar (context-to-vars nc)))
		   (myerror "assume" "new variable expected" uservar))
		  ((not (equal? uservar var)) ;then rename
		   (let ((ng1 (make-goal-in-all-elim-form ng uservar)))
		     (list
		      (cons uservar nc)
		      (goal-subst np ng (make-proof-in-all-intro-form
					 uservar ng1))
		      ng1 nh)))
		  (else
		   (let ((ng1 (make-goal-in-all-elim-form ng var)))
		     (list
		      (cons var nc)
		      (goal-subst np ng (make-proof-in-all-intro-form var ng1))
		      ng1 nh))))))
	      ((allnc)
	       (let* ((var (allnc-form-to-var nf))
		      (type (var-to-type var))
		      (t-deg (var-to-t-deg var))
		      (userstring
		       (if (string? x1) x1
			   (myerror "assume" "string expected" x1)))
		      (userterm (pt x1))
		      (uservar (if (term-in-var-form? userterm)
				   (term-in-var-form-to-var userterm)
				   (myerror "assume" "variable expected" x1)))
		      (usertype (var-to-type uservar))
		      (user-t-deg (var-to-t-deg uservar)))
		 (cond
		  ((not (equal? type usertype))
		   (myerror "assume" "variables of the same type expected"
			    uservar var))
		  ((not (equal? t-deg user-t-deg))
		   (myerror "assume" "variables of the same t-deg expected"
			    uservar var))
		  ((or (member uservar (context-to-vars context))
		       (member uservar (context-to-vars nc)))
		   (myerror "assume" "new variable expected" uservar))
		  ((not (equal? uservar var)) ;then rename
		   (let ((ng1 (make-goal-in-allnc-elim-form-with-new-ncvar
			       ng uservar)))
		     (list
		      (cons uservar nc)
		      (goal-subst np ng (make-proof-in-allnc-intro-form
					 uservar ng1))
		      ng1 nh)))
		  (else
		   (let ((ng1 (make-goal-in-allnc-elim-form-with-new-ncvar
			       ng var)))
		     (list
		      (cons var nc)
		      (goal-subst
		       np ng (make-proof-in-allnc-intro-form var ng1))
		      ng1 nh))))))
	      ((imp)
	       (let* ((premise (imp-form-to-premise nf))
		      (name (if (string? x1) x1 DEFAULT-AVAR-NAME))
		      (avar (formula-to-new-avar premise name))
		      (ng1 (make-goal-in-imp-elim-form ng avar))
		      (hypnumber (+ (length (context-to-avars context))
				    (length (context-to-avars nc))))
		      (nh1 (if (string? x1)
			       (add-hypname-info (+ 1 hypnumber) x1 nh)
			       nh)))
		 (list
		  (cons avar nc)
		  (goal-subst np ng (make-proof-in-imp-intro-form avar ng1))
		  ng1 nh1)))
	      ((impnc)
	       (let* ((premise (impnc-form-to-premise nf))
		      (name (if (string? x1) x1 DEFAULT-AVAR-NAME))
		      (avar (formula-to-new-avar premise name))
		      (ng1 (make-goal-in-impnc-elim-form-with-new-ncvar
			    ng avar))
		      (hypnumber (+ (length (context-to-avars context))
				    (length (context-to-avars nc))))
		      (nh1 (if (string? x1)
			       (add-hypname-info (+ 1 hypnumber) x1 nh)
			       nh)))
		 (list
		  (cons avar nc)
		  (goal-subst np ng (make-proof-in-impnc-intro-form avar ng1))
		  ng1 nh1)))
	      ((exca)
	       (let* ((vars (exca-form-to-vars nf))
		      (kernel (exca-form-to-kernel nf))
		      (premise
		       (apply mk-all
			      (append vars
				      (list
				       (apply mk-imp
					      (append
					       (tensor-form-to-parts
						kernel)
					       (list falsity)))))))
		      (name (if (string? x1) x1 DEFAULT-AVAR-NAME))
		      (avar (formula-to-new-avar premise name))
		      (ng1 (make-goal-in-imp-elim-form ng avar))
		      (hypnumber (+ (length (context-to-avars context))
				    (length (context-to-avars nc))))
		      (nh1 (if (string? x1)
			       (add-hypname-info (+ 1 hypnumber) x1 nh)
			       nh)))
		 (list
		  (cons avar nc)
		  (goal-subst np ng (make-proof-in-imp-intro-form avar ng1))
		  ng1 nh1)))
	      ((excl)
	       (let* ((vars (excl-form-to-vars nf))
		      (kernel (excl-form-to-kernel nf))
		      (premise
		       (apply mk-all
			      (append vars
				      (list
				       (apply mk-imp
					      (append
					       (tensor-form-to-parts
						kernel)
					       (list falsity-log)))))))
		      (name (if (string? x1) x1 DEFAULT-AVAR-NAME))
		      (avar (formula-to-new-avar premise name))
		      (ng1 (make-goal-in-imp-elim-form ng avar))
		      (hypnumber (+ (length (context-to-avars context))
				    (length (context-to-avars nc))))
		      (nh1 (if (string? x1)
			       (add-hypname-info (+ 1 hypnumber) x1 nh)
			       nh)))
		 (list
		  (cons avar nc)
		  (goal-subst np ng (make-proof-in-imp-intro-form avar ng1))
		  ng1 nh1)))
	      ((atom)
	       (cond
		((term=?
		  (make-term-in-const-form
		   (pconst-name-to-pconst "ImpConst"))
		  (term-in-app-form-to-final-op (atom-form-to-kernel nf)))
		 (let* ((kernel (atom-form-to-kernel nf))
			(args (term-in-app-form-to-args kernel))
			(arg1 (if (= 2 (length args))
				  (car args)
				  (myerror "two args expected")))
			(arg2 (cadr args))
			(prem (make-atomic-formula arg1))
			(concl (make-atomic-formula arg2))
			(name (if (string? x1) x1 DEFAULT-AVAR-NAME))
			(avar (formula-to-new-avar prem name))
			(hypnumber (+ (length (context-to-avars context))
				      (length (context-to-avars nc))))
			(nh1 (if (string? x1)
				 (add-hypname-info (+ 1 hypnumber) x1 nh)
				 nh))
			(context (goal-to-context ng))
			(ncvars (goal-to-ncvars ng))
			(new-goalformula
			 (context-and-ncvars-and-formula-to-formula
			  (append context (list avar)) ncvars concl))
			(new-goalvar (formula-to-new-avar
				      new-goalformula DEFAULT-AVAR-NAME))
			(ng1 (apply mk-goal-in-elim-form
				    (make-goal-in-avar-form new-goalvar)
				    (append context (list avar)))))
		   (list
		    (cons avar nc)
		    (goal-subst np ng (mk-proof-in-elim-form
				       imp-to-atom-proof
				       arg1 arg2 (make-proof-in-imp-intro-form
						  avar ng1)))
		    ng1 nh1)))
		(else (myerror "assume" "unexpected atom" nf))))
	      (else (myerror "assume" "formula"
			     nf "not of the appropriate form to assume"
			     x1))))))
	((null? l)
	 (let* ((np (cadr nc-and-np-and-ng-and-nh))
		(ng (caddr nc-and-np-and-ng-and-nh))
		(nh (cadddr nc-and-np-and-ng-and-nh))
		(new-num-goal (make-num-goal (+ 1 maxgoal) ng drop-info nh
					     ignore-deco-flag)))
	   (make-pproof-state (cons new-num-goal (cdr num-goals))
			      (goal-subst proof goal np)
			      (+ 1 maxgoal)))))))

;; In the following definition of use x is one of the following.
;; - A number or string identifying a hypothesis from the context.
;; - A formula with free variables from the context, generating a new goal.
;; - The name of a theorem or global assumption.
;; - A closed proof.
;; It is checked whether some final part of the used formula has the
;; form of (or "matches") the goal, where if (i) x determines a
;; hypothesis or is the formula for a new goal, then all its free
;; topvars are rigid, and if (ii) x determines a closed proof, then all
;; its (implicitely generalized) tpvars are flexible, except the pvar
;; bot from falsity-log.  elab-path-and-terms is a list consisting of
;; symbols left or right, giving directions in case the used formula
;; contains conjunctions, and of terms/cterms to be substituted for the
;; variables that cannot be instantiated by matching.  Matching is done
;; for type and object variables first (via match), and in case this
;; fails with huet-match next.  use2 only applies huet-match

(define (use x . elab-path-and-terms)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply use-intern num-goals proof maxgoal x elab-path-and-terms))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (use2 x . elab-path-and-terms)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (if ;x determines a closed proof
     (or (and (string? x) (assoc x THEOREMS))
	 (and (string? x) (assoc x GLOBAL-ASSUMPTIONS))
	 (proof-form? x))
     (let ((closed-proof (if (proof-form? x) x (thm-or-ga-name-to-proof x))))
       (set! PPROOF-STATE
	     (apply use2-closed-proof-intern
		    num-goals proof maxgoal closed-proof elab-path-and-terms))
       (pproof-state-history-push PPROOF-STATE)
       (display-new-goals num-goals number))
					;else x determines hyp or a new goal
     (begin (set! PPROOF-STATE
		  (apply use2-hyp-or-new-goal-intern
			 num-goals proof maxgoal x elab-path-and-terms))
	    (pproof-state-history-push PPROOF-STATE)
	    (display-new-goals num-goals number)))))

(define (use-intern num-goals proof maxgoal x . elab-path-and-terms)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (goal-formula (goal-to-formula goal))
	 (leaf (if (formula-form? x)
		   (context-and-ncvars-and-formula-to-new-goal
		    context ncvars x)
		   (hyp-info-to-leaf num-goal x)))
 	 (used-formula
	  (unfold-formula (if (formula-form? x) x (proof-to-formula leaf))))
	 (closed-proof (cond
			((and (string? x)
			      (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS)))
			 (thm-or-ga-name-to-proof x))
			((proof-form? x) x)
			(else #f)))
	 (sig-tvars (context-to-tvars context))
	 (sig-vars (context-to-vars context))
	 (ignore-deco-flag-and-sig-tovars
	  (cons ignore-deco-flag (append sig-tvars sig-vars)))
	 (elab-path (do ((l elab-path-and-terms (cdr l))
			 (res '() (if (memq (car l) '(left right))
				      (cons (car l) res)
				      res)))
			((null? l) (reverse res))))
	 (tvars (if closed-proof
		    (set-minus (proof-to-tvars closed-proof) sig-tvars)
		    '()))
	 (x-list-and-vars-and-alist-and-tosubst1
	  (apply
	   fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data
	   used-formula ignore-deco-flag-and-sig-tovars goal-formula
	   elab-path))
	 (nfla-and-ngoal
	  (if x-list-and-vars-and-alist-and-tosubst1
	      #f ;no normalization needed
	      (list (normalize-formula used-formula)
		    (normalize-formula goal-formula))))
	 (x-list-and-vars-and-alist-and-tosubst
	  (or x-list-and-vars-and-alist-and-tosubst1
	      (apply
	       fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data
	       (car nfla-and-ngoal)
	       ignore-deco-flag-and-sig-tovars
	       (cadr nfla-and-ngoal)
	       elab-path))))
    (if
     x-list-and-vars-and-alist-and-tosubst ;succeed with first-order-match
     (let* ((x-list (car x-list-and-vars-and-alist-and-tosubst))
	    (uninst-vars (cadr x-list-and-vars-and-alist-and-tosubst))
	    (uninst-to-old-vars-alist ;for error messages only
	     (caddr x-list-and-vars-and-alist-and-tosubst))
	    (tosubst (cadddr x-list-and-vars-and-alist-and-tosubst))
	    (terms (list-transform-positive elab-path-and-terms
		     term-form?))
	    (subst (if (<= (length uninst-vars) (length terms))
		       (map list
			    uninst-vars (list-head terms (length uninst-vars)))
		       empty-subst))
	    (subst-x-list (map (lambda (x) (if (term-form? x)
					       (term-substitute x subst)
					       x))
			       x-list))
	    (types
	     (let ((tsubst (list-transform-positive tosubst
			     (lambda (x) (tvar-form? (car x))))))
	       (if (and (or (and (string? x) (assoc x THEOREMS))
			    (and (string? x) (assoc x GLOBAL-ASSUMPTIONS))
			    (proof-form? x))
			(pair? tsubst)) ;else '()
		   (let* ((proof (if (proof-form? x) x
				     (thm-or-ga-name-to-proof x)))
			  (fla (proof-to-formula proof))
			  (tvars (formula-to-tvars fla)))
		     (map (lambda (tvar) (type-substitute tvar tsubst))
			  tvars))
		   '()))))
       (if (> (length uninst-vars) (length terms))
	   (apply myerror
		  "use" "more terms expected, to be substituted for"
		  (map (lambda (x) (cadr (assoc x uninst-to-old-vars-alist)))
		       (list-tail uninst-vars (length terms)))))
       (if (and COMMENT-FLAG (< (length uninst-vars) (length terms)))
	   (begin (comment "warning: superfluous terms")
		  (for-each comment
			    (map term-to-string
				 (list-tail terms (length uninst-vars))))))
       (apply use-with-intern
	      num-goals proof maxgoal x
	      (append types subst-x-list)))
					;else try 2nd order matching
     (if closed-proof
	 (apply use2-closed-proof-intern
		num-goals proof maxgoal closed-proof elab-path-and-terms)
	 (apply use2-hyp-or-new-goal-intern
		num-goals proof maxgoal x elab-path-and-terms)))))

(define (use2-hyp-or-new-goal-intern
	 num-goals proof maxgoal x . elab-path-and-terms)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (goal-formula (goal-to-formula goal))
	 (leaf (if (formula-form? x)
		   (context-and-ncvars-and-formula-to-new-goal
		    context ncvars x)
		   (hyp-info-to-leaf num-goal x)))
 	 (used-formula
	  (unfold-formula (if (formula-form? x) x (proof-to-formula leaf))))
	 (sig-vars (context-to-vars context))
	 (sig-topvars (append (formula-to-tvars used-formula)
			      (union sig-vars (formula-to-free used-formula))
			      (union (list falsity-log-pvar)
				     (formula-to-pvars used-formula))))
	 (elab-path (do ((l elab-path-and-terms (cdr l))
			 (res '() (if (memq (car l) '(left right))
				      (cons (car l) res)
				      res)))
			((null? l) (reverse res))))
	 (x-list-and-vars-and-alist-and-subst1
	  (apply fla-and-sig-topvars-and-goal-fla-to-use2-data
		 used-formula sig-topvars goal-formula elab-path))
	 (x-list-and-vars-and-alist-and-subst
	  (or x-list-and-vars-and-alist-and-subst1
	      (apply fla-and-sig-topvars-and-goal-fla-to-use2-data
		     (normalize-formula used-formula)
		     sig-topvars
		     (normalize-formula goal-formula)
		     elab-path))))
    (if
     x-list-and-vars-and-alist-and-subst ;match succeeded
     (let* ((x-list (car x-list-and-vars-and-alist-and-subst))
	    (uninst-vars (cadr x-list-and-vars-and-alist-and-subst))
	    (uninst-to-old-vars-alist ;for error messages only
	     (caddr x-list-and-vars-and-alist-and-subst))
	    (subst (cadddr x-list-and-vars-and-alist-and-subst))
	    (user-terms
	     (list-transform-positive elab-path-and-terms term-form?))
	    (user-subst (if (<= (length uninst-vars) (length user-terms))
			    (map list
				 uninst-vars
				 (list-head user-terms (length uninst-vars)))
			    empty-subst))
	    (subst-x-list (map (lambda (x) (if (term-form? x)
					       (term-substitute x user-subst)
					       x))
			       x-list)))

       (if (> (length uninst-vars) (length user-terms))
	   (apply myerror
		  "use2-hyp-or-new-goal-intern"
		  "more terms expected, to be substituted for"
		  (map (lambda (var)
			 (let ((info (assoc var uninst-to-old-vars-alist)))
			   (if info (cadr info) var)))
		       (list-tail uninst-vars (length user-terms)))))
       (if (and COMMENT-FLAG (< (length uninst-vars) (length user-terms)))
	   (begin
	     (comment "warning: superfluous terms")
	     (for-each comment
		       (map term-to-string
			    (list-tail user-terms (length uninst-vars))))))
       (apply use-with-intern
	      num-goals proof maxgoal x subst-x-list))
					;else give up
     (let ((normalized-goal-formula (normalize-formula goal-formula)))
       (if (formula=? goal-formula normalized-goal-formula)
	   (myerror "use2-hyp-or-new-goal-intern" "unusable formula"
		    used-formula
		    "for goal formula"
		    goal-formula)
	   (myerror "use2-hyp-or-new-goal-intern" "unusable formula"
		    used-formula
		    "for goal formula"
		    goal-formula
		    "as well as normalized goal formula"
		    normalized-goal-formula))))))

(define (use2-closed-proof-intern
	 num-goals proof maxgoal closed-proof . elab-path-and-terms)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (goal-formula (goal-to-formula goal))
	 (sig-vars (context-to-vars context))
	 (sig-topvars (append sig-vars (list falsity-log-pvar)))
	 (tvars (proof-to-tvars closed-proof))
	 (goal-tvars (formula-to-tvars goal-formula))
	 (clash-tvars (intersection tvars goal-tvars))
	 (rest-tvars (set-minus tvars clash-tvars))
	 (new-clash-tvars (map (lambda (x) (new-tvar)) clash-tvars))
	 (renamed-tvars (append new-clash-tvars rest-tvars))
	 (renaming-tsubst (map list clash-tvars new-clash-tvars))
	 (pvars (proof-to-pvars closed-proof))
	 (goal-pvars (formula-to-pvars goal-formula))
	 (critical-pvars ;whose arities contain goal-tvars
	  (list-transform-positive pvars
	    (lambda (pvar)
	      (let* ((arity (pvar-to-arity pvar))
		     (types (arity-to-types arity))
		     (arity-tvars (apply union (map type-to-tvars types))))
		(pair? (intersection arity-tvars goal-tvars))))))
	 (clash-pvars (intersection (set-minus pvars critical-pvars)
				    goal-pvars))
	 (rest-pvars (set-minus pvars (append critical-pvars clash-pvars)))
	 (critical-arities (map pvar-to-arity critical-pvars))
	 (new-critical-arities
	  (map (lambda (arity)
		 (apply make-arity
			(map (lambda (type)
			       (type-substitute type renaming-tsubst))
			     (arity-to-types arity))))
	       critical-arities))
	 (new-critical-pvars
	  (map arity-to-new-pvar new-critical-arities critical-pvars))
	 (new-clash-pvars (map arity-to-new-pvar
			       (map pvar-to-arity clash-pvars) clash-pvars))
	 (new-critical-pvar-cterms
	  (map predicate-to-cterm new-critical-pvars))
	 (new-clash-pvar-cterms (map predicate-to-cterm new-clash-pvars))
	 (renaming-psubst
	  (append (map list critical-pvars new-critical-pvar-cterms)
		  (map list clash-pvars new-clash-pvar-cterms)))
	 (renaming-tpsubst (append renaming-tsubst renaming-psubst))
	 (renamed-closed-proof ;to let huet-match work correctly if clash
	  (if (pair? renaming-tpsubst)
	      (proof-substitute closed-proof renaming-tpsubst)
	      closed-proof))
	 (renamed-pvars
	  (append new-critical-pvars new-clash-pvars rest-pvars))
	 (renamed-used-formula (proof-to-formula renamed-closed-proof))
	 (elab-path (do ((l elab-path-and-terms (cdr l))
			 (res '() (if (memq (car l) '(left right))
				      (cons (car l) res)
				      res)))
			((null? l) (reverse res))))
	 (x-list-and-vars-and-alist-and-topsubst1
	  (apply fla-and-sig-topvars-and-goal-fla-to-use2-data
		 renamed-used-formula sig-topvars goal-formula elab-path))
	 (x-list-and-vars-and-alist-and-topsubst
	  (or x-list-and-vars-and-alist-and-topsubst1
	      (apply fla-and-sig-topvars-and-goal-fla-to-use2-data
		     (normalize-formula renamed-used-formula)
		     sig-topvars
		     (normalize-formula goal-formula)
		     elab-path))))
    (if
     x-list-and-vars-and-alist-and-topsubst ;match succeeded
     (let* ((x-list (car x-list-and-vars-and-alist-and-topsubst))
	    (uninst-vars (cadr x-list-and-vars-and-alist-and-topsubst))
	    (uninst-to-old-vars-alist ;for error messages only
	     (caddr x-list-and-vars-and-alist-and-topsubst))
	    (topsubst (cadddr x-list-and-vars-and-alist-and-topsubst))
	    (uninst-pvars
	     (list-transform-positive renamed-pvars
	       (lambda (pvar) (and (not (assoc pvar topsubst))
				   (not (member pvar sig-topvars))))))
	    (renamed-to-old-pvars-alist ;for error messages only
	     (map list renamed-pvars pvars))
	    (user-terms
	     (list-transform-positive elab-path-and-terms term-form?))
	    (user-cterms
	     (list-transform-positive elab-path-and-terms cterm-form?))
	    (user-subst (if (<= (length uninst-vars) (length user-terms))
			    (map list
				 uninst-vars
				 (list-head user-terms (length uninst-vars)))
			    empty-subst))
	    (subst-x-list (map (lambda (x) (if (term-form? x)
					       (term-substitute x user-subst)
					       x))
			       x-list))
	    (types (let ((tsubst (list-transform-positive topsubst
				   (lambda (x) (tvar-form? (car x))))))
		     (if (pair? tsubst) ;else '()
			 (map (lambda (tvar) (type-substitute tvar tsubst))
			      renamed-tvars)
			 '())))
	    (cterms
	     (let* ((user-psubst-length
		     (min (length uninst-pvars) (length user-cterms)))
		    (user-psubst
		     (map list
			  (list-head uninst-pvars user-psubst-length)
			  (list-head user-cterms user-psubst-length)))
		    (psubst-and-user-psubst
		     (append (list-transform-positive topsubst
			       (lambda (x) (pvar-form? (car x))))
			     user-psubst)))
	       (if (pair? psubst-and-user-psubst) ;else '()
		   (map (lambda (pvar)
			  (let ((info (assoc pvar psubst-and-user-psubst)))
			    (if info (cadr info)
				(predicate-to-cterm pvar))))
			renamed-pvars)
		   '()))))
       (if (> (length uninst-pvars) (length user-cterms))
	   (apply myerror
		  "use2-closed-proof-intern"
		  "more cterms expected, to be substituted for"
		  (map (lambda (pvar)
			 (let ((info (assoc pvar renamed-to-old-pvars-alist)))
			   (if info
			       (pvar-to-string (cadr info))
			       (pvar-to-string pvar))))
		       (list-tail uninst-pvars (length user-cterms)))))
       (if (> (length uninst-vars) (length user-terms))
	   (apply
	    myerror
	    "use2-closed-proof-intern"
	    "more terms expected, to be substituted for"
	    (map (lambda (var)
		   (let ((info (assoc var uninst-to-old-vars-alist)))
		     (if info (cadr info) var)))
		 (list-tail uninst-vars (length user-terms)))))
       (if (and COMMENT-FLAG (< (length uninst-pvars) (length user-cterms)))
	   (begin
	     (comment "warning: superfluous cterms")
	     (for-each
	      comment
	      (map cterm-to-string
		   (list-tail user-cterms (length uninst-pvars))))))
       (if (and COMMENT-FLAG (< (length uninst-vars) (length user-terms)))
	   (begin
	     (comment "warning: superfluous terms")
	     (for-each comment
		       (map term-to-string
			    (list-tail user-terms (length uninst-vars))))))
       (apply use-with-intern
	      num-goals proof maxgoal renamed-closed-proof
	      (append types cterms subst-x-list))) ;else give up
     (let ((normalized-goal-formula (normalize-formula goal-formula)))
       (if (formula=? goal-formula normalized-goal-formula)
	   (myerror "use2-closed-proof-intern" "unusable formula"
		    renamed-used-formula
		    "for goal formula"
		    goal-formula)
	   (myerror "use2-closed-proof-intern" "unusable formula"
		    renamed-used-formula
		    "for goal formula"
		    goal-formula
		    "as well as normalized goal formula"
		    normalized-goal-formula))))))

;; fla-and-sig-topvars-and-goal-fla-to-use2-data is #f if the
;; used-formula is not a pattern for the goal formula.  Otherwise the
;; following data are returned: (1) the arguments x-list for the
;; hypothesis x, that produce via substitution the goal formula, (2)
;; vars (from x-list) whose instantiations cannot be inferred, hence
;; need to be provided by the user, (3) an association list storing the
;; renaming of vars done, and (4) a topsubst, that turns the used-formula
;; into the goal formula.  Notice that we only build an association
;; list for object vars.  For pvars this is done in use2-intern.

(define (fla-and-sig-topvars-and-goal-fla-to-use2-data
	 used-formula sig-topvars goal-formula . elab-path)
  (let ((match-res (apply huet-match
			  used-formula
			  goal-formula
			  #f ;for ignore-deco-flag
			  sig-topvars)))
    (if
     match-res
     (list '() '() '() match-res)
     (case (tag used-formula)
       ((predicate ex) #f)
       ((imp)
	(let* ((concl (imp-form-to-conclusion used-formula))
	       (prev (apply fla-and-sig-topvars-and-goal-fla-to-use2-data
			    concl sig-topvars goal-formula elab-path)))
	  (if (not prev)
	      #f
	      (let* ((x-list (car prev))
		     (vars (cadr prev))
		     (vars-to-old-vars-alist (caddr prev))
		     (topsubst (cadddr prev)))
		(list (cons DEFAULT-GOAL-NAME x-list) vars
		      vars-to-old-vars-alist topsubst)))))
       ((impnc)
	(let* ((concl (impnc-form-to-conclusion used-formula))
	       (prev (apply
		      fla-and-sig-topvars-and-goal-fla-to-use2-data
		      concl sig-topvars goal-formula elab-path)))
	  (if (not prev)
	      #f
	      (let* ((x-list (car prev))
		     (vars (cadr prev))
		     (vars-to-old-vars-alist (caddr prev))
		     (topsubst (cadddr prev)))
		(list (cons DEFAULT-GOAL-NAME x-list) vars
		      vars-to-old-vars-alist topsubst)))))
       ((all)
	(let* ((var (all-form-to-var used-formula))
	       (kernel (all-form-to-kernel used-formula))
	       (new-var (var-to-new-var var))
	       (new-kernel
		(formula-subst kernel var (make-term-in-var-form new-var)))
	       (prev (apply
		      fla-and-sig-topvars-and-goal-fla-to-use2-data
		      new-kernel sig-topvars goal-formula elab-path)))
	  (if (not prev)
	      #f
	      (let* ((x-list (car prev))
		     (vars (cadr prev))
		     (vars-to-old-vars-alist (caddr prev))
		     (topsubst (cadddr prev))
		     (info (assoc new-var topsubst)))
		(if
		 info ;instance found by matching
		 (list ;insert instance into x-list
		  (cons (cadr info) x-list)
		  vars
		  (cons (list new-var var) vars-to-old-vars-alist)
		  topsubst)
		 (list ;else insert new-var into x-list, and new-var to vars
		  (cons (make-term-in-var-form new-var) x-list)
		  (cons new-var vars)
		  (cons (list new-var var) vars-to-old-vars-alist)
		  topsubst))))))
       ((allnc)
	(let* ((var (allnc-form-to-var used-formula))
	       (kernel (allnc-form-to-kernel used-formula))
	       (new-var (var-to-new-var var))
	       (new-kernel
		(formula-subst kernel var (make-term-in-var-form new-var)))
	       (prev (apply fla-and-sig-topvars-and-goal-fla-to-use2-data
			    new-kernel sig-topvars goal-formula elab-path)))
	  (if (not prev)
	      #f
	      (let* ((x-list (car prev))
		     (vars (cadr prev))
		     (vars-to-old-vars-alist (caddr prev))
		     (topsubst (cadddr prev))
		     (info (assoc new-var topsubst)))
		(if
		 info ;instance found by matching
		 (list ;insert instance into x-list
		  (cons (cadr info) x-list)
		  vars
		  (cons (list new-var var) vars-to-old-vars-alist)
		  topsubst)
		 (list ;else insert new-var into x-list, and new-var to vars
		  (cons (make-term-in-var-form new-var) x-list)
		  (cons new-var vars)
		  (cons (list new-var var) vars-to-old-vars-alist)
		  topsubst))))))
       ((and)
	(let ((left-conjunct (and-form-to-left used-formula))
	      (right-conjunct (and-form-to-right used-formula)))
	  (if
	   (pair? elab-path)
	   (let* ((direction (car elab-path))
		  (conjunct (cond ((eq? 'left direction) left-conjunct)
				  ((eq? 'right direction) right-conjunct)
				  (else (myerror "left or right expected"
						 direction))))
		  (prev (apply
			 fla-and-sig-topvars-and-goal-fla-to-use2-data
			 conjunct sig-topvars goal-formula (cdr elab-path))))
	     (if (not prev)
		 #f
		 (let* ((x-list (car prev))
			(vars (cadr prev))
			(vars-to-old-vars-alist (caddr prev))
			(topsubst (cadddr prev)))
		   (list (cons direction x-list) vars
			 vars-to-old-vars-alist topsubst))))
	   (let ((prev1 (fla-and-sig-topvars-and-goal-fla-to-use2-data
			 left-conjunct sig-topvars goal-formula)))
	     (if
	      prev1
	      (let* ((x-list (car prev1))
		     (vars (cadr prev1))
		     (vars-to-old-vars-alist (caddr prev1))
		     (topsubst (cadddr prev1)))
		(list (cons 'left x-list) vars
		      vars-to-old-vars-alist topsubst))
	      (let ((prev2 (fla-and-sig-topvars-and-goal-fla-to-use2-data
			    right-conjunct sig-topvars goal-formula)))
		(if prev2
		    (let* ((x-list (car prev2))
			   (vars (cadr prev2))
			   (vars-to-old-vars-alist (caddr prev2))
			   (topsubst (cadddr prev2)))
		      (list (cons 'right x-list) vars
			    vars-to-old-vars-alist topsubst))
		    #f)))))))
       ((atom)
	(cond
	 ((term=? (make-term-in-const-form
		   (pconst-name-to-pconst "ImpConst"))
		  (term-in-app-form-to-final-op (atom-form-to-kernel
						 used-formula)))
	  (let* ((kernel (atom-form-to-kernel used-formula))
		 (args (term-in-app-form-to-args kernel))
		 (arg1 (if (= 2 (length args))
			   (car args)
			   (myerror "two args expected")))
		 (arg2 (cadr args))
		 (prem (make-atomic-formula arg1))
		 (concl (make-atomic-formula arg2))
		 (prev (apply
			fla-and-sig-topvars-and-goal-fla-to-use2-data
			concl sig-topvars goal-formulaelab-path)))
	    (if (not prev)
		#f
		(let* ((x-list (car prev))
		       (vars (cadr prev))
		       (vars-to-old-vars-alist (caddr prev))
		       (topsubst (cadddr prev)))
		  (list (cons DEFAULT-GOAL-NAME x-list) vars
			vars-to-old-vars-alist topsubst)))))
	 ((term=?
	   (make-term-in-const-form
	    (pconst-name-to-pconst "AndConst"))
	   (term-in-app-form-to-final-op (atom-form-to-kernel
					  used-formula)))
	  (let* ((kernel (atom-form-to-kernel used-formula))
		 (args (term-in-app-form-to-args kernel))
		 (left-arg (if (= 2 (length args))
			       (car args)
			       (myerror "two args expected")))
		 (right-arg (cadr args))
		 (left-conjunct (make-atomic-formula left-arg))
		 (right-conjunct (make-atomic-formula right-arg)))
	    (if
	     (pair? elab-path)
	     (let* ((direction (car elab-path))
		    (conjunct (cond ((eq? 'left direction) left-conjunct)
				    ((eq? 'right direction) right-conjunct)
				    (else (myerror "left or right expected"
						   direction))))
		    (prev (apply
			   fla-and-sig-topvars-and-goal-fla-to-use2-data
			   conjunct sig-topvars goal-formula (cdr elab-path))))
	       (if (not prev)
		   #f
		   (let* ((x-list (car prev))
			  (vars (cadr prev))
			  (vars-to-old-vars-alist (caddr prev))
			  (topsubst (cadddr prev)))
		     (list (cons direction x-list) vars
			   vars-to-old-vars-alist topsubst))))
	     (let ((prev1 (fla-and-sig-topvars-and-goal-fla-to-use2-data
			   left-conjunct sig-topvars goal-formula)))
	       (if
		prev1
		(let* ((x-list (car prev1))
		       (vars (cadr prev1))
		       (vars-to-old-vars-alist (caddr prev1))
		       (topsubst (cadddr prev1)))
		  (list (cons 'left x-list) vars
			vars-to-old-vars-alist topsubst))
		(let ((prev2 (fla-and-sig-topvars-and-goal-fla-to-use2-data
			      right-conjunct sig-topvars goal-formula)))
		  (if prev2
		      (let* ((x-list (car prev2))
			     (vars (cadr prev2))
			     (vars-to-old-vars-alist (caddr prev2))
			     (topsubst (cadddr prev2)))
			(list (cons 'right x-list) vars
			      vars-to-old-vars-alist topsubst))
		      #f)))))))
	 (else #f)))
       (else (myerror "fla-and-sig-topvars-and-goal-fla-to-use2-data"
		      "formula expected"
		      used-formula))))))

;; fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data is
;; #f if the used-formula is not a pattern for the goal formula.
;; Otherwise the following data are returned: (1) the arguments x-list
;; for the hypothesis x, that produce via instantiation the goal
;; formula, (2) vars (from x-list) whose instantiations cannot be
;; inferred, hence need to be provided by the user, (3) an association
;; list storing the renaming of vars done, and (4) a type substitution
;; plus object instantiation, that turns the used-formula into the
;; goal formula.

(define (fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data
	 used-formula ignore-deco-flag-and-sig-tovars goal-formula . elab-path)
  (let ((match-res
	 (apply match
		used-formula goal-formula ignore-deco-flag-and-sig-tovars)))
    (if
     match-res
     (list '() '() '() match-res)
     (cond
      ((or (prime-predicate-form? used-formula)
	   (ord-form? used-formula)
	   (orl-form? used-formula)
	   (orr-form? used-formula)
	   (oru-form? used-formula)
	   (ornc-form? used-formula)
	   (ex-form? used-formula)
	   (exd-form? used-formula)
	   (exl-form? used-formula)
	   (exr-form? used-formula)
	   (exnc-form? used-formula)
	   (exdt-form? used-formula)
	   (exlt-form? used-formula)
	   (exrt-form? used-formula)
	   (exnct-form? used-formula)) #f)
      ((or (imp-form? used-formula) (impnc-form? used-formula))
       (let* ((concl (bicon-form-to-right used-formula))
	      (prev
	       (apply
		fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data
		concl ignore-deco-flag-and-sig-tovars goal-formula elab-path)))
	 (if (not prev)
	     #f
	     (let* ((x-list (car prev))
		    (vars (cadr prev))
		    (vars-to-old-vars-alist (caddr prev))
		    (toinst (cadddr prev)))
	       (list (cons DEFAULT-GOAL-NAME x-list) vars
		     vars-to-old-vars-alist toinst)))))
      ((or (all-form? used-formula) (allnc-form? used-formula))
       (let* ((var (car (quant-form-to-vars used-formula)))
	      (kernel (quant-form-to-kernel used-formula))
	      (new-var (var-to-new-var var))
	      (new-kernel
	       (formula-subst kernel var (make-term-in-var-form new-var)))
	      (prev
	       (apply
		fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data
		new-kernel
		ignore-deco-flag-and-sig-tovars goal-formula elab-path)))
	 (if (not prev)
	     #f
	     (let* ((x-list (car prev))
		    (vars (cadr prev))
		    (vars-to-old-vars-alist (caddr prev))
		    (toinst (cadddr prev))
		    (info (assoc new-var toinst)))
	       (if
		info ;instance found by matching
		(list ;insert instance into x-list
		 (cons (cadr info) x-list)
		 vars
		 (cons (list new-var var) vars-to-old-vars-alist)
		 toinst)
		(list ;else insert new-var into x-list, and new-var to vars
		 (cons (make-term-in-var-form new-var) x-list)
		 (cons new-var vars)
		 (cons (list new-var var) vars-to-old-vars-alist)
		 toinst))))))
      ((and (bicon-form? used-formula)
	    (memq (bicon-form-to-bicon used-formula)
		  '(and andd andl andr andnc)))
       (let ((left-conjunct (bicon-form-to-left used-formula))
	     (right-conjunct (bicon-form-to-right used-formula)))
	 (if
	  (pair? elab-path)
	  (let* ((direction (car elab-path))
		 (conjunct (cond ((eq? 'left direction) left-conjunct)
				 ((eq? 'right direction) right-conjunct)
				 (else (myerror "left or right expected"
						direction))))
		 (prev
		  (apply
		   fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data
		   conjunct ignore-deco-flag-and-sig-tovars goal-formula
		   (cdr elab-path))))
	    (if (not prev)
		#f
		(let* ((x-list (car prev))
		       (vars (cadr prev))
		       (vars-to-old-vars-alist (caddr prev))
		       (toinst (cadddr prev)))
		  (list (cons direction x-list) vars
			vars-to-old-vars-alist toinst))))
	  (let ((prev1
		 (fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data
		  left-conjunct ignore-deco-flag-and-sig-tovars goal-formula)))
	    (if
	     prev1
	     (let* ((x-list (car prev1))
		    (vars (cadr prev1))
		    (vars-to-old-vars-alist (caddr prev1))
		    (toinst (cadddr prev1)))
	       (list (cons 'left x-list) vars
		     vars-to-old-vars-alist toinst))
	     (let ((prev2
		    (fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data
		     right-conjunct
		     ignore-deco-flag-and-sig-tovars goal-formula)))
	       (if prev2
		   (let* ((x-list (car prev2))
			  (vars (cadr prev2))
			  (vars-to-old-vars-alist (caddr prev2))
			  (toinst (cadddr prev2)))
		     (list (cons 'right x-list) vars
			   vars-to-old-vars-alist toinst))
		   #f)))))))
      ((atom-form? used-formula)
       (cond
	((term=?
	  (make-term-in-const-form
	   (pconst-name-to-pconst "ImpConst"))
	  (term-in-app-form-to-final-op (atom-form-to-kernel
					 used-formula)))
	 (let* ((kernel (atom-form-to-kernel used-formula))
		(args (term-in-app-form-to-args kernel))
		(arg1
		 (if (= 2 (length args))
		     (car args)
		     (myerror
		      "fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data"
		      "two args expected")))
		(arg2 (cadr args))
		(prem (make-atomic-formula arg1))
		(concl (make-atomic-formula arg2))
		(prev
		 (apply
		  fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data
		  concl
		  ignore-deco-flag-and-sig-tovars goal-formula elab-path)))
	   (if (not prev)
	       #f
	       (let* ((x-list (car prev))
		      (vars (cadr prev))
		      (vars-to-old-vars-alist (caddr prev))
		      (toinst (cadddr prev)))
		 (list (cons DEFAULT-GOAL-NAME x-list) vars
		       vars-to-old-vars-alist toinst)))))
	((term=?
	  (make-term-in-const-form
	   (pconst-name-to-pconst "AndConst"))
	  (term-in-app-form-to-final-op (atom-form-to-kernel
					 used-formula)))
	 (let* ((kernel (atom-form-to-kernel used-formula))
		(args (term-in-app-form-to-args kernel))
		(left-arg (if (= 2 (length args))
			      (car args)
			      (myerror "two args expected")))
		(right-arg (cadr args))
		(left-conjunct (make-atomic-formula left-arg))
		(right-conjunct (make-atomic-formula right-arg)))
	   (if
	    (pair? elab-path)
	    (let* ((direction (car elab-path))
		   (conjunct (cond ((eq? 'left direction) left-conjunct)
				   ((eq? 'right direction) right-conjunct)
				   (else (myerror "left or right expected"
						  direction))))
		   (prev (apply
			  fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data
			  conjunct ignore-deco-flag-and-sig-tovars goal-formula
			  (cdr elab-path))))
	      (if (not prev)
		  #f
		  (let* ((x-list (car prev))
			 (vars (cadr prev))
			 (vars-to-old-vars-alist (caddr prev))
			 (toinst (cadddr prev)))
		    (list (cons direction x-list) vars
			  vars-to-old-vars-alist toinst))))
	    (let ((prev1
		   (fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data
		    left-conjunct
		    ignore-deco-flag-and-sig-tovars goal-formula)))
	      (if
	       prev1
	       (let* ((x-list (car prev1))
		      (vars (cadr prev1))
		      (vars-to-old-vars-alist (caddr prev1))
		      (toinst (cadddr prev1)))
		 (list (cons 'left x-list) vars
		       vars-to-old-vars-alist toinst))
	       (let ((prev2
		      (fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data
		       right-conjunct
		       ignore-deco-flag-and-sig-tovars goal-formula)))
		 (if prev2
		     (let* ((x-list (car prev2))
			    (vars (cadr prev2))
			    (vars-to-old-vars-alist (caddr prev2))
			    (toinst (cadddr prev2)))
		       (list (cons 'right x-list) vars
			     vars-to-old-vars-alist toinst))
		     #f)))))))
	(else #f)))
      (else (myerror
	     "fla-and-ignore-deco-flag-and-sig-tovars-and-goal-fla-to-use-data"
	     "formula expected"
	     used-formula))))))

;; use-with is a more verbose form of use, where the terms are not
;; inferred via unification, but have to be given explicitly.  Also,
;; for the instantiated premises one can indicate how they are to come
;; about.  In the following definition of use-with x is one of the
;; following.

;; - A number or string identifying a hypothesis form the context.
;; - The name of a theorem or global assumption.  If it is a global
;;   assumption whose final conclusion is a nullary predicate variable
;;   distinct from bot (e.g. EfqLog or StabLog), this predicate variable
;;   is substituted by the goal formula.
;; - A closed proof.
;; - A formula with free variables from the context, generating a new goal.
;; Moreover x-list is a list consisting of
;; - a number or string identifying a hypothesis form the context,
;; - the name of a theorem or global assumption,
;; - a closed proof,
;; - the string "?" (value of DEFAULT-GOAL-NAME), generating a new goal,
;; - a symbol left or right,
;; - a term, whose free variables are added to the context,
;; - a type, which is substituted for the 1st tvar,
;; - a comprehension term, which is substituted for the 1st pvar.

;; Notice that new free variables not in the ordered context can be
;; introduced in use-with.  They will be present in the newly generated
;; num-goals.  The reason is that proofs should be allowed to contain free
;; variables.  This is necessary to allow logic in ground types where no
;; contant is available (e.g. to prove all x Px -> all x ~ Px -> F).

(define (use-with x . x-list)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply use-with-intern num-goals proof maxgoal x x-list))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (use-with-intern num-goals proof maxgoal x . x-list)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (goal-formula (goal-to-formula goal))
	 (proof-and-new-num-goals-and-maxgoal
	  (apply x-and-x-list-to-proof-and-new-num-goals-and-maxgoal
		 num-goal maxgoal x x-list))
	 (new-proof (car proof-and-new-num-goals-and-maxgoal))
	 (new-num-goals (cadr proof-and-new-num-goals-and-maxgoal))
	 (new-maxgoal (caddr proof-and-new-num-goals-and-maxgoal)))
    (if (not (classical-formula=?
	      (proof-to-formula new-proof) goal-formula ignore-deco-flag))
	(myerror "use-with-intern" "equal formulas expected"
		 (rename-variables (fold-formula (proof-to-formula new-proof)))
		 goal-formula))
    (let ((final-proof (goal-subst proof goal new-proof)))
      (if
       COMMENT-FLAG
       (let ((nc-viols (nc-violations final-proof)))
	 (if (pair? nc-viols)
	     (begin
	       (comment "Warning: nc-intro with cvar(s)")
	       (for-each comment (map (lambda (x)
					(if (var-form? x)
					    (var-to-string x)
					    (avar-to-string x)))
				      nc-viols))))))
      (make-pproof-state
       (append (reverse new-num-goals) (cdr num-goals))
       final-proof
       new-maxgoal))))

;; When creating new num-goals in the given context we will need

(define (context-and-ncvars-and-formula-to-formula context ncvars formula)
  (if (null? context)
      formula
      (let* ((x (car context))
	     (prev (context-and-ncvars-and-formula-to-formula
		    (cdr context) ncvars formula)))
	(cond ((var-form? x)
	       (if (member x ncvars) (make-allnc x prev) (make-all x prev)))
	      ((avar-form? x)
	       (if (member-wrt avar=? x ncvars)
		   (make-impnc (avar-to-formula x) prev)
		   (make-imp (avar-to-formula x) prev)))
	      (else (myerror "context-and-ncvars-and-formula-to-formula"
			     "var or avar expected"
			     x))))))

(define (context-to-proofargs context)
  (map (lambda (x) (cond ((var-form? x) (make-term-in-var-form x))
			 ((avar-form? x) (make-proof-in-avar-form x))
			 (else (myerror
				"context-to-proofargs" "var or avar expected"
				x))))
       context))

(define (context-and-ncvars-and-formula-to-new-goal context ncvars formula)
  (let* ((goalvarformula
	  (context-and-ncvars-and-formula-to-formula context ncvars formula))
	 (goalvar
	  (if (null? (formula-to-free goalvarformula))
	      (formula-to-new-avar goalvarformula DEFAULT-AVAR-NAME)
	      (apply myerror "unexpected free variables"
		     (formula-to-free goalvarformula)))))
    (apply mk-goal-in-elim-form
	   (make-goal-in-avar-form goalvar) context)))

(define (hyp-info-to-leaf num-goal x)
  (let* ((goal (num-goal-to-goal num-goal))
	 (goal-formula (goal-to-formula goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (maxhyp (length avars)))
    (cond
     ((and (integer? x) (positive? x))
      (if (<= x maxhyp)
	  (make-proof-in-avar-form (list-ref avars (- x 1)))
	  (myerror "hyp-info-to-leaf" "assumption number expected" x)))
     ((and (string? x)
	   (member x (hypname-info-to-names hypname-info)))
      (let ((i (name-and-hypname-info-to-index x hypname-info)))
	(if (<= i maxhyp)
	    (make-proof-in-avar-form (list-ref avars (- i 1)))
	    (myerror "hyp-info-to-leaf" "assumption number expected" i))))
     ((string? x)
      (let ((info (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS))))
	(if (not info)
	    (myerror "hyp-info-to-leaf" "illegal first argument" x))
	(let ((aconst (cadr info)))
	  (make-proof-in-aconst-form aconst))))
     ((proof-form? x) x)
     (else (myerror "hyp-info-to-leaf" "illegal first argument" x)))))

(define (hyp-info-to-formula num-goal x)
  (let* ((goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (maxhyp (length avars)))
    (cond
     ((and (integer? x) (positive? x))
      (if (<= x maxhyp)
	  (avar-to-formula (list-ref avars (- x 1)))
	  (myerror "hyp-info-to-formula" "assumption number expected" x)))
     ((and (string? x)
	   (member x (hypname-info-to-names hypname-info)))
      (let ((i (name-and-hypname-info-to-index x hypname-info)))
	(if (<= i maxhyp)
	    (avar-to-formula (list-ref avars (- i 1)))
	    (myerror "hyp-info-to-formula" "assumption number expected" i))))
     ((string? x)
      (let ((info (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS))))
	(if info
	    (aconst-to-formula (cadr info))
	    (myerror "hyp-info-to-formula" "illegal first argument" x))))
     ((proof-form? x) (proof-to-formula x))
     (else (myerror "hyp-info-to-formula" "illegal first argument" x)))))

;; PVAR-TO-MR-PVAR-ALIST initially has
;; (Pvar alpha) -> (Pvar alpha gamma)^
;; Pvar2 -> (Pvar beta2)^2
;; Pvar1 -> (Pvar beta1)^1
;; Pvar  -> (Pvar beta)^

(define PVAR-TO-MR-PVAR-ALIST
  (list
   (list (make-pvar (make-arity (make-tvar -1 "alpha"))
		    -1 h-deg-zero n-deg-zero "")
	 (make-pvar (make-arity (make-tvar -1 "alpha") (make-tvar -1 "gamma"))
		    -1 h-deg-one n-deg-zero ""))
   (list (make-pvar (make-arity)
		    2 h-deg-zero n-deg-zero "")
	 (make-pvar (make-arity (make-tvar 2 "beta"))
		    2 h-deg-one n-deg-zero ""))
   (list (make-pvar (make-arity)
		    1 h-deg-zero n-deg-zero "")
	 (make-pvar (make-arity (make-tvar 1 "beta"))
		    1 h-deg-one n-deg-zero ""))
   (list (make-pvar (make-arity)
		    -1 h-deg-zero n-deg-zero "")
	 (make-pvar (make-arity (make-tvar -1 "beta"))
		    -1 h-deg-one n-deg-zero ""))))

(define (PVAR-TO-MR-PVAR pvar)
  (let ((info (assoc pvar PVAR-TO-MR-PVAR-ALIST)))
    (if info
	(cadr info)
	(let* ((type (PVAR-TO-TVAR pvar))
	       (arity (pvar-to-arity pvar))
	       (types (arity-to-types arity))
	       (newarity (apply make-arity (append types (list type))))
	       (newpvar (arity-to-new-harrop-pvar newarity)))
	      (set! PVAR-TO-MR-PVAR-ALIST
		    (cons (list pvar newpvar) PVAR-TO-MR-PVAR-ALIST))
	      newpvar))))

(define (x-and-x-list-to-proof-and-new-num-goals-and-maxgoal
	 num-goal maxgoal x . x-list)
  (let* ((number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (avars (context-to-avars context))
	 (maxhyp (length avars))
	 (types (list-transform-positive x-list type-form?))
	 (cterms (list-transform-positive x-list cterm-form?))
	 (rest-x-list (list-transform-positive x-list
			(lambda (y) (and (not (type-form? y))
					 (not (cterm-form? y))))))
	 (x-for-types-and-cterms
	  (if
	   (or (pair? types) (pair? cterms)) ;else x
	   (let* ((proof (if (proof-form? x) x (thm-or-ga-name-to-proof x)))
		  (tvars (proof-to-tvars proof))
		  (l1 (min (length tvars) (length types)))
		  (pvars (proof-to-pvars proof))
		  (l2 (min (length pvars) (length cterms)))
		  (tsubst (map list (list-head tvars l1) (list-head types l1)))
		  (psubst (map list (list-head pvars l2) (list-head cterms l2)))
		  (tpsubst (append tsubst psubst)))
	     (if (and COMMENT-FLAG (< (length tvars) (length types)))
		 (begin
		   (comment "warning: superfluous types")
		   (for-each
		    comment
		    (map type-to-string (list-tail types (length tvars))))))
	     (if (and COMMENT-FLAG (< (length pvars) (length cterms)))
		 (begin
		   (comment "warning: superfluous cterms")
		   (for-each
		    comment
		    (map cterm-to-string (list-tail cterms (length pvars))))))
	     (if (not (admissible-substitution? tpsubst proof))
		 (myerror "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
			  "inadmissible substitution"
			  tpsubst
			  "for proof"
			  (if (proof-form? x) (tag x) x)))
	     (if (not (mr-correct? psubst PVAR-TO-MR-PVAR-ALIST))
		 (myerror "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
			  "mr-correct predicate substitution expected"
			  psubst
			  "for proof"
			  (if (proof-form? x) (tag x) x)))
	     (proof-substitute proof tpsubst))
	   x))
	 (leaf (if (formula-form? x-for-types-and-cterms)
		   (context-and-ncvars-and-formula-to-new-goal
		    context ncvars x-for-types-and-cterms)
		   (hyp-info-to-leaf num-goal x-for-types-and-cterms)))
	 (new-num-goals
	  (if
	   (formula-form? x-for-types-and-cterms) ;then a new goal is created
	   (list (make-num-goal
		  (+ 1 maxgoal) leaf drop-info hypname-info
		  (or ignore-deco-flag
		      (formula-of-nulltype? x-for-types-and-cterms))))
	   '()))
	 (leaf-and-new-num-goals-and-maxgoal
	  (list leaf new-num-goals (if (formula-form? x-for-types-and-cterms)
				       (+ 1 maxgoal)
				       maxgoal)))
	 (x-list-test
	  (if (null? x-list)
	      #t
	      (do ((l1 x-list (cdr l1))
		   (l2 (cdr x-list) (cdr l2))
		   (res #t (let ((fst (car l1))
				 (snd (car l2)))
			     (and res (cond
				       ((type-form? fst) #t)
				       ((cterm-form? fst)
					(not (type-form? snd)))
				       (else (not (or (type-form? snd)
						      (cterm-form? snd)))))))))
		  ((null? l2) res)))))
    (if (and COMMENT-FLAG (not x-list-test))
	(comment
	 "warning: expected order of arguments is types - cterms - rest"))
    (do ((l rest-x-list (cdr l))
	 (proof-and-new-num-goals-and-maxgoal
	  leaf-and-new-num-goals-and-maxgoal
	  (let* ((proof (car proof-and-new-num-goals-and-maxgoal))
		 (used-formula (unfold-formula (proof-to-formula proof)))
		 (new-num-goals (cadr proof-and-new-num-goals-and-maxgoal))
		 (maxgoal (caddr proof-and-new-num-goals-and-maxgoal))
		 (x1 (car l)))
	    (cond
	     ((or (imp-form? used-formula) (impnc-form? used-formula))
	      (if
	       (equal? x1 DEFAULT-GOAL-NAME) ;then a new goal is created
	       (let* ((prem (bicon-form-to-left used-formula))
		      (newvars (set-minus (formula-to-free prem)
					  (context-to-vars context)))
		      (goalvarformula
		       (context-and-ncvars-and-formula-to-formula
			context ncvars
			(apply mk-all (append newvars (list prem)))))
		      (goalvar (formula-to-new-avar goalvarformula
						    DEFAULT-AVAR-NAME))
		      (goal (apply mk-goal-in-elim-form
				   (make-goal-in-avar-form goalvar)
				   (append context newvars)))
		      (new-num-goal
		       (make-num-goal
			(+ 1 maxgoal) goal drop-info hypname-info
			(or ignore-deco-flag (formula-of-nulltype? prem)))))
		 (list (if (imp-form? used-formula)
			   (make-proof-in-imp-elim-form proof goal)
			   (make-proof-in-impnc-elim-form proof goal))
		       (cons new-num-goal new-num-goals)
		       (+ 1 maxgoal)))
	       (let
		   ((arg
		     (cond
		      ((and (integer? x1) (positive? x1))
		       (if
			(<= x1 maxhyp)
			(make-proof-in-avar-form
			 (list-ref avars (- x1 1)))
			(myerror
			 "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
			 "assumption number expected" x1)))
		      ((and (string? x1)
			    (member x1 (hypname-info-to-names
					hypname-info)))
		       (let ((i (name-and-hypname-info-to-index
				 x1 hypname-info)))
			 (if
			  (<= i maxhyp)
			  (make-proof-in-avar-form
			   (list-ref avars (- i 1)))
			  (myerror
			   "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
			   "assumption number expected" i))))
		      ((and (string? x1) (assoc x1 THEOREMS))
		       (make-proof-in-aconst-form
			(cadr (assoc x1 THEOREMS))))
		      ((and (string? x1) (assoc x1 GLOBAL-ASSUMPTIONS))
		       (make-proof-in-aconst-form
			(cadr (assoc x1 GLOBAL-ASSUMPTIONS))))
		      ((proof-form? x1) x1)
		      (else
		       (myerror
			"x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
			"unexpected argument" x1)))))
		 (if (classical-formula=? (bicon-form-to-left used-formula)
					  (proof-to-formula arg))
		     (list (if (imp-form? used-formula)
			       (make-proof-in-imp-elim-form proof arg)
			       (make-proof-in-impnc-elim-form proof arg))
			   new-num-goals maxgoal)
		     (myerror
		      "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		      "formulas do not fit"
		      used-formula
		      (proof-to-formula arg))))))
	     ((and-form? used-formula)
	      (cond
	       ((eq? x1 'left)
		(list (make-proof-in-and-elim-left-form proof)
		      new-num-goals maxgoal))
	       ((eq? x1 'right)
		(list (make-proof-in-and-elim-right-form proof)
		      new-num-goals maxgoal))
	       (else (myerror
		      "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		      "left or right expected" x1))))
	     ((andd-form? used-formula)
	      (cond
	       ((eq? x1 'left)
		(list (make-proof-in-andd-elim-left-form proof)
		      new-num-goals maxgoal))
	       ((eq? x1 'right)
		(list (make-proof-in-andd-elim-right-form proof)
		      new-num-goals maxgoal))
	       (else (myerror
		      "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		      "left or right expected" x1))))
	     ((andl-form? used-formula)
	      (cond
	       ((eq? x1 'left)
		(list (make-proof-in-andl-elim-left-form proof)
		      new-num-goals maxgoal))
	       ((eq? x1 'right)
		(list (make-proof-in-andl-elim-right-form proof)
		      new-num-goals maxgoal))
	       (else (myerror
		      "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		      "left or right expected" x1))))
	     ((andr-form? used-formula)
	      (cond
	       ((eq? x1 'left)
		(list (make-proof-in-andr-elim-left-form proof)
		      new-num-goals maxgoal))
	       ((eq? x1 'right)
		(list (make-proof-in-andr-elim-right-form proof)
		      new-num-goals maxgoal))
	       (else (myerror
		      "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		      "left or right expected" x1))))
	     ((andnc-form? used-formula)
	      (cond
	       ((eq? x1 'left)
		(list (make-proof-in-andnc-elim-left-form proof)
		      new-num-goals maxgoal))
	       ((eq? x1 'right)
		(list (make-proof-in-andnc-elim-right-form proof)
		      new-num-goals maxgoal))
	       (else (myerror
		      "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		      "left or right expected" x1))))
	     ((or (all-form? used-formula) (allnc-form? used-formula))
	      (if
	       (term-form? x1)
	       (let* ((var (car (quant-form-to-vars used-formula)))
		      (type1 (var-to-type var))
		      (t-deg1 (var-to-t-deg var))
		      (type2 (term-to-type x1)))
		 (if
		  (equal? type1 type2)
		  (if
		   (not (and (t-deg-one? t-deg1)
			     (not (synt-total? x1))))
		   (list (if (all-form? used-formula)
			     (make-proof-in-all-elim-form proof x1)
			     (make-proof-in-allnc-elim-form proof x1))
			 new-num-goals maxgoal)
		   (myerror
		    "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		    "attempt to apply all-elim to non-total term" x1))
		  (myerror
		   "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		   "types don't fit for all-elim" type1 type2
		   "originating from all-formula" used-formula
		   "and use-with argument" x1)))
	       (myerror
		"x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		"term expected" x1)))
	     ((atom-form? used-formula)
	      (cond
	       ((term=? (make-term-in-const-form
			 (pconst-name-to-pconst "ImpConst"))
			(term-in-app-form-to-final-op (atom-form-to-kernel
						       used-formula)))
		(let*
		    ((kernel (atom-form-to-kernel used-formula))
		     (args (term-in-app-form-to-args kernel))
		     (arg1
		      (if
		       (= 2 (length args))
		       (car args)
		       (myerror
			"x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
			"two args expected")))
		     (arg2 (cadr args))
		     (imp-proof (if (and (synt-total? arg1) (synt-total? arg2))
				    atom-to-imp-proof
				    (make-proof-in-aconst-form
				     atom-to-imp-aconst)))
		     (prem (make-atomic-formula arg1)))
		  (if
		   (equal? x1 DEFAULT-GOAL-NAME) ;then a new goal is created
		   (let* ((newvars (set-minus (formula-to-free prem)
					      (context-to-vars context)))
			  (goalvarformula
			   (context-and-ncvars-and-formula-to-formula
			    context ncvars
			    (apply mk-all (append newvars (list prem)))))
			  (goalvar (formula-to-new-avar goalvarformula
							DEFAULT-AVAR-NAME))
			  (goal
			   (apply mk-goal-in-elim-form
				  (make-goal-in-avar-form goalvar)
				  (append context newvars)))
			  (new-num-goal
			   (make-num-goal
			    (+ 1 maxgoal) goal drop-info hypname-info
			    (or ignore-deco-flag (formula-of-nulltype? prem)))))
		     (list (mk-proof-in-elim-form
			    imp-proof arg1 arg2 proof goal)
			   (cons new-num-goal new-num-goals)
			   (+ 1 maxgoal)))
		   (let ((arg
			  (cond
			   ((and (integer? x1) (positive? x1))
			    (if
			     (<= x1 maxhyp)
			     (make-proof-in-avar-form
			      (list-ref avars (- x1 1)))
			     (myerror
			      "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
			      "assumption number expected" x1)))
			   ((and (string? x1)
				 (member x1 (hypname-info-to-names
					     hypname-info)))
			    (let ((i (name-and-hypname-info-to-index
				      x1 hypname-info)))
			      (if
			       (<= i maxhyp)
			       (make-proof-in-avar-form
				(list-ref avars (- i 1)))
			       (myerror
				"x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
				"assumption number expected" i))))
			   ((and (string? x1) (assoc x1 THEOREMS))
			    (make-proof-in-aconst-form
			     (cadr (assoc x1 THEOREMS))))
			   ((and (string? x1) (assoc x1 GLOBAL-ASSUMPTIONS))
			    (make-proof-in-aconst-form
			     (cadr (assoc x1 GLOBAL-ASSUMPTIONS))))
			   ((proof-form? x1) x1)
			   (else
			    (myerror
			     "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
			     "unexpected argument" x1)))))
		     (if
		      (classical-formula=? prem (proof-to-formula arg))
		      (list (mk-proof-in-elim-form
			     imp-proof arg1 arg2 proof arg)
			    new-num-goals maxgoal)
		      (myerror
		       "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		       "formulas do not fit"
		       used-formula
		       (proof-to-formula arg)))))))
	       ((term=? (make-term-in-const-form
			 (pconst-name-to-pconst "AndConst"))
			(term-in-app-form-to-final-op (atom-form-to-kernel
						       used-formula)))
		(let*
		    ((kernel (atom-form-to-kernel used-formula))
		     (args (term-in-app-form-to-args kernel))
		     (left-arg
		      (if
		       (= 2 (length args))
		       (car args)
		       (myerror
			"x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
			"two args expected")))
		     (right-arg (cadr args)))
		  (cond
		   ((eq? x1 'left)
		    (list (mk-proof-in-elim-form
			   (if (and (synt-total? left-arg)
				    (synt-total? right-arg))
			       and-atom-to-left-proof
			       (make-proof-in-aconst-form
				and-atom-to-left-aconst))
			   left-arg right-arg proof)
			  new-num-goals maxgoal))
		   ((eq? x1 'right)
		    (list (mk-proof-in-elim-form
			   (if (and (synt-total? left-arg)
				    (synt-total? right-arg))
			       and-atom-to-right-proof
			       (make-proof-in-aconst-form
				and-atom-to-right-aconst))
			   left-arg right-arg proof)
			  new-num-goals maxgoal))
		   (else
		    (myerror
		     "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		     "left or right expected" x1)))))
	       (else (myerror
		      "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		      "unexpected atom" used-formula))))
	     (else (myerror
		    "x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		    "unexpected formula" used-formula))))))
	((null? l) proof-and-new-num-goals-and-maxgoal))))

(define (mr-correct? psubst alist)
  (or (null? alist)
      (let* ((item (car alist))
	     (pvar1 (car item))
	     (info1 (assoc pvar1 psubst)))
	(if info1 ;else rec call
	    (let* ((pvar2 (cadr item))
		   (info2 (assoc pvar2 psubst)))
	      (if info2 ;else rec call
		  (let* ((cterm1 (cadr info1))
			 (vars1 (cterm-to-vars cterm1))
			 (fla1 (cterm-to-formula cterm1))
			 (cterm2 (cadr info2))
			 (vars2 (cterm-to-vars cterm2))
			 (var (type-to-new-partial-var
			       (formula-to-et-type fla1)))
			 (mr-fla (real-and-formula-to-mr-formula
				  (make-term-in-var-form var) fla1))
			 (mr-cterm
			  (apply make-cterm var (append vars1 (list mr-fla))))
			 (test (cterm=? cterm2 mr-cterm)))
		    (and test (mr-correct? psubst (cdr alist))))
		  (mr-correct? psubst (cdr alist))))
	    (mr-correct? psubst (cdr alist))))))

;; inst-with does for forward chaining the same as use-with for backward
;; chaining.  It replaces the present goal by a new one, with one
;; additional hypothesis obtained by instantiating a previous one.  Notice
;; that this effect could also be obtained by cut.  In the following
;; definition of inst-with x is one of the following.
;; - A number or string identifying a hypothesis form the context.
;; - The name of a theorem or global assumption.
;; - A closed proof.
;; - A formula with free variables from the context, generating a new goal.
;; Moreover x-list is a list consisting of
;; - a number or string identifying a hypothesis form the context,
;; - the name of a theorem or global assumption,
;; - a closed proof,
;; - the string "?" (value of DEFAULT-GOAL-NAME), generating a new goal,
;; - a symbol left or right,
;; - a term, whose free variables are added to the context,
;; - a type, which is substituted for the 1st tvar,
;; - a comprehension term, which is substituted for the 1st pvar.

(define (inst-with x . x-list)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply inst-with-intern num-goals proof maxgoal x x-list))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (inst-with-intern num-goals proof maxgoal x . x-list)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (goal-formula (goal-to-formula goal))
	 (proof-and-new-num-goals-and-maxgoal
	  (apply x-and-x-list-to-proof-and-new-num-goals-and-maxgoal
		 num-goal maxgoal x x-list))
	 (proof-of-inst (car proof-and-new-num-goals-and-maxgoal))
	 (new-num-goals (cadr proof-and-new-num-goals-and-maxgoal))
	 (new-maxgoal (caddr proof-and-new-num-goals-and-maxgoal))
	 (inst-formula (proof-to-formula proof-of-inst))
	 (new-avar (formula-to-new-avar inst-formula DEFAULT-AVAR-NAME))
	 (new-goalformula
	  (context-and-ncvars-and-formula-to-formula
	   (append context (list new-avar)) ncvars goal-formula))
	 (new-goalvar (formula-to-new-avar new-goalformula DEFAULT-AVAR-NAME))
	 (new-goal (apply mk-goal-in-elim-form
			  (make-goal-in-avar-form new-goalvar)
			  (append context (list new-avar))))
	 (new-proof (make-proof-in-imp-elim-form
		     (make-proof-in-imp-intro-form new-avar new-goal)
		     proof-of-inst))
	 (new-num-goal
	  (begin (set! maxgoal (+ 1 new-maxgoal))
		 (make-num-goal maxgoal new-goal drop-info hypname-info
				ignore-deco-flag))))
    (let ((final-proof (goal-subst proof goal new-proof)))
      (if
       COMMENT-FLAG
       (let ((nc-viols (nc-violations final-proof)))
	 (if (pair? nc-viols)
	     (begin
	       (comment "Warning: nc-intro with cvar(s)")
	       (for-each comment (map (lambda (x)
					(if (var-form? x)
					    (var-to-string x)
					    (avar-to-string x)))
				      nc-viols))))))
      (make-pproof-state
       (append (cons new-num-goal (reverse new-num-goals))
	       (cdr num-goals))
       final-proof
       maxgoal))))

;; inst-with-to expects a string as its last argument, which is used (via
;; name-hyp) to name the newly introduced instantiated hypothesis.

(define (inst-with-to x . x-list-and-name)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply inst-with-to-intern
		 num-goals proof maxgoal x
		 x-list-and-name))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (inst-with-to-intern num-goals proof maxgoal x . x-list-and-name)
  (if (null? x-list-and-name)
      (myerror "inst-with-to" "more arguments expected"))
  (if (member DEFAULT-GOAL-NAME x-list-and-name)
      (myerror "? illegal for inst-with-to; use inst-with instead"))
  (let ((name (car (last-pair x-list-and-name)))
	(x-and-x-list (cons x (list-head x-list-and-name
					 (- (length x-list-and-name) 1)))))
    (if (not (string? name))
	(myerror "inst-with-to" "string expected" name))
    (let* ((pproof-state1
	    (apply inst-with-intern num-goals proof maxgoal x-and-x-list))
	   (num-goals (pproof-state-to-num-goals pproof-state1))
	   (num-goal
	    (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	   (goal (num-goal-to-goal num-goal))
	   (context (goal-to-context goal))
	   (avars (context-to-avars context))
	   (maxhyp (length avars)))
      (apply name-hyp-intern
	     (append pproof-state1 (list maxhyp name))))))

;; Given a goal B, (cut A) generates the two new goals A -> B and A,
;; with A -> B to be proved first.

(define (cut string-or-formula)
  (let ((formula (if (string? string-or-formula)
		     (pf string-or-formula)
		     string-or-formula)))
    (if (not (formula-form? formula))
	(myerror "cut" "formula expected" formula))
    (if (formula-with-illegal-tensor? (unfold-formula formula))
	(myerror "tensor ! should be used with excl or exca only" formula))
    (let* ((num-goals (pproof-state-to-num-goals))
	   (proof (pproof-state-to-proof))
	   (maxgoal (pproof-state-to-maxgoal))
	   (number
	    (num-goal-to-number
	     (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
      (set! PPROOF-STATE (cut-intern num-goals proof maxgoal formula))
      (pproof-state-history-push PPROOF-STATE)
      (display-new-goals num-goals number))))

(define (cut-intern num-goals proof maxgoal side-premise-formula)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (formula (goal-to-formula goal)))
    (use-with-intern num-goals proof maxgoal
		     (make-imp (unfold-formula side-premise-formula) formula)
		     DEFAULT-GOAL-NAME)))

;; Given a goal B, (assert A) generates the two new goals A and A -> B,
;; with A to be proved first.

(define (assert string-or-formula)
  (let ((formula (if (string? string-or-formula)
		     (pf string-or-formula)
		     string-or-formula)))
    (if (not (formula-form? formula))
	(myerror "assert" "formula expected" formula))
    (if (formula-with-illegal-tensor? (unfold-formula formula))
	(myerror "tensor ! should be used with excl or exca only" formula))
    (let* ((num-goals (pproof-state-to-num-goals))
	   (proof (pproof-state-to-proof))
	   (maxgoal (pproof-state-to-maxgoal))
	   (number
	    (num-goal-to-number
	     (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
      (set! PPROOF-STATE (assert-intern num-goals proof maxgoal formula))
      (pproof-state-history-push PPROOF-STATE)
      (display-new-goals num-goals number))))

(define (assert-intern num-goals proof maxgoal formula)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (goal-formula (goal-to-formula goal))
	 (pproof-state1 (use-with-intern
			 num-goals proof maxgoal
			 (make-imp (unfold-formula formula) goal-formula)
			 DEFAULT-GOAL-NAME))
	 (num-goals1 (pproof-state-to-num-goals pproof-state1))
	 (reordered-num-goals
	  (append (list (cadr num-goals1) (car num-goals1))
		  (cddr num-goals1))))
    (make-pproof-state
     reordered-num-goals
     (pproof-state-to-proof pproof-state1)
     (pproof-state-to-maxgoal pproof-state1))))

;; To move (all or n) universally quantified variables and hypotheses of
;; the current goal into the context, we use (strip) or (strip n).

(define (strip . x)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal)))
    (set! PPROOF-STATE (apply strip-intern num-goals proof maxgoal x))
    (pproof-state-history-push PPROOF-STATE)
    (display-comment "ok, we now have the new goal ")
    (if COMMENT-FLAG (newline))
    (display-num-goal (car (pproof-state-to-num-goals)))))

(define (strip-intern num-goals proof maxgoal . x)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (formula (goal-to-formula goal)))
    (do ((nc-and-ncv-and-np-and-ng
	  (list '() '() goal goal)
	  (let* ((nc (car nc-and-ncv-and-np-and-ng))
		 (ncv (cadr nc-and-ncv-and-np-and-ng))
		 (np (caddr nc-and-ncv-and-np-and-ng))
		 (ng (cadddr nc-and-ncv-and-np-and-ng))
		 (nf (proof-to-formula ng)))
	    (case (tag nf)
	      ((all)
	       (let ((var (all-form-to-var nf)))
		 (if ;quantified var already occurs: rename
		  (or (member var (context-to-vars context))
		      (member var (context-to-vars nc)))
		  (let* ((newvar (var-to-new-var var))
			 (ng1 (make-goal-in-all-elim-form ng newvar)))
		    (list (cons newvar nc)
			  (if (formula-of-nulltype? (goal-to-formula ng))
			      ncv
			      (cons newvar ncv))
			  (goal-subst np ng (make-proof-in-all-intro-form
					      newvar ng1))
			  ng1))
		  (let ((ng1 (make-goal-in-all-elim-form ng var)))
		    (list (cons var nc)
			  (if (formula-of-nulltype? (goal-to-formula ng))
			      ncv
			      (cons var ncv))
			  (goal-subst
			   np ng (make-proof-in-all-intro-form var ng1))
			  ng1)))))
	      ((allnc)
	       (let ((var (allnc-form-to-var nf)))
		 (if ;quantified var already occurs: rename
		  (or (member var (context-to-vars context))
		      (member var (context-to-vars nc)))
		  (let* ((newvar (var-to-new-var var))
			 (ng1 (make-goal-in-allnc-elim-form ng newvar)))
		    (list (cons newvar nc)
			  ncv
			  (goal-subst np ng (make-proof-in-allnc-intro-form
					     newvar ng1))
			  ng1))
		  (let ((ng1 (make-goal-in-allnc-elim-form ng var)))
		    (list (cons var nc)
			  ncv
			  (goal-subst
			   np ng (make-proof-in-allnc-intro-form var ng1))
			  ng1)))))
	      ((imp)
	       (let* ((premise (imp-form-to-premise nf))
		      (avar (formula-to-new-avar premise DEFAULT-AVAR-NAME))
		      (ng1 (make-goal-in-imp-elim-form ng avar)))
		 (list
		  (cons avar nc)
		  ncv
		  (goal-subst np ng (make-proof-in-imp-intro-form avar ng1))
		  ng1)))
	      ((impnc)
	       (let* ((premise (impnc-form-to-premise nf))
		      (avar (formula-to-new-avar premise DEFAULT-AVAR-NAME))
		      (ng1 (make-goal-in-impnc-elim-form ng avar)))
		 (list
		  (cons avar nc)
		  ncv
		  (goal-subst np ng (make-proof-in-impnc-intro-form avar ng1))
		  ng1)))
	      ((exca)
	       (let* ((vars (exca-form-to-vars nf))
		      (kernel (exca-form-to-kernel nf))
		      (premise
		       (apply mk-all
			      (append vars
				      (list
				       (apply mk-imp
					      (append
					       (tensor-form-to-parts kernel)
					       (list falsity)))))))
		      (avar (formula-to-new-avar premise DEFAULT-AVAR-NAME))
		      (ng1 (make-goal-in-imp-elim-form ng avar)))
		 (list
		  (cons avar nc)
		  ncv
		  (goal-subst np ng (make-proof-in-imp-intro-form avar ng1))
		  ng1)))
	      ((excl)
	       (let* ((vars (excl-form-to-vars nf))
		      (kernel (excl-form-to-kernel nf))
		      (premise
		       (apply mk-all
			      (append vars
				      (list
				       (apply mk-imp
					      (append
					       (tensor-form-to-parts kernel)
					       (list falsity-log)))))))
		      (avar (formula-to-new-avar premise DEFAULT-AVAR-NAME))
		      (ng1 (make-goal-in-imp-elim-form ng avar)))
		 (list
		  (cons avar nc)
		  ncv
		  (goal-subst np ng (make-proof-in-imp-intro-form avar ng1))
		  ng1)))
	      (else (myerror "strip" "unexpected formula" nf)))))
	 (n (cond ((null? x)
		   (string-length (formula-to-string formula)))
		  ((and (integer? (car x)) (positive? (car x))) (car x))
		  (else
		   (myerror "strip" "positive integer expected" (car x))))
	    (- n 1)))
	((or (zero? n) (let* ((ng (cadddr nc-and-ncv-and-np-and-ng))
			      (nf (proof-to-formula ng)))
			 (or (atom-form? nf)
			     (predicate-form? nf)
			     (and-form? nf)
			     (ex-form? nf))))
	 (let* ((np (caddr nc-and-ncv-and-np-and-ng))
		(ng (cadddr nc-and-ncv-and-np-and-ng))
		(new-num-goal
		 (make-num-goal (+ 1 maxgoal) ng drop-info hypname-info
				ignore-deco-flag)))
	   (make-pproof-state (cons new-num-goal (cdr num-goals))
			      (goal-subst (pproof-state-to-proof) goal np)
			      (+ 1 maxgoal)))))))

;; In (drop . x-list), x-list is a list of numbers or strings identifying
;; hypotheses from the context.  A new goal is created, which differs
;; from the previous one only in display aspects: the listed hypotheses
;; are hidden (but still present).  If x-list is empty, all hypotheses
;; are hidden.

(define (drop . x-list)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal)))
    (set! PPROOF-STATE (apply drop-intern num-goals proof maxgoal x-list))
    (pproof-state-history-push PPROOF-STATE)
    (display-comment "ok, we now have the new goal ")
    (if COMMENT-FLAG (newline))
    (display-num-goal (car (pproof-state-to-num-goals)))))

(define (drop-intern num-goals proof maxgoal . x-list)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (names (hypname-info-to-names hypname-info))
	 (i-list
	  (map (lambda (x)
		 (cond ((number? x) x)
		       ((string? x)
			(if (member x names)
			    (name-and-hypname-info-to-index x hypname-info)
			    (myerror "drop" "hypname expected" x)))
		       (else (myerror "drop" "index or hypname expected" x))))
	       x-list))
	 (dropped-indices (if (null? x-list)
			      (let ((avars (context-to-avars context)))
				(do ((l avars (cdr l))
				     (i 1 (+ 1 i))
				     (res '() (cons i res)))
				    ((null? l) (reverse res))))
			      i-list))
	 (new-drop-info (union drop-info dropped-indices))
	 (new-num-goal
	  (make-num-goal (+ 1 maxgoal) goal new-drop-info hypname-info
			 ignore-deco-flag)))
    (make-pproof-state (cons new-num-goal (cdr num-goals))
		       proof
		       (+ 1 maxgoal))))

;; In (drop-except . x-list), x-list is a list of numbers or strings
;; identifying hypotheses from the context.  A new goal is created,
;; which differs from the previous one only in display aspects: all
;; hypotheses except the listed ones are hidden (but still present).

(define (drop-except . x-list)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal)))
    (set! PPROOF-STATE
	  (apply drop-except-intern num-goals proof maxgoal x-list))
    (pproof-state-history-push PPROOF-STATE)
    (display-comment "ok, we now have the new goal ")
    (if COMMENT-FLAG (newline))
    (display-num-goal (car (pproof-state-to-num-goals)))))

(define (drop-except-intern num-goals proof maxgoal . x-list)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (names (hypname-info-to-names hypname-info))
	 (i-list
	  (map (lambda (x)
		 (cond
		  ((number? x) x)
		  ((string? x)
		   (if (member x names)
		       (name-and-hypname-info-to-index x hypname-info)
		       (myerror "drop-except" "hypname expected" x)))
		  (else (myerror
			 "drop-except" "index or hypname expected" x))))
	       x-list))
	 (dropped-indices
	  (let* ((avars (context-to-avars context))
		 (avar-indices (do ((l avars (cdr l))
				    (i 1 (+ 1 i))
				    (res '() (cons i res)))
				   ((null? l) (reverse res)))))
	    (set-minus avar-indices i-list)))
	 (new-drop-info (union drop-info dropped-indices))
	 (new-num-goal
	  (make-num-goal (+ 1 maxgoal) goal new-drop-info hypname-info
			 ignore-deco-flag)))
    (make-pproof-state (cons new-num-goal (cdr num-goals))
		       proof
		       (+ 1 maxgoal))))

;; In (name-hyp i string) a new goal is created, which differs from the
;; previous one only in display aspects: the list (i string) is added to
;; hypname-info.

(define (name-hyp i string)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal)))
    (set! PPROOF-STATE (name-hyp-intern num-goals proof maxgoal i string))
    (pproof-state-history-push PPROOF-STATE)
    (display-comment "ok, we now have the new goal ")
    (if COMMENT-FLAG (newline))
    (display-num-goal (car (pproof-state-to-num-goals)))))

(define (name-hyp-intern num-goals proof maxgoal i string)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (names (hypname-info-to-names hypname-info))
	 (new-hypname-info
	  (cond ((is-used? string '() '())
		 (myerror "name-hyp" "already used" string))
		((member string names)
		 (myerror "name-hyp" "already a hypname" string))
		(else (add-hypname-info i string hypname-info))))
	 (new-num-goal
	  (make-num-goal (+ 1 maxgoal) goal drop-info new-hypname-info
			 ignore-deco-flag)))
    (make-pproof-state (cons new-num-goal (cdr num-goals))
		       proof
		       (+ 1 maxgoal))))

;; (split) expects as goal a conjunction or an AndConst-atom, and
;; splits it into two sub-goals.

(define (split)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal)))
    (set! PPROOF-STATE (split-intern num-goals proof maxgoal))
    (pproof-state-history-push PPROOF-STATE)
    (display-comment "ok, we now have the new goals ")
    (if COMMENT-FLAG (newline))
    (display-num-goal (cadr (pproof-state-to-num-goals)))
    (if COMMENT-FLAG (newline))
    (display-num-goal (car (pproof-state-to-num-goals)))))

(define (split-intern num-goals proof maxgoal)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (goal-formula (goal-to-formula goal))
	 (and-flag (and-form? goal-formula))
	 (andd-flag (andd-form? goal-formula))
	 (andl-flag (andl-form? goal-formula))
	 (andr-flag (andr-form? goal-formula))
	 (andnc-flag (andnc-form? goal-formula))
	 (andb-flag (and (atom-form? goal-formula)
			 (term=? (make-term-in-const-form
				  (pconst-name-to-pconst "AndConst"))
				 (term-in-app-form-to-final-op
				  (atom-form-to-kernel goal-formula)))
			 (= 2 (length (term-in-app-form-to-args
				       (atom-form-to-kernel goal-formula)))))))
    (if (not (or and-flag andd-flag andl-flag andr-flag andnc-flag andb-flag))
	(myerror "split-intern" "conjunction expected" goal-formula))
    (let* ((left-conjunct
	    (cond (and-flag (and-form-to-left goal-formula))
		  (andd-flag (andd-form-to-left goal-formula))
		  (andl-flag (andl-form-to-left goal-formula))
		  (andr-flag (andr-form-to-left goal-formula))
		  (andnc-flag (andnc-form-to-left goal-formula))
		  (andb-flag (make-atomic-formula
			      (car (term-in-app-form-to-args
				    (atom-form-to-kernel goal-formula)))))))
	   (right-conjunct
	    (cond (and-flag (and-form-to-right goal-formula))
		  (andd-flag (andd-form-to-right goal-formula))
		  (andl-flag (andl-form-to-right goal-formula))
		  (andr-flag (andr-form-to-right goal-formula))
		  (andnc-flag (andnc-form-to-right goal-formula))
		  (andb-flag (make-atomic-formula
			      (cadr (term-in-app-form-to-args
				     (atom-form-to-kernel goal-formula)))))))
	   (goalvar-left-formula
	    (context-and-ncvars-and-formula-to-formula
	     context ncvars left-conjunct))
	   (goalvar-right-formula
	    (context-and-ncvars-and-formula-to-formula
	     context ncvars right-conjunct))
	   (goalvar-left (formula-to-new-avar goalvar-left-formula
					      DEFAULT-AVAR-NAME))
	   (goalvar-right (formula-to-new-avar goalvar-right-formula
					       DEFAULT-AVAR-NAME))
	   (ngleft (apply mk-goal-in-elim-form
			  (make-goal-in-avar-form goalvar-left)
			  context))
	   (ngright (apply mk-goal-in-elim-form
			   (make-goal-in-avar-form goalvar-right)
			   context))
	   (np
	    (cond
	     (and-flag (make-proof-in-and-intro-form ngleft ngright))
	     (andd-flag
	      (let* ((idpc (make-idpredconst
			    "AndD"
			    '() ;no types
			    (list (make-cterm (proof-to-formula ngleft))
				  (make-cterm (proof-to-formula ngright)))))
		     (aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
		     (inst-formula (aconst-to-inst-formula aconst))
		     (free (formula-to-free inst-formula)))
		(apply mk-proof-in-elim-form
		       (make-proof-in-aconst-form aconst)
		       (append (map make-term-in-var-form free)
			       (list ngleft ngright)))))
	     (andl-flag
	      (let* ((idpc (make-idpredconst
			    "AndL"
			    '() ;no types
			    (list (make-cterm (proof-to-formula ngleft))
				  (make-cterm (proof-to-formula ngright)))))
		     (aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
		     (inst-formula (aconst-to-inst-formula aconst))
		     (free (formula-to-free inst-formula)))
		(apply mk-proof-in-elim-form
		       (make-proof-in-aconst-form aconst)
		       (append (map make-term-in-var-form free)
			       (list ngleft ngright)))))
	     (andr-flag
	      (let* ((idpc (make-idpredconst
			    "AndR"
			    '() ;no types
			    (list (make-cterm (proof-to-formula ngleft))
				  (make-cterm (proof-to-formula ngright)))))
		     (aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
		     (inst-formula (aconst-to-inst-formula aconst))
		     (free (formula-to-free inst-formula)))
		(apply mk-proof-in-elim-form
		       (make-proof-in-aconst-form aconst)
		       (append (map make-term-in-var-form free)
			       (list ngleft ngright)))))
	     (andnc-flag
	      (let* ((idpc (make-idpredconst
			    "AndNc"
			    '() ;no types
			    (list (make-cterm (proof-to-formula ngleft))
				  (make-cterm (proof-to-formula ngright)))))
		     (aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
		     (inst-formula (aconst-to-inst-formula aconst))
		     (free (formula-to-free inst-formula)))
		(apply mk-proof-in-elim-form
		       (make-proof-in-aconst-form aconst)
		       (append (map make-term-in-var-form free)
			       (list ngleft ngright)))))
	     (andb-flag
	      (mk-proof-in-elim-form
	       atoms-to-and-atom-proof
	       (car (term-in-app-form-to-args
		     (atom-form-to-kernel goal-formula)))
	       (cadr (term-in-app-form-to-args
		      (atom-form-to-kernel goal-formula)))
	       ngleft ngright))))
	   (new-num-leftgoal
	    (make-num-goal
	     (+ 1 maxgoal) ngleft drop-info hypname-info
	     (or ignore-deco-flag (formula-of-nulltype? left-conjunct))))
	   (new-num-rightgoal
	    (make-num-goal
	     (+ 2 maxgoal) ngright drop-info hypname-info
	     (or ignore-deco-flag (formula-of-nulltype? right-conjunct)))))
      (make-pproof-state (cons new-num-leftgoal
			       (cons new-num-rightgoal (cdr num-goals)))
			 (goal-subst (pproof-state-to-proof) goal np)
			 (+ 2 maxgoal)))))

;; We allow multiple split over a conjunctive formula (all conjuncts
;; connected through & which are at the same level are split at once).

(define (msplit)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal)))
    (set! PPROOF-STATE (split-intern num-goals proof maxgoal))
    (pproof-state-history-push PPROOF-STATE)
    (display-comment "ok, we now have the new goals ")
    (if COMMENT-FLAG (newline))
    (display-num-goal (car (pproof-state-to-num-goals)))
    (if COMMENT-FLAG (newline))
    (display-num-goal (cadr (pproof-state-to-num-goals)))
    (let ((new-num-goals (pproof-state-to-num-goals)))
      (set! PPROOF-STATE
	    (make-pproof-state
	     (cons (cadr new-num-goals)
		   (cons (car new-num-goals) (cddr new-num-goals)))
	     (pproof-state-to-proof)
	     (pproof-state-to-maxgoal)))
      (let ((new-goal-formula
	     (goal-to-formula
	      (num-goal-to-goal (car (pproof-state-to-num-goals))))))
	(if (or (and-form? new-goal-formula)
		(andd-form? new-goal-formula)
		(andl-form? new-goal-formula)
		(andr-form? new-goal-formula)
		(andnc-form? new-goal-formula)
		(and (atom-form? new-goal-formula)
		     (term=? (make-term-in-const-form
			      (pconst-name-to-pconst "AndConst"))
			     (term-in-app-form-to-final-op
			      (atom-form-to-kernel new-goal-formula)))
		     (= 2 (length (term-in-app-form-to-args
				   (atom-form-to-kernel new-goal-formula))))))
	    (msplit))))))

;; To be able to work on a goal different from that on top of the stack,
;; we have to move it up using get:

(define (get goal-number)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal)))
    (set! PPROOF-STATE (get-intern num-goals proof maxgoal goal-number) )
    (pproof-state-history-push PPROOF-STATE)
    (display-comment "ok, now the active goal is")
    (if COMMENT-FLAG (newline))
    (display-num-goal (car (pproof-state-to-num-goals)))))

(define (get-intern num-goals proof maxgoal goal-number)
  (let* ((info (assoc goal-number num-goals))
         (num-goal (if info info (myerror "get" "goal number expected"
					  goal-number)))
	 (rest-num-goals
	  (list-transform-positive num-goals
	    (lambda (ng) (not (= (car ng) goal-number))))))
    (make-pproof-state (cons num-goal rest-num-goals) proof maxgoal)))

;; The last n steps of an interactive proof can be made undone using
;; (undo n).  (undo) has the same effect as (undo 1).

(define (undo . x)
  (let ((n (if (null? x) 1 (car x)))
	(l PPROOF-STATE-HISTORY-LENGTH))
    (cond
     ((not (and (integer? n) (positive? n)))
      (myerror "undo" "positive integer expected" n))
     ((< n l)
      (pproof-state-history-pop n)
      (set! PPROOF-STATE (pproof-state-history-head))
      (display-comment "ok, we are back to goal")
      (if COMMENT-FLAG (newline))
      (display-num-goal (car (pproof-state-to-num-goals))))
     (else (myerror "undo" "have not done that many steps" n)))))

;; (undoto n) allows to go back to a previous pproof state whose (top)
;; goal had number n

(define (undoto . x)
  (if (null? x) (myerror "undoto" "no argument given"))
  (let ((n (car x)))
    (if (not (and (integer? n) (positive? n)))
	(myerror "undoto" "positive integer expected" n))
    (do ((hist PPROOF-STATE-HISTORY (cdr hist))
	 (i 0 (+ 1 i)))
	((or (null? hist)
	     (= n (num-goal-to-number
		   (car (pproof-state-to-num-goals (car hist))))))
	 (if (null? hist)
	     (myerror "undoto"
		      "number never denoted a top goal" n)
	     (begin
	       (pproof-state-history-pop i)
	       (set! PPROOF-STATE (pproof-state-history-head))
	       (display-comment "ok, we are back to goal")
	       (if COMMENT-FLAG (newline))
	       (display-num-goal (car (pproof-state-to-num-goals)))))))))

;; As special case of simind we first treat the case when we have a free
;; algebra which is not simultaneously defined.  Then we do not have to
;; provide the all-formula, but rather can take it form to present goal.

;; (ind) expects a goal formula all x A with x of alg type and total.
;; Let c1 ... cn be the constructors of the algebra.  Then n new goals
;; all xs_i(A[x_1i] -> ... -> A[x_ki] -> A[c_i xs_i]) are generated.
;; (ind t) expects a goal A(t).  It computes the algebra rho as type of
;; the term t.  Then again the n new goals above are generated.

(define (ind . opt-term)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (apply ind-intern num-goals proof maxgoal opt-term))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (ind-intern num-goals proof maxgoal . opt-term)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (formula (goal-to-formula goal))
	 (all-formula
          (if (null? opt-term)
	      (cond
	       ((all-form? formula)
		(let* ((var (all-form-to-var formula))
		       (t-deg (var-to-t-deg var)))
		  (if (t-deg-one? t-deg)
		      formula
		      (myerror "ind" "total variable expected" formula))))
	       ((and (allnc-form? formula) (formula-of-nulltype? formula))
		(let* ((var (allnc-form-to-var formula))
		       (kernel (allnc-form-to-kernel formula))
		       (t-deg (var-to-t-deg var))
		       (newvar (if (t-deg-one? t-deg)
				   (var-and-t-deg-to-new-var var t-deg)
				   (myerror "ind" "total variable expected"
					    formula)))
		       (varterm (make-term-in-var-form newvar))
		       (subst-kernel (formula-subst kernel var varterm)))
		  (make-all newvar subst-kernel)))
	       (else (myerror "ind"
			      "allnc form with n.c. goal or all form expected"
			      formula)))
              (let* ((term (car opt-term))
                     (type (if (term-form? term)
			       (term-to-type term)
			       (myerror "ind" "term expected" term)))
                     (t-deg (term-to-t-deg term))
                     (var (if (t-deg-one? t-deg)
                              (type-to-new-var type)
			      (myerror "ind" "total term expected" term)))
		     (varterm (make-term-in-var-form var))
                     (kernel-formula (formula-gen-subst formula term varterm)))
		(make-all var kernel-formula))))
	 (ind-aconst (all-formulas-to-ind-aconst all-formula)) ;includes check
	 (var (all-form-to-var all-formula))
	 (newvar ;makes var usable in the step proofs
	  (if (t-deg-one? (var-to-t-deg var))
	      (var-to-new-var var)
	      (myerror "ind" "total variable expected" var)))
	 (type (var-to-type var))
	 (alg-name (if (alg-form? type)
		       (alg-form-to-name type)
		       (myerror "ind" "variable of algebra type expected"
				var)))
	 (k (length (alg-name-to-typed-constr-names alg-name)))
	 (pproof (if (null? opt-term)
		     (pproof-all-intro
		      (make-pproof-state num-goals proof maxgoal) newvar)
		     (make-pproof-state num-goals proof maxgoal))))
    (apply
     use-with-intern
     (append pproof
             (list (make-proof-in-aconst-form ind-aconst))
	     (map make-term-in-var-form (formula-to-free all-formula))
             (if (null? opt-term)
                 (list (make-term-in-var-form newvar))
                 opt-term)
	     (vector->list (make-vector k DEFAULT-GOAL-NAME))))))

;; pproof-all-intro does an all-intro without changing the maxgoal
;; number.

(define (pproof-all-intro pproof var)
  (let* ((num-goals (pproof-state-to-num-goals pproof))
         (proof (pproof-state-to-proof pproof))
         (maxgoal (pproof-state-to-maxgoal pproof))
         (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
         (goal (num-goal-to-goal num-goal))
         (drop-info (num-goal-to-drop-info num-goal))
         (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
         (ng (make-goal-in-all-elim-form goal var))
         (new-num-goal (make-num-goal maxgoal ng drop-info hypname-info
				      ignore-deco-flag)))
    (make-pproof-state (cons new-num-goal (cdr num-goals))
                       (goal-subst proof goal
                                   (make-proof-in-all-intro-form var ng))
                       maxgoal)))

(define (pproof-all-intros pproof . vars)
  (if (null? vars)
      pproof
      (apply pproof-all-intros
             (pproof-all-intro pproof (car vars))
	     (cdr vars))))

;; pproof-imp-intro does an imp-intro without changing the maxgoal
;; number.

(define (pproof-imp-intro pproof avar)
  (let* ((num-goals (pproof-state-to-num-goals pproof))
         (proof (pproof-state-to-proof pproof))
         (maxgoal (pproof-state-to-maxgoal pproof))
         (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
         (goal (num-goal-to-goal num-goal))
         (drop-info (num-goal-to-drop-info num-goal))
         (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
         (ng (make-goal-in-imp-elim-form goal avar))
         (new-num-goal (make-num-goal maxgoal ng drop-info hypname-info
				      ignore-deco-flag)))
    (make-pproof-state (cons new-num-goal (cdr num-goals))
                       (goal-subst proof goal
                                   (make-proof-in-imp-intro-form avar ng))
                       maxgoal)))

;; (simind) expects a goal formula all x A with x of alg type and
;; total.  We have to provide the other all formulas to be proved
;; simultaneously with the goal.

(define (simind . all-formulas)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply simind-intern num-goals proof maxgoal all-formulas))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (simind-intern num-goals proof maxgoal . all-formulas)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
         (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (formula (goal-to-formula goal))
	 (all-formula (if (all-form? formula)
			  formula
			  (myerror "simind" "all formula expected" formula)))
	 (var (all-form-to-var all-formula))
         (newvar (var-to-new-var var))
	 (type (var-to-type var))
         (all-formula-and-all-formulas (cons all-formula all-formulas))
	 (aconst (apply all-formulas-to-ind-aconst
			all-formula-and-all-formulas))
	 (alg-names
	  (do ((l all-formula-and-all-formulas (cdr l))
	       (res '() (if (all-form? (car l))
			    (let* ((var (all-form-to-var (car l)))
				   (type (var-to-type var)))
			      (if (alg-form? type)
				  (cons (alg-form-to-name type) res)
				  (myerror
				   "simind" "variable of algebra type expected"
				   var)))
			    (myerror "simind" "all formula expected"
				     (car l)))))
	      ((null? l) (reverse res))))
	 (alg-name (car alg-names))
	 (simalg-names (alg-name-to-simalg-names alg-name))
	 (pproof (pproof-all-intro
		  (make-pproof-state num-goals proof maxgoal) newvar)))
    (if ;var total, but not all of all-formulas total
     (not (apply and-op (map (lambda (x)
			       (t-deg-one?
				(var-to-t-deg (all-form-to-var x))))
			     all-formulas)))
     (apply myerror "simind-intern" "all formulas should be total"
	    all-formulas))
    (if (not (equal? alg-names (remove-duplicates alg-names)))
	(apply myerror "simind-intern" "distinct algebras expected" alg-names))
    (if (pair? (set-minus simalg-names alg-names))
	(myerror "simind-intern" "formulas missing for"
		 (set-minus simalg-names alg-names)))
    (if (pair? (set-minus alg-names simalg-names))
	(myerror "simind-intern" "too many alg names"
		 (set-minus alg-names simalg-names)))
    (let* ((typed-constr-names
	    (apply append (map alg-name-to-typed-constr-names alg-names)))
	   (k (length typed-constr-names))
	   (free (apply union (map formula-to-free all-formulas))))
      (apply use-with-intern
	     (append pproof
		     (list (make-proof-in-aconst-form aconst))
		     (map make-term-in-var-form free)
                     (list (make-term-in-var-form newvar))
		     (vector->list (make-vector k DEFAULT-GOAL-NAME)))))))

;; (gind h) expects a goal of the form all xs A(xs) and generates a
;; new goal Prog_h {xs | A(xs)} where h is a term of type rhos=>nat,
;; x_i has type rho_i and Prog_h {xs | A (xs)} =
;; all xs(all ys(h ys<h xs -> A(ys)) -> A(xs)).

;; (gind h t1 .. tn) expects a goal A(ts) and generates the same goal
;; as for (gind h) with the formula all xs A(xs).

(define (gind term . opt-terms)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply gind-intern num-goals proof maxgoal term opt-terms))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (gind-intern num-goals proof maxgoal measure . opt-terms)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
         (goal (num-goal-to-goal num-goal))
         (formula (goal-to-formula goal))
         (types (if (not (term-form? measure))
                    (myerror "gind" "measure term expected" measure)
                    (arrow-form-to-arg-types (term-to-type measure))))
         (m (length types)) ;|rhos|
         (all-formula
          (if (null? opt-terms)
              formula
              (let* ((vars (map (lambda (t)
                                  (if (t-deg-one? (term-to-t-deg t))
                                      (type-to-new-var (term-to-type t))
                                      (myerror "gind" "total terms expected"
                                               t)))
                                opt-terms))
                     (gen-subst (map (lambda (x y)
                                       (list x (make-term-in-var-form y)))
                                     opt-terms vars))
                     (kernel (formula-gen-substitute formula gen-subst)))
                (apply mk-all (append vars (list kernel))))))
         (vars (all-form-to-vars all-formula m))
         (newvars (map var-to-new-var vars)) ;for usability we use fresh vars
         (partial-flag (apply or-op (map (lambda (x)
                                           (t-deg-zero? (var-to-t-deg x)))
                                         vars)))
         (pproof (if partial-flag
                     (myerror "gind" "total variables expected" vars)
                     (apply
                      pproof-all-intros
                      (make-pproof-state num-goals proof maxgoal)
		      (list-tail newvars (length opt-terms))))))
    (cond ((not (equal? (arrow-form-to-final-val-type (term-to-type measure))
                        (py "nat")))
           (myerror "gind"
                    "the expected value type of the measure term is nat, not"
                    (arrow-form-to-final-val-type (term-to-type measure))))
          ((not (equal? types
                        (map var-to-type
                             (all-form-to-vars all-formula m))))
           (myerror "gind" types
                    "are the expected types of the variables in"
                    all-formula))
          (else
           (apply
            use-with-intern
            (append pproof
                    (list (make-proof-in-aconst-form
                           (all-formula-and-number-to-gind-aconst
			    all-formula m)))
                    (map make-term-in-var-form (formula-to-free all-formula))
                    (cons measure
                          (if (pair? opt-terms)
                              opt-terms
                              '()))
                    (map make-term-in-var-form
                         (list-tail newvars (length opt-terms)))
                    (list DEFAULT-GOAL-NAME)
                    (list (pt "True")
                          (make-proof-in-aconst-form truth-aconst))))))))

;; Introduction for inductively defined predicates

(define (intro i . terms)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply intro-intern num-goals proof maxgoal i terms))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (intro-intern num-goals proof maxgoal i . terms)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (formula (goal-to-formula goal))
	 (idpredconst
	  (if (predicate-form? formula)
	      (let ((pred (predicate-form-to-predicate formula)))
		(if (idpredconst-form? pred)
		    pred
		    (myerror "intro" "idpredconst expected" pred)))
	      (myerror "intro" "predicate expected" formula)))
	 (intro-aconst (number-and-idpredconst-to-intro-aconst i idpredconst)))
    (apply use-intern
	   num-goals proof maxgoal (make-proof-in-aconst-form intro-aconst)
	   terms)))

(define (intro-with i . x-list)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply intro-with-intern num-goals proof maxgoal i x-list))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (intro-with-intern num-goals proof maxgoal i . x-list)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (formula (goal-to-formula goal))
	 (idpredconst
	  (if (predicate-form? formula)
	      (let ((pred (predicate-form-to-predicate formula)))
		(if (idpredconst-form? pred)
		    pred
		    (myerror "intro-with" "idpredconst expected" pred)))
	      (myerror "intro-with" "predicate expected" formula)))
	 (intro-aconst (number-and-idpredconst-to-intro-aconst i idpredconst)))
    (apply use-with-intern
	   num-goals proof maxgoal (make-proof-in-aconst-form intro-aconst)
	   x-list)))

;; Recall that I rs provides
;; - a type substitution,
;; - a predicate instantiation, and
;; - the list rs of argument terms.

;; In (elim idhyp) idhyp is, with an inductively defined predicate I,
;; - a number or string identifying a hypothesis I rs form the context
;; - the name of a global assumption or theorem I rs;
;; - a closed proof of a formula I rs;
;; - a formula I rs with free variables from the context, generating a
;;   new goal.
;; Then the (strengthened) elimination axiom is used with rs for xs and
;; idhyp for I rs to prove the goal A(rs), leaving the instantiated
;; (with {xs|A(xs)}) clauses as new goals.

;; (elim) expects an inst-imp-formula I rs -> A(rs) as goal.  Then the
;; (strengthened) instantiated (with {xs|A(xs)}) clauses are new goals.

;; In case of simultaneously inductively defined predicate constants we
;; can provide other imp-formulas to be proved simultaneously with the
;; given one.  Then the (strengthened) simplified clauses are generated
;; as new goals.

(define (elim . opt-idhyp-and-imp-formulas)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply elim-intern
		 num-goals proof maxgoal
		 opt-idhyp-and-imp-formulas))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (elim-intern num-goals proof maxgoal . opt-idhyp-and-imp-formulas)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (l (length avars))
	 (goal-formula (goal-to-formula goal))
	 (opt-idhyp
	  (if (and (pair? opt-idhyp-and-imp-formulas)
		   (not (imp-form? (car opt-idhyp-and-imp-formulas))))
	      (list (car opt-idhyp-and-imp-formulas))
	      '()))
	 (imp-formulas
	  (if (and (pair? opt-idhyp-and-imp-formulas)
		   (not (imp-form? (car opt-idhyp-and-imp-formulas))))
	      (cdr opt-idhyp-and-imp-formulas)
	      opt-idhyp-and-imp-formulas))
	 (id-formula-and-idhyp1
	  (if
	   (null? opt-idhyp)
	   (list (if (imp-form? goal-formula)
		     (imp-form-to-premise goal-formula)
		     (myerror "elim" "implication expected" goal-formula))
		 #f)
	   (let ((idhyp (car opt-idhyp)))
	     (cond
	      ((and (integer? idhyp) (positive? idhyp))
	       (if (<= idhyp l)
		   (let* ((avar (list-ref avars (- idhyp 1)))
			  (formula (avar-to-formula avar)))
		     (list formula (make-proof-in-avar-form avar)))
		   (myerror "elim" "assumption number expected" idhyp)))
	      ((and (string? idhyp)
		    (member idhyp (hypname-info-to-names hypname-info)))
	       (let ((i (name-and-hypname-info-to-index idhyp hypname-info)))
		 (if (<= i l)
		     (let* ((avar (list-ref avars (- i 1)))
			    (formula (avar-to-formula avar)))
		       (list formula (make-proof-in-avar-form avar)))
		     (myerror "elim" "assumption number expected" i))))
	      ((and (string? idhyp) (assoc idhyp THEOREMS))
	       (let* ((aconst (theorem-name-to-aconst idhyp))
		      (formula (aconst-to-formula aconst)))
		 (list formula (make-proof-in-aconst-form aconst))))
	      ((and (string? idhyp) (assoc idhyp GLOBAL-ASSUMPTIONS))
	       (let* ((aconst (global-assumption-name-to-aconst idhyp))
		      (formula (aconst-to-formula aconst)))
		 (list formula (make-proof-in-aconst-form aconst))))
	      ((proof-form? idhyp) (list (proof-to-formula idhyp) idhyp))
	      ((formula-form? idhyp) ;then a new goal is created
	       (list idhyp DEFAULT-GOAL-NAME))
	      (else (myerror "elim" "illegal argument" idhyp))))))
	 (id-formula (car id-formula-and-idhyp1))
	 (idhyp1 (cadr id-formula-and-idhyp1))
	 (inst-imp-formula (if (null? opt-idhyp)
			       goal-formula
			       (make-imp id-formula goal-formula)))
	 (idpredconst (if (predicate-form? id-formula)
			  (predicate-form-to-predicate id-formula)
			  (myerror "elim-intern" "predicate form expected"
				   id-formula)))
	 (name (idpredconst-to-name idpredconst))
	 (test1 ;for an inductive but not coinductive predicate
	  (let ((pred (predicate-form-to-predicate id-formula)))
	    (if (not (idpredconst-form? pred))
		(myerror "elim-intern" "idpredconst form expected" id-formula)
		(let ((name (idpredconst-to-name pred)))
		  (if (not (assoc name IDS))
		      (myerror "elim-intern" "inductive predicate expected"
			       id-formula)
		      (if (assoc name COIDS)
			  (myerror
			   "elim-intern"
			   "inductive (not coinductive) predicate expected"
			   id-formula)))))))
	 (test2 ;one-clause-nc
	   (if (and (nc-idpredconst-name? name)
		    (< 1 (length (idpredconst-name-to-clauses name)))
		    (not (formula-of-nulltype? goal-formula)))
	       (myerror	"elim-intern"
			"non-computational multi-clause idpreconst" name
			"expects a non-computational competitor" goal-formula)))
	 (arity (idpredconst-to-arity idpredconst))
	 (args (predicate-form-to-args id-formula))
	 (types (arity-to-types arity))
	 (t-degs (map term-to-t-deg args))
	 (vars (map (lambda (type t-deg)
		      (if (t-deg-zero? t-deg)
			  (type-to-new-partial-var type)
			  (type-to-new-var type)))
		    types t-degs))
	 (varterms (map make-term-in-var-form vars))
	 (imp-formula (formula-gen-substitute
		       inst-imp-formula (map list args varterms)))
	 (inst-imp-formula-test
	  (if (not (classical-formula=?
		    inst-imp-formula
		    (formula-substitute imp-formula (map list vars args))))
	      (myerror "elim" "elim-aconst not computable from"
		       inst-imp-formula)))
	 (elim-aconst (apply imp-formulas-to-elim-aconst
			     imp-formula imp-formulas))
	 (mr? (mr-idpredconst-name? (idpredconst-to-name idpredconst)))
	 (inst-elim-formula ;Ij xs^ -> K1(Is,Cs) ->..-> Kk(Is,Cs) -> Cj rs
					;if mr?: allnc x^(Ij xs^ x^ -> .. -> Cj
	  (aconst-to-inst-formula elim-aconst))
	 (free (formula-to-free inst-elim-formula))
	 (prem ;if mr? then Ij xs^ x^ else Ij xs^
	  (if mr? (imp-form-to-premise (allnc-form-to-kernel inst-elim-formula))
	      (imp-form-to-premise inst-elim-formula)))
	 (new-arg-vars ;if mr? then xs^ x^ else xs^
	  (map term-in-var-form-to-var (predicate-form-to-args prem)))
	 (proper-new-arg-vars ;xs^
	  (if mr? (reverse (cdr (reverse new-arg-vars))) new-arg-vars))
	 (idpc-vars ;internal for the cterms in idpc
	  (set-minus (formula-to-free prem) new-arg-vars))
	 (rest-vars (set-minus free (append idpc-vars proper-new-arg-vars)))
	 (elim-terms
	  (if mr? (append (map make-term-in-var-form idpc-vars)
			  (reverse (cdr (reverse args)))
			  (map make-term-in-var-form rest-vars)
			  (list (car (reverse args))))
	      (append (map make-term-in-var-form idpc-vars)
		      args
		      (map make-term-in-var-form rest-vars))))
	 (uninst-elim-formula
	  (if mr? (all-form-to-kernel (aconst-to-uninst-formula elim-aconst))
	      (aconst-to-uninst-formula elim-aconst)))
	 (k (- (length (imp-form-to-premises uninst-elim-formula))
	       1)))
    (if
     (null? opt-idhyp)
     (let* ((avar (formula-to-new-avar id-formula))
	    (pproof (pproof-imp-intro
		     (make-pproof-state num-goals proof maxgoal)
		     avar)))
       (apply use-with-intern
	      (append pproof
		      (list (make-proof-in-aconst-form elim-aconst))
		      elim-terms
		      (list (make-proof-in-avar-form avar))
		      (vector->list (make-vector k DEFAULT-GOAL-NAME)))))
     (apply use-with-intern
	    num-goals proof maxgoal (make-proof-in-aconst-form elim-aconst)
	    (append elim-terms
		    (list idhyp1)
		    (vector->list (make-vector k DEFAULT-GOAL-NAME)))))))

;; In the following definition of inversion, x is one of the following.
;; - A number or string identifying a hypothesis I rs form the context.
;; - The name of a theorem or global assumption stating I rs
;; - A closed proof of I rs
;; - A formula I rs with free vars from the context, generating a new goal.

;; imp-formulas have the form J ss -> B.  Here I,J are inductively
;; defined predicates, with clauses K1 ... Kn.  One uses the elim-aconst
;; for I xs -> xs=rs -> goal and the additional implications J ys ->
;; ys=ss -> B, with ? ... ?  for the clauses, rs for xs and proofs for
;; rs=rs, to obtain the goal.  Then many of the generated goals for the
;; clauses will contain false premises, coming from substituted
;; equations xs=rs, and are proved automatically.

;; imp-formulas not provided are taken as J xs -> J xs.  Generated
;; clauses for such J are proved automatically from the intro axioms
;; (the rec-prems are not needed).

;; For simultaneous inductively defined predicates simplified-inversion
;; does not add imp-formulas J xs -> J xs to form the elim-aconst.
;; Then the (new) imp-formulas-to-uninst-elim-formulas-etc generates
;; simplified clauses.  In some special cases this suffices.

(define (inversion x . imp-formulas)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply inversion-intern num-goals proof maxgoal x imp-formulas))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (inversion-intern num-goals proof maxgoal x . imp-formulas)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (goal-formula (goal-to-formula goal))
	 (prem (if (formula-form? x) x (hyp-info-to-formula num-goal x)))
	 (imp-formula (make-imp prem goal-formula))
	 (imp-formula-and-imp-formulas (cons imp-formula imp-formulas))
	 (prems (map (lambda (formula)
		       (if (imp-form? formula)
			   (imp-form-to-premise formula)
			   (myerror "inversion"
				    "implication expected" formula)))
		     imp-formula-and-imp-formulas))
	 (concls (map imp-form-to-conclusion imp-formula-and-imp-formulas))
	 (preds (map (lambda (prem)
		       (if (predicate-form? prem)
			   (predicate-form-to-predicate prem)
			   (myerror "inversion" "predicate expected" prem)))
		     prems))
	 (idpredconsts
	  (map (lambda (pred prem)
		 (if (idpredconst-form? pred) pred
		     (myerror "inversion"
			      "inductively defined predicate expected"
			      prem)))
	       preds prems))
	 (names (map idpredconst-to-name idpredconsts))
	 (name (car names))
	 (simidpc-names (idpredconst-name-to-simidpc-names name))
	 (added-names (set-minus simidpc-names names))
	 (types (idpredconst-to-types (car preds)))
	 (cterms (idpredconst-to-cterms (car preds)))
	 (added-idpcs (map (lambda (name)
			     (make-idpredconst name types cterms))
			   added-names))
	 (added-arities (map (lambda (idpc) (idpredconst-to-arity idpc))
			     added-idpcs))
	 (added-type-lists (map arity-to-types added-arities))
	 (added-var-lists (map (lambda (types)
				 (map type-to-new-partial-var types))
			       added-type-lists))
	 (added-varterm-lists (map (lambda (vars)
				     (map make-term-in-var-form vars))
				   added-var-lists))
	 (added-imp-formulas
	  (map (lambda (pred varterms)
		 (let ((predicate-formula (apply make-predicate-formula
						 pred varterms)))
		   (make-imp predicate-formula predicate-formula)))
	       added-idpcs added-varterm-lists))
	 (arg-lists (map predicate-form-to-args prems))
	 (type-lists (map (lambda (args) (map term-to-type args))
			  arg-lists))
	 (var-lists (map (lambda (types) (map type-to-new-partial-var types))
			 type-lists))
	 (varterm-lists (map (lambda (vars) (map make-term-in-var-form vars))
			     var-lists))
	 (eq-lists (map (lambda (varterms args types)
			  (map (lambda (varterm arg type)
				 (if (finalg? type)
				     (make-= arg varterm)
				     (make-eqd arg varterm)))
			       varterms args types))
			varterm-lists arg-lists type-lists))
	 (new-imp-formulas
	  (map (lambda (pred varterms eqs concl)
		 (apply mk-imp (apply make-predicate-formula pred varterms)
			(append eqs (list concl))))
	       preds varterm-lists eq-lists concls))
	 (elim-aconst (apply imp-formulas-to-elim-aconst
			     (append new-imp-formulas added-imp-formulas)))
	 (free (formula-to-free (aconst-to-inst-formula elim-aconst)))
	 (args (car arg-lists))
	 (rest-of-free (list-tail free (length args)))
	 (instantiated-elim-proof
	  (apply mk-proof-in-elim-form
		 (make-proof-in-aconst-form elim-aconst)
		 (append args (map make-term-in-var-form
				   rest-of-free))))
	 (k (length (apply append (map idpredconst-name-to-clauses
				       simidpc-names))))
	 (strengthened-clauses (cdr (imp-form-to-premises
                                     (proof-to-formula
                                      instantiated-elim-proof) (+ k 1))))
	 (eqd-proofs
	  (map (lambda (arg type)
		 (if (finalg? type)
		     (make-proof-in-aconst-form truth-aconst)
		     (let* ((idpc (make-idpredconst "EqD" (list type) '()))
			    (initeqd-aconst ;all a a eqd a
			     (number-and-idpredconst-to-intro-aconst 0 idpc)))
		       (mk-proof-in-elim-form
			(make-proof-in-aconst-form initeqd-aconst) arg))))
	       (car arg-lists) (car type-lists)))
	 (scl-lists ;one for each of simidpc-names
	  (do ((names simidpc-names (cdr names))
	       (res-and-l
		(list '() strengthened-clauses)
		(let* ((name (car names))
		       (number-of-clauses
			(length (idpredconst-name-to-clauses name)))
		       (res (car res-and-l))
		       (l (cadr res-and-l)))
		  (list (cons (list-head l number-of-clauses) res)
			(list-tail l number-of-clauses)))))
	      ((null? names) (reverse (car res-and-l)))))
	 (clause-proofs
	  (apply append
		 (map (lambda (name scls)
			(if (member name added-names)
			    (let ((idpc (make-idpredconst name types cterms)))
			      (do ((i 0 (+ 1 i))
				   (l scls (cdr l))
				   (res '() (cons (added-scl-etc-to-proof
						   (car l) i idpc) res)))
				  ((null? l) (reverse res))))
			    (map (lambda (scl)
				   (let ((test (formula-to-efq-proof-or-f scl)))
				     (if test test DEFAULT-GOAL-NAME)))
				 scls)))
		      simidpc-names scl-lists))))
    (if (not (equal? names (remove-duplicates names)))
	(apply myerror "inversion" "distinct names expected" names))
    (if (pair? (set-minus names simidpc-names))
	(apply myerror
	       "inversion" "superfluous formulas for"
	       (set-minus names simidpc-names)))
    (apply use-with-intern
	   num-goals proof maxgoal instantiated-elim-proof x
	   (append clause-proofs
		   eqd-proofs))))

(define (simplified-inversion x . imp-formulas)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (apply simplified-inversion-intern
			      num-goals proof maxgoal x imp-formulas))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (simplified-inversion-intern num-goals proof maxgoal x . imp-formulas)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (goal-formula (goal-to-formula goal))
	 (prem (if (formula-form? x) x (hyp-info-to-formula num-goal x)))
	 (imp-formula (make-imp prem goal-formula))
	 (imp-formula-and-imp-formulas (cons imp-formula imp-formulas))
	 (prems (map (lambda (formula)
		       (if (imp-form? formula)
			   (imp-form-to-premise formula)
			   (myerror "simplified-inversion"
				    "implication expected" formula)))
		     imp-formula-and-imp-formulas))
	 (concls (map imp-form-to-conclusion imp-formula-and-imp-formulas))
	 (preds (map (lambda (prem)
		       (if (predicate-form? prem)
			   (predicate-form-to-predicate prem)
			   (myerror "simplified-inversion"
				    "predicate expected" prem)))
		     prems))
	 (idpredconsts
	  (map (lambda (pred prem)
		 (if (idpredconst-form? pred) pred
		     (myerror "simplified-inversion"
			      "inductively defined predicate expected"
			      prem)))
	       preds prems))
	 (names (map idpredconst-to-name idpredconsts))
	 (name (car names))
	 (simidpc-names (idpredconst-name-to-simidpc-names name))
	 (types (idpredconst-to-types (car preds)))
	 (cterms (idpredconst-to-cterms (car preds)))
	 (arg-lists (map predicate-form-to-args prems))
	 (type-lists (map (lambda (args) (map term-to-type args))
			  arg-lists))
	 (var-lists (map (lambda (types) (map type-to-new-partial-var types))
			 type-lists))
	 (varterm-lists (map (lambda (vars) (map make-term-in-var-form vars))
			     var-lists))
	 (eq-lists (map (lambda (varterms args types)
			  (map (lambda (varterm arg type)
				 (if (finalg? type)
				     (make-= arg varterm)
				     (make-eqd arg varterm)))
			       varterms args types))
			varterm-lists arg-lists type-lists))
	 (new-imp-formulas
	  (map (lambda (pred varterms eqs concl)
		 (apply mk-imp
			(apply make-predicate-formula pred varterms)
			(append eqs (list concl))))
	       preds varterm-lists eq-lists concls))
	 (elim-aconst (apply imp-formulas-to-elim-aconst new-imp-formulas))
	 (free (formula-to-free (aconst-to-inst-formula elim-aconst)))
	 (args (car arg-lists))
	 (rest-of-free (list-tail free (length args)))
	 (inst-elim-proof
	  (apply mk-proof-in-elim-form
		 (make-proof-in-aconst-form elim-aconst)
		 (append args (map make-term-in-var-form
				   rest-of-free))))
	 (k (- (length (imp-form-to-premises
			(aconst-to-uninst-formula elim-aconst)))
	       1))
	 (clauses (cdr (imp-form-to-premises
			(proof-to-formula inst-elim-proof) (+ k 1))))
	 (eqd-proofs
	  (map (lambda (arg type)
		 (if (finalg? type)
		     (make-proof-in-aconst-form truth-aconst)
		     (let* ((idpc (make-idpredconst "EqD" (list type) '()))
			    (initeqd-aconst ;all a a eqd a
			     (number-and-idpredconst-to-intro-aconst 0 idpc)))
		       (mk-proof-in-elim-form
			(make-proof-in-aconst-form initeqd-aconst) arg))))
	       (car arg-lists) (car type-lists)))
	 (clause-proofs (map (lambda (clause)
			       (let ((test (formula-to-efq-proof-or-f clause)))
				 (if test test DEFAULT-GOAL-NAME)))
			     clauses)))
    (if (not (equal? names (remove-duplicates names)))
	(apply myerror
	       "simplified-inversion" "distinct names expected" names))
    (if (pair? (set-minus names simidpc-names))
	(apply myerror
	       "simplified-inversion" "superfluous formulas for"
	       (set-minus names simidpc-names)))
    (apply use-with-intern
	   num-goals proof maxgoal inst-elim-proof x
	   (append clause-proofs eqd-proofs))))

(define (added-scl-etc-to-proof scl i idpc)
  (let* ((intro-aconst (number-and-idpredconst-to-intro-aconst i idpc))
	 (uninst-clause (aconst-to-uninst-formula intro-aconst))
	 (orig-kernel (all-allnc-form-to-final-kernel uninst-clause))
	 (number-of-orig-nc-prems
	  (length (impnc-form-to-premises orig-kernel)))
	 (number-of-orig-prems
	  (length (imp-form-to-premises (impnc-form-to-final-conclusion
					 orig-kernel))))
	 (ncvars (allnc-form-to-vars scl))
	 (vars (all-form-to-vars (allnc-form-to-final-kernel scl)))
	 (scl-total-prems (imp-form-to-premises
			   (all-form-to-final-kernel
			    (allnc-form-to-final-kernel scl))))
	 (scl-nc-prems (list-head scl-total-prems number-of-orig-nc-prems))
	 (scl-prems (list-head
		     (list-tail scl-total-prems number-of-orig-nc-prems)
		     number-of-orig-prems))
	 (rec-scl-prems (list-tail scl-total-prems
				   (+ number-of-orig-nc-prems
				      number-of-orig-prems)))
	 (scl-nc-prem-avars (map formula-to-new-avar scl-nc-prems))
	 (scl-prem-avars (map formula-to-new-avar scl-prems))
	 (rec-scl-prem-avars (map formula-to-new-avar rec-scl-prems))
	 (concl-proof
	  (apply mk-proof-in-elim-form
		 (make-proof-in-aconst-form intro-aconst)
		 (append
		  (map make-term-in-var-form ncvars)
		  (map make-term-in-var-form vars)
		  (map make-proof-in-avar-form scl-nc-prem-avars)
		  (map make-proof-in-avar-form scl-prem-avars)))))
    (apply
     mk-proof-in-nc-intro-form
     (append
      ncvars
      (list (apply
	     mk-proof-in-intro-form
	     (append
	      vars
	      (list (apply
		     mk-proof-in-nc-intro-form
		     (append
		      scl-nc-prem-avars
		      (list (apply
			     mk-proof-in-intro-form
			     (append
			      scl-prem-avars rec-scl-prem-avars
			      (list concl-proof))))))))))))))

;; Now for coinduction (i.e., applications of the greatest fixed point
;; axioms Gfp).

;; Recall that J rs provides
;; - a type substitution,
;; - a predicate instantiation, and
;; - the list rs of argument terms.

;; (coind hyp) expects a goal J rs, with a coinductively defined
;; predicate J, and hyp is expected to be
;; - a number or string identifying a hypothesis A(rs) form the context;
;; - the name of a global assumption or theorem A(rs);
;; - a closed proof of a formula A(rs);
;; - a formula A(rs) with free variables from the context, generating a
;;   new goal.
;; (coind) expects an inst-imp-formula A(rs) -> J rs as goal.  Then the
;; Gfp axiom for J is used: P xs -> all xs(P xs -> C(P)) -> J xs with
;; C(J) the defining clause for J.  Substitute {xs|A(xs)} for P, and
;; use A(xs) -> all xs(A(xs) -> C({xs|A(xs)})) -> J xs (i.e., its
;; universal closure).  After an appropriate application (rs for xs) we
;; are left with a new goal saying that {xs|A(xs)} satisfies the
;; defining clause for J.

;; In case of simultaneous coinductively defined predicates we can
;; provide other imp-formulas to be proved simultaneously with the
;; given one.  Then their clauses are generated as new goals.

(define (coind . opt-hyp-and-imp-formulas)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply coind-intern
		 num-goals proof maxgoal opt-hyp-and-imp-formulas))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (coind-intern num-goals proof maxgoal . opt-hyp-and-imp-formulas)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (l (length avars))
	 (goal-formula (goal-to-formula goal))
	 (coidpc-formula (imp-form-to-final-conclusion goal-formula))
	 (coidpredconst
	  (if (and (predicate-form? coidpc-formula)
		   (idpredconst-form?
		    (predicate-form-to-predicate coidpc-formula)))
	      (predicate-form-to-predicate coidpc-formula)
	      (myerror "coind" "coinductively defined prime formula expected"
		       coidpc-formula)))
	 (name (idpredconst-to-name coidpredconst))
	 (simidpc-names (idpredconst-name-to-simidpc-names name))
	 (opt-hyp?
	  (= (length simidpc-names) (length opt-hyp-and-imp-formulas)))
	 (hyp-formula-and-hyp1
	  (if
	   (not opt-hyp?)
	   (list (if (imp-form? goal-formula)
		     (imp-form-to-premise goal-formula)
		     (myerror "coind" "implication expected" goal-formula))
		 #f)
	   (let ((hyp (car opt-hyp-and-imp-formulas)))
	     (cond
	      ((and (integer? hyp) (positive? hyp))
	       (if (<= hyp l)
		   (let* ((avar (list-ref avars (- hyp 1)))
			  (formula (avar-to-formula avar)))
		     (list formula (make-proof-in-avar-form avar)))
		   (myerror "coind" "assumption number expected" hyp)))
	      ((and (string? hyp)
		    (member hyp (hypname-info-to-names hypname-info)))
	       (let ((i (name-and-hypname-info-to-index hyp hypname-info)))
		 (if (<= i l)
		     (let* ((avar (list-ref avars (- i 1)))
			    (formula (avar-to-formula avar)))
		       (list formula (make-proof-in-avar-form avar)))
		     (myerror "coind" "assumption number expected" i))))
	      ((and (string? hyp) (assoc hyp THEOREMS))
	       (let* ((aconst (theorem-name-to-aconst hyp))
		      (formula (aconst-to-formula aconst)))
		 (list formula (make-proof-in-aconst-form aconst))))
	      ((and (string? hyp) (assoc hyp GLOBAL-ASSUMPTIONS))
	       (let* ((aconst (global-assumption-name-to-aconst hyp))
		      (formula (aconst-to-formula aconst)))
		 (list formula (make-proof-in-aconst-form aconst))))
	      ((proof-form? hyp) (list (proof-to-formula hyp) hyp))
	      ((formula-form? hyp) ;then a new goal is created
	       (list hyp DEFAULT-GOAL-NAME))
	      (else (myerror "coind" "illegal argument" hyp))))))
	 (hyp-formula (car hyp-formula-and-hyp1))
	 (hyp1 (cadr hyp-formula-and-hyp1))
	 (inst-imp-formula (if opt-hyp?
			       (make-imp hyp-formula goal-formula)
			       goal-formula))
	 (arity (idpredconst-to-arity coidpredconst))
	 (args (predicate-form-to-args coidpc-formula))
	 (vars (map (lambda (arg)
		      (let ((t-deg (term-to-t-deg arg))
			    (type (term-to-type arg)))
			(if (t-deg-zero? t-deg)
			    (type-to-new-partial-var type)
			    (type-to-new-var type))))
		    args))
	 (varterms (map make-term-in-var-form vars))
	 (imp-formula (formula-gen-substitute
		       inst-imp-formula (map list args varterms)))
	 (inst-imp-formula-test
	  (if (not (classical-formula=?
		    inst-imp-formula
		    (formula-substitute imp-formula (map list vars args))))
	      (myerror "coind" "gfp-aconst not computable from"
		       inst-imp-formula)))
	 (imp-formulas (if opt-hyp?
			   (cdr opt-hyp-and-imp-formulas)
			   opt-hyp-and-imp-formulas))
	 (test ;imp-formula and imp-formulas are as expected
	  (if
	   (and
	    (apply and-op (map imp-form? (cons imp-formula imp-formulas)))
	    (let ((concls (map imp-form-to-conclusion
			       (cons imp-formula imp-formulas))))
	      (and
	       (apply and-op (map predicate-form? concls))
	       (let ((preds (map predicate-form-to-predicate concls))
		     (args-list (map predicate-form-to-args concls)))
		 (and
		  (apply and-op (map idpredconst-form? preds))
		  (apply and-op (map (lambda (args)
				       (apply and-op
					      (map term-in-var-form? args)))
				     args-list))
		  (let ((names (map idpredconst-to-name preds))
			(cterms-list (map idpredconst-to-cterms preds))
			(types-list (map idpredconst-to-types preds)))
		    (and
		     (null? (set-minus-wrt string=? names simidpc-names))
		     (null? (set-minus-wrt string=? simidpc-names names))
		     (= 1 (length (remove-duplicates cterms-list)))
		     (= 1 (length (remove-duplicates types-list))))))))))
	   'ok
	   (apply myerror
		  "coind-intern" "imp-formulas expected" imp-formula
		  imp-formulas)))
	 (gfp-aconst (apply imp-formulas-to-gfp-aconst
			    imp-formula imp-formulas))
	 (inst-gfp-formula ;Aj(xs) -> K1(Js,As) ->..-> Kk(Js,As) -> J xs
	  (aconst-to-inst-formula gfp-aconst))
	 (free (formula-to-free (imp-form-to-final-conclusion
				 inst-gfp-formula)))
	 ;; (free (formula-to-free inst-gfp-formula))
	 (coidpc-vars (map term-in-var-form-to-var
			   (predicate-form-to-args
			    (imp-form-to-final-conclusion inst-gfp-formula))))
	 (vars-args-alist (map (lambda (var arg) (list var arg))
			       coidpc-vars args))
	 (free-terms-with-args-for-vars
	  (map (lambda (x)
		 (let ((info (assoc x vars-args-alist)))
		   (if info
		       (cadr info)
		       (make-term-in-var-form x))))
	       free))
	 (k (- (length (imp-form-to-premises
			(aconst-to-uninst-formula gfp-aconst)))
	       1)))
    (if
     (not opt-hyp?)
     (let* ((avar (formula-to-new-avar hyp-formula))
	    (pproof (pproof-imp-intro
		     (make-pproof-state num-goals proof maxgoal)
		     avar)))
       (apply use-with-intern
	      (append pproof
		      (list (make-proof-in-aconst-form gfp-aconst))
		      free-terms-with-args-for-vars
		      (list (make-proof-in-avar-form avar))
		      (vector->list (make-vector k DEFAULT-GOAL-NAME)))))
     (apply use-with-intern
	    num-goals proof maxgoal (make-proof-in-aconst-form gfp-aconst)
	    (append free-terms-with-args-for-vars
		    (list hyp1)
		    (vector->list (make-vector k DEFAULT-GOAL-NAME)))))))

;; To simplify proofs by coinduction we provide

(define (imp-formulas-to-coind-proof imp-formula . imp-formulas)
  (map (lambda (imp-fla)
	 (if (and (formula-of-nulltype? (imp-form-to-premise imp-fla))
		  (not (formula-of-nulltype? (imp-form-to-conclusion imp-fla))))
	     (myerror "imp-formulas-to-coind-proof"
		      "c.r. premise expected in" imp-fla)))
       (cons imp-formula imp-formulas))
  (let* ((aconst (apply imp-formulas-to-gfp-aconst imp-formula imp-formulas))
	 (aconst-fla (aconst-to-formula aconst))
	 (aconst-vars (all-allnc-form-to-vars aconst-fla))
	 (aconst-kernel (all-allnc-form-to-final-kernel aconst-fla))
	 (aconst-prems (imp-impnc-form-to-premises aconst-kernel))
	 (coind-fla (car aconst-prems))
	 (coind-steps (cdr aconst-prems))
	 (coind-fla-avar (formula-to-new-avar coind-fla))
	 (coind-step-avars (map formula-to-new-avar coind-steps)))
    (apply
     mk-proof-in-intro-form
     (append
      coind-step-avars
      (list
       (apply
	mk-proof-in-nc-intro-form
	(append
	 aconst-vars
	 (list
	  (make-proof-in-imp-intro-form
	   coind-fla-avar
	   (apply
	    mk-proof-in-elim-form
	    (make-proof-in-aconst-form aconst)
	    (append
	     (map make-term-in-var-form aconst-vars)
	     (map make-proof-in-avar-form
		  (cons coind-fla-avar coind-step-avars)))))))))))))

;; ex-intro and ex-elim can be used in interactive proofs.

(define (ex-intro string-or-term)
  (let ((term (if (string? string-or-term)
		  (pt string-or-term)
		  string-or-term)))
    (if (not (term-form? term))
	(myerror "ex-intro" "term expected" term))
    (let* ((num-goals (pproof-state-to-num-goals))
	   (proof (pproof-state-to-proof))
	   (maxgoal (pproof-state-to-maxgoal))
	   (number
	    (num-goal-to-number
	     (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
      (set! PPROOF-STATE (ex-intro-intern num-goals proof maxgoal term))
      (pproof-state-history-push PPROOF-STATE)
      (display-new-goals num-goals number))))

(define (ex-intro-intern num-goals proof maxgoal term)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (formula (goal-to-formula goal))
	 (free (if (ex-form? formula)
                   (formula-to-free formula)
                   (myerror "ex-intro" "existential goal expected"))))
    (apply use-with-intern
	   num-goals proof maxgoal
	   (make-proof-in-aconst-form (ex-formula-to-ex-intro-aconst formula))
	   (append (map make-term-in-var-form free)
		   (list term DEFAULT-GOAL-NAME)))))

;; In the following definition of ex-elim x is
;; - a number or string identifying an existential hypothesis form the context,
;; - the name of an existential global assumption or theorem,
;; - a closed proof of an existential formula (closed ones suffice),
;; - an existential formula with free variables from the context,
;;   generating a new goal.

(define (ex-elim x)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (ex-elim-intern num-goals proof maxgoal x))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (ex-elim-intern num-goals proof maxgoal x)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (l (length avars))
	 (goal-formula (goal-to-formula goal))
	 (ex-formula-and-x1
	  (cond
	   ((and (integer? x) (positive? x))
	    (if (<= x l)
		(let* ((avar (list-ref avars (- x 1)))
		       (formula (avar-to-formula avar)))
		  (list formula (make-proof-in-avar-form avar)))
		(myerror "ex-elim" "assumption number expected" x)))
	   ((and (string? x)
		 (member x (hypname-info-to-names hypname-info)))
	    (let ((i (name-and-hypname-info-to-index x hypname-info)))
	      (if (<= i l)
		  (let* ((avar (list-ref avars (- i 1)))
			 (formula (avar-to-formula avar)))
		    (list formula (make-proof-in-avar-form avar)))
		  (myerror "ex-elim" "assumption number expected" i))))
	   ((and (string? x) (assoc x THEOREMS))
	    (let* ((aconst (theorem-name-to-aconst x))
		   (formula (aconst-to-formula aconst)))
	      (list formula (make-proof-in-aconst-form aconst))))
	   ((and (string? x) (assoc x GLOBAL-ASSUMPTIONS))
	    (let* ((aconst (global-assumption-name-to-aconst x))
		   (formula (aconst-to-formula aconst)))
	      (list formula (make-proof-in-aconst-form aconst))))
	   ((proof-form? x) (list (proof-to-formula x) x))
	   ((formula-form? x) ;then a new goal is created
	    (list x DEFAULT-GOAL-NAME))
	   (else (myerror "ex-elim" "illegal argument" x))))
         (ex-formula (car ex-formula-and-x1))
         (x1 (cadr ex-formula-and-x1))
         (free1 (if (ex-form? ex-formula)
                    (formula-to-free ex-formula)
                    (myerror "ex-elim" "ex formula expected" ex-formula)))
         (free2 (formula-to-free goal-formula))
         (free (union free1 free2)))
    (apply use-with-intern
	   num-goals proof maxgoal
	   (make-proof-in-aconst-form
	    (ex-formula-and-concl-to-ex-elim-aconst
	     ex-formula goal-formula))
	   (append (map make-term-in-var-form free)
		   (list x1 DEFAULT-GOAL-NAME)))))

;; Assume we prove a goal from an existential formula ex x A, exd x A,
;; exr x A, exl x A, exnc x A or exc x1,..,xn(A1!..!Am).  The
;; natural way to use this hypothesis is to say "by exhyp assume we
;; have an x satisfying A" or "by exhyp assume we have x1,..,xn
;; satisfying A1...,Am".  Correspondingly we provide

(define (by-assume exhyp . varnames-and-hyps)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (apply by-assume-intern
			      num-goals proof maxgoal exhyp varnames-and-hyps))
    (pproof-state-history-push PPROOF-STATE)
    (display-comment "ok, we now have the new goal ")
    (if COMMENT-FLAG (newline))
    (display-num-goal (car (pproof-state-to-num-goals)))))

(define (by-assume-intern
	 num-goals proof maxgoal exhyp . varnames-and-hyps)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (l (length avars))
	 (ex-fla-and-x1
	  (cond
	   ((and (integer? exhyp) (positive? exhyp))
	    (if (<= exhyp l)
		(let* ((avar (list-ref avars (- exhyp 1)))
		       (formula (avar-to-formula avar)))
		  (list formula (make-proof-in-avar-form avar)))
		(myerror "by-assume" "assumption number expected" exhyp)))
	   ((and (string? exhyp)
		 (member exhyp (hypname-info-to-names hypname-info)))
	    (let ((i (name-and-hypname-info-to-index exhyp hypname-info)))
	      (if (<= i l)
		  (let* ((avar (list-ref avars (- i 1)))
			 (formula (avar-to-formula avar)))
		    (list formula (make-proof-in-avar-form avar)))
		  (myerror "by-assume" "assumption number expected" i))))
	   ((and (string? exhyp) (assoc exhyp THEOREMS))
	    (let* ((aconst (theorem-name-to-aconst exhyp))
		   (formula (aconst-to-formula aconst)))
	      (list formula (make-proof-in-aconst-form aconst))))
	   ((and (string? exhyp) (assoc exhyp GLOBAL-ASSUMPTIONS))
	    (let* ((aconst (global-assumption-name-to-aconst exhyp))
		   (formula (aconst-to-formula aconst)))
	      (list formula (make-proof-in-aconst-form aconst))))
	   ((proof-form? exhyp) (list (proof-to-formula exhyp) exhyp))
	   ((formula-form? exhyp) ;then a new goal is created
	    (list exhyp DEFAULT-GOAL-NAME))
	   (else (myerror "by-assume" "illegal argument" exhyp))))
	 (ex-fla (fold-formula (car ex-fla-and-x1)))
	 (x1 (cadr ex-fla-and-x1))
	 (n-and-m (cond ((or (ex-form? ex-fla)
			     (exd-form? ex-fla) (exdt-form? ex-fla)
			     (exr-form? ex-fla) (exrt-form? ex-fla)
			     (exl-form? ex-fla) (exlt-form? ex-fla)
			     (exnc-form? ex-fla) (exnct-form? ex-fla))
			 (list 1 1))
			((excl-form? ex-fla)
			 (list (length (excl-form-to-vars ex-fla))
			       (length (tensor-form-to-parts
					(excl-form-to-kernel ex-fla)))))
			((exca-form? ex-fla)
			 (list (length (exca-form-to-vars ex-fla))
			       (length (tensor-form-to-parts
					(exca-form-to-kernel ex-fla)))))
			(else (myerror "ex-form expected" ex-fla))))
	 (n (car n-and-m))
	 (m (cadr n-and-m))
	 (varnames
	  (if (= (+ n m) (length varnames-and-hyps))
	      (list-head varnames-and-hyps n)
	      (myerror (+ n m) "arguments expected in addition to exhyp")))
	 (vars (map pv varnames))
	 (hyps (list-tail varnames-and-hyps n)))
    (if (not (apply and-op (map (lambda (x) (and (string? x) (var? (pv x))))
				varnames)))
	(myerror "variable names expected" varnames))
    (if (not (apply and-op (map (lambda (hyp)
				  (or (string? hyp) (integer? hyp)))
				hyps)))
	(myerror "names or numbers for hypotheses expected" hyps))
    (let ((pproof-state1
	   (cond ((ex-form? ex-fla)
		  (ex-elim-intern num-goals proof maxgoal exhyp))
		 ((or (exd-form? ex-fla) (exdt-form? ex-fla)
		      (exr-form? ex-fla) (exrt-form? ex-fla)
		      (exl-form? ex-fla) (exlt-form? ex-fla)
		      (exnc-form? ex-fla) (exnct-form? ex-fla))
		  (exi-elim-intern num-goals proof maxgoal exhyp))
		 ((or (excl-form? ex-fla) (exca-form? ex-fla))
		  (exc-elim-intern num-goals proof maxgoal exhyp))
		 (else (myerror "existential formula expected" ex-fla)))))
      (cond
       ((or ;hypothesis
	 (and (integer? exhyp) (positive? exhyp))
	 (and (string? exhyp)
	      (member exhyp (hypname-info-to-names hypname-info))))
	(let ((pproof-state2
	       (apply assume-intern (append pproof-state1 varnames hyps))))
	  (apply drop-intern (append pproof-state2 (list exhyp)))))
       ((or ;theorem/global assumption/proof
	 (and (string? exhyp) (assoc exhyp THEOREMS))
	 (and (string? exhyp) (assoc exhyp GLOBAL-ASSUMPTIONS))
	 (proof-form? exhyp))
	(apply assume-intern (append pproof-state1 varnames hyps)))
       ((formula-form? exhyp) ;then a new goal is created
	(let ((pproof-state2
	       (apply get-intern
		      (append pproof-state1
			      (list (pproof-state-to-maxgoal
				     pproof-state1))))))
	  (apply assume-intern (append pproof-state2 varnames hyps))))
       (else (myerror "by-assume-intern" "unexpected exhyp" exhyp))))))

(define (exi-elim-intern num-goals proof maxgoal x)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (l (length avars))
	 (goal-formula (goal-to-formula goal))
	 (exi-formula-and-x1
	  (cond
	   ((and (integer? x) (positive? x))
	    (if (<= x l)
		(let* ((avar (list-ref avars (- x 1)))
		       (formula (avar-to-formula avar)))
		  (list formula (make-proof-in-avar-form avar)))
		(myerror "exi-elim-intern" "assumption number expected" x)))
	   ((and (string? x)
		 (member x (hypname-info-to-names hypname-info)))
	    (let ((i (name-and-hypname-info-to-index x hypname-info)))
	      (if (<= i l)
		  (let* ((avar (list-ref avars (- i 1)))
			 (formula (avar-to-formula avar)))
		    (list formula (make-proof-in-avar-form avar)))
		  (myerror
		   "exi-elim-intern" "assumption number expected" i))))
	   ((and (string? x) (assoc x THEOREMS))
	    (let* ((aconst (theorem-name-to-aconst x))
		   (formula (aconst-to-formula aconst)))
	      (list formula (make-proof-in-aconst-form aconst))))
	   ((and (string? x) (assoc x GLOBAL-ASSUMPTIONS))
	    (let* ((aconst (global-assumption-name-to-aconst x))
		   (formula (aconst-to-formula aconst)))
	      (list formula (make-proof-in-aconst-form aconst))))
	   ((proof-form? x) (list (proof-to-formula x) x))
	   ((formula-form? x) ;then a new goal is created
	    (list x DEFAULT-GOAL-NAME))
	   (else (myerror "exi-elim-intern" "illegal argument" x))))
         (exi-formula (car exi-formula-and-x1))
         (x1 (cadr exi-formula-and-x1))
         (free1 (formula-to-free exi-formula))
         (free2 (formula-to-free goal-formula))
         (free (union free1 free2)))
    (apply use-with-intern
	   num-goals proof maxgoal
	   (make-proof-in-aconst-form
	    (imp-formulas-to-elim-aconst
	     (make-imp exi-formula goal-formula)))
	   (append (map make-term-in-var-form free)
		   (list x1 DEFAULT-GOAL-NAME)))))

;; For backward compatibility:

(define by-assume-with-intern by-assume-intern) ;obsolete
(define by-assume-with by-assume) ;obsolete

;; (cases) expects a goal formula all x A with x of alg type and total.
;; Let c1 ... cn be the constructors of the algebra.  Then n new goals
;; all xs_i A[c_i xs_i] are generated.  (cases t) expects a goal A(t)
;; with t a total term.  If t is a boolean term, the goal A is replaced
;; by new goals (atom t) -> A(True) and ((atom t) -> F) -> A(False).
;; If t is a total non-boolean term, cases is called with the
;; all-formula all x(x=t -> A(x)).

;; (cases 'auto) expects an atomic goal and checks whether its boolean
;; kernel contains an if-term whose test is neither an if-term nor
;; contains bound variables.  With the first such test (cases test) is
;; called.

(define (cases . x)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (apply cases-intern num-goals proof maxgoal x))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (cases-intern num-goals proof maxgoal . x)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (formula (goal-to-formula goal)))
    (cond
     ((and (pair? x)
	   (term-form? (car x))
	   (equal? (make-alg "boole") (term-to-type (car x))))
      (casedist-intern num-goals proof maxgoal (car x)))
     ((and (pair? x) (eq? 'auto (car x)))
      (let ((boolean-kernel (if (atom-form? formula)
				(atom-form-to-kernel formula)
				(myerror "cases" "atomic goal expected"
					 formula))))
	(cases-intern num-goals proof maxgoal
		      (first-if-term-in boolean-kernel))))
     (else
      (let* ((all-formula
	      (if
	       (null? x)
	       (cond
		((all-form? formula)
		 (let* ((var (all-form-to-var formula))
			(t-deg (var-to-t-deg var)))
		   (if (t-deg-one? t-deg)
		       formula
		       (myerror "cases" "total variable expected" formula))))
		((and (allnc-form? formula) (formula-of-nulltype? formula))
		 (let* ((var (allnc-form-to-var formula))
			(kernel (allnc-form-to-kernel formula))
			(t-deg (var-to-t-deg var))
			(newvar (if (t-deg-one? t-deg)
				    (var-and-t-deg-to-new-var var t-deg)
				    (myerror "cases" "total variable expected"
					     formula)))
			(varterm (make-term-in-var-form newvar))
			(subst-kernel (formula-subst kernel var varterm)))
		   (make-all newvar subst-kernel)))
		(else (myerror "cases"
			       "allnc form with n.c. goal or all form expected"
			       formula)))
	       (let* ((term (car x))
		      (type (if (term-form? term)
				(term-to-type term)
				(myerror "cases" "term expected" term)))
		      (t-deg (term-to-t-deg term))
		      (var (if (t-deg-one? t-deg)
			       (type-to-new-var type)
			       (myerror "cases" "total term expected" term)))
		      (varterm (make-term-in-var-form var))
		      (substformula (formula-gen-subst formula term varterm))
		      (kernel-formula (make-imp (if (finalg? type)
						    (make-= term varterm)
						    (make-eqd term varterm))
						substformula)))
		 (make-all var kernel-formula))))
	     (aconst (all-formula-to-cases-aconst all-formula))
             (var (all-form-to-var all-formula))
             (kernel (all-form-to-kernel all-formula))
             (newvar (if (t-deg-one? (var-to-t-deg var))
			 (var-to-new-var var)
			 (myerror "cases" "total variable expected" var)))
	     (type (var-to-type var))
	     (alg-name (if (alg-form? type)
			   (alg-form-to-name type)
			   (myerror "cases" "variable of algebra type expected"
				    var)))
	     (k (length (alg-name-to-typed-constr-names alg-name)))
             (pproof (if (null? x)
			 (pproof-all-intro
			  (make-pproof-state num-goals proof maxgoal)
			  newvar)
			 (make-pproof-state num-goals proof maxgoal))))
        (apply
         use-with-intern
         (append
          pproof
          (list (make-proof-in-aconst-form aconst))
          (map make-term-in-var-form (formula-to-free all-formula))
          (if (null? x)
              (list (make-term-in-var-form newvar))
              x)
          (vector->list (make-vector k DEFAULT-GOAL-NAME))
          (if (pair? x)
              (list (if (finalg? type)
			(make-proof-in-aconst-form truth-aconst)
			(let* ((idpc (make-idpredconst "EqD" (list type) '()))
			       (initeqd-aconst ;all a a eqd a
				(number-and-idpredconst-to-intro-aconst
				 0 idpc)))
			  (mk-proof-in-elim-form
			   (make-proof-in-aconst-form initeqd-aconst)
			   (car x)))))
	      '()))))))))

;; (casedist test) replaces the goal A(test) by two new goals
;;   (atom test) -> A(True)
;;   ((atom test) -> F) -> A(False)

(define (casedist test)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (casedist-intern num-goals proof maxgoal test))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (casedist-intern num-goals proof maxgoal test)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (formula (goal-to-formula goal))
	 (vars (context-to-vars context))
	 (info (if (term-form? test)
		   (set-minus (term-to-free test) vars)
		   (myerror "casedist" "term expected" test))))
    (if (pair? info)
	(myerror "casedist" "test has free variables not in context"
		 (map var-to-string info)))
    (if (not (equal? (make-alg "boole") (term-to-type test)))
	(myerror "casedist" "boolean term extected" test))
    (if (not (synt-total? test))
	(myerror "casedist" "total term expected" test))
    (let* ((var (type-to-new-partial-var (make-alg "boole")))
	   (varterm (make-term-in-var-form var))
	   (kernel-formula (formula-gen-subst formula test varterm))
	   (cterm (make-cterm var kernel-formula))
	   (pvar (predicate-form-to-predicate
		  (imp-form-to-final-conclusion
		   (all-form-to-kernel (proof-to-formula dec-cases-proof)))))
	   (subst-dec-cases-proof
	     ;of all p((p -> A(True)) -> (~p -> A(False)) -> A(p))
	    (proof-subst dec-cases-proof pvar cterm)))
      (use-with-intern num-goals proof maxgoal
		       subst-dec-cases-proof test
		       DEFAULT-GOAL-NAME DEFAULT-GOAL-NAME))))

(define (term-to-if-tests term)
  (case (tag term)
    ((term-in-var-form term-in-const-form) '())
    ((term-in-abst-form)
     (let* ((var (term-in-abst-form-to-var term))
	    (kernel (term-in-abst-form-to-kernel term))
	    (if-tests (term-to-if-tests kernel)))
       (list-transform-positive if-tests
	 (lambda (x) (not (member var (term-to-free x)))))))
    ((term-in-app-form)
     (let ((if-tests1
	    (term-to-if-tests (term-in-app-form-to-op term)))
	   (if-tests2
	    (term-to-if-tests (term-in-app-form-to-arg term))))
       (union-wrt term=? if-tests1 if-tests2)))
    ((term-in-pair-form)
     (union-wrt term=?
		(term-to-if-tests (term-in-pair-form-to-left term))
		(term-to-if-tests (term-in-pair-form-to-right term))))
    ((term-in-lcomp-form)
     (term-to-if-tests (term-in-lcomp-form-to-kernel term)))
    ((term-in-rcomp-form)
     (term-to-if-tests (term-in-rcomp-form-to-kernel term)))
    ((term-in-if-form)
     (let* ((test (term-in-if-form-to-test term))
	    (alts (term-in-if-form-to-alts term))
	    (type (term-to-type test)))
       (if
	(and (equal? (make-alg "boole") type)
	     (not (term-in-if-form? test)))
	(apply union-wrt
	       term=? (list test) (map term-to-if-tests alts))
	(apply union-wrt
	       (list term=?)
	       (map term-to-if-tests (cons test alts))))))
    (else (myerror "term-to-if-tests" "term expected" term))))

(define (first-if-term-in term)
  (let ((tests (term-to-if-tests term)))
    (if (pair? tests)
	(car tests)
	(myerror "first-if-term-in" "no if-term found"))))

;; In the following definition of (simp opt-dir-or-x . x-and-xs-or-xs),
;; opt-dir is either the string "<-" or missing.  x is one of the following.
;; - A number or string identifying a hypothesis form the context.
;; - The name of a theorem or global assumption, but not one whose final
;;   conclusion is a predicate variable.
;; - A closed proof.
;; - A formula with free variables from the context, generating a new goal.
;; xs is a list consisting of symbols left or right, giving
;; directions in case the used formula contains conjunctions, and of
;; terms.  The universal quantifiers of the used formula are
;; instantiated with appropriate terms to match a part of the goal.
;; The terms provided are substituted for those variables that
;; cannot be inferred.  For the instantiated premises new goals are
;; created.  This generates a used formula, which is to be an atom,
;; a negated atom or (lhs eqd rhs).  If it as a (negated) atom,
;; check whether the kernel or its normal form is present in the
;; goal.  If so, replace it by True (False).  If it is (lhs = rhs)
;; or (lhs eqd rhs) with lhs or its normal form present in the goal,
;; replace lhs by rhs.  In case "<-" exchange lhs by rhs.

;; simp-with is a more verbose form of simp, where the terms are not
;; inferred via matching, but have to be given explicitly.  In fact,
;; simp is defined via simp-with.  In (simp-with opt-dir-or-x
;; . x-and-xs-or-xs), opt-dir and x are as in simp, except that the
;; formula of x must be an atom, a negated atom or (lhs eqd rhs).
;; xs is a list consisting of
;; - a number or string identifying a hypothesis form the context,
;; - the name of a theorem or global assumption,
;; - a closed proof,
;; - the string "?" (value of DEFAULT-GOAL-NAME), generating a new goal,
;; - a symbol left or right,
;; - a term, whose free variables are added to the context,
;; - a type, which is substituted for the 1st tvar,
;; - a comprehension term, which is substituted for the 1st pvar.

(define (simp-with opt-dir-or-x . x-and-xs-or-xs)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply simp-with-intern
		 num-goals proof maxgoal opt-dir-or-x x-and-xs-or-xs))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (simp-with-intern num-goals proof maxgoal . rest)
  (let* ((opt-dir-or-x
	  (if (null? rest)
	      (myerror "simp-with-intern" "more arguments expected")
	      (car rest)))
	 (left-to-right
	  (not (and (string? opt-dir-or-x) (string=? "<-" opt-dir-or-x))))
	 (x-and-x-list (if left-to-right
			   rest
			   (cdr rest)))
	 (x (if (null? x-and-x-list)
		(myerror "simp-with-intern" "more arguments expected")
		(car x-and-x-list)))
	 (x-list (cdr x-and-x-list))
	 (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (proof-and-new-num-goals-and-maxgoal
	  (if (and (string? x)
		   (let ((info (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS))))
		     (and info
			  (let* ((aconst (cadr info))
				 (aconst-formula (aconst-to-formula aconst))
				 (final-concl
				  (imp-impnc-all-allnc-form-to-final-conclusion
				   aconst-formula)))
			    (and (predicate-form? final-concl)
				 (pvar? (predicate-form-to-predicate
					 final-concl)))))))
	      (myerror "simp-with-intern" "unexpected aconst name" x)
	      (apply x-and-x-list-to-proof-and-new-num-goals-and-maxgoal
		     num-goal (+ 1 maxgoal) x x-list)))
	 (negatom-or-eq-proof (car proof-and-new-num-goals-and-maxgoal))
	 (new-num-goals (cadr proof-and-new-num-goals-and-maxgoal))
	 (new-maxgoal (caddr proof-and-new-num-goals-and-maxgoal))
	 (goal-formula (goal-to-formula goal))
	 (used-formula (proof-to-formula negatom-or-eq-proof))
	 (used-prime-formula
	  (cond ((prime-form? used-formula) used-formula)
		((and (imp-impnc-form? used-formula)
		      (atom-form? (imp-impnc-form-to-premise used-formula))
		      (classical-formula=?
		       falsity (imp-impnc-form-to-conclusion used-formula)))
		 (imp-impnc-form-to-premise used-formula))
		(else (myerror "simp-with-intern"
			       "negated atom or prime formula expected"
			       used-formula))))
	 (used-nprime-formula (normalize-formula used-prime-formula))
	 (bvar (type-to-new-var (make-alg "boole")))
	 (bvarterm (make-term-in-var-form bvar))
	 (used-kernel (if (atom-form? used-prime-formula)
			  (atom-form-to-kernel used-prime-formula)
			  bvarterm)) ;anything would do
	 (used-nkernel (nt used-kernel))
	 (op (term-in-app-form-to-final-op used-kernel))
	 (nop (term-in-app-form-to-final-op used-nkernel))
	 (goal-formula-without-kernel
	  (if (atom-form? used-prime-formula)
	      (formula-gen-subst goal-formula used-kernel bvarterm)
	      goal-formula))
	 (ngoal-formula (nf goal-formula))
	 (ngoal-formula-without-nkernel
	  (if (atom-form? used-prime-formula)
	      (formula-gen-subst ngoal-formula used-nkernel bvarterm)
	      ngoal-formula))
	 (kernel-present? (not (formula=?
				goal-formula-without-kernel
				goal-formula)))
	 (nkernel-present? (not (formula=?
				 ngoal-formula-without-nkernel
				 ngoal-formula))))
    (cond
     ((and kernel-present?
	   (not (term=? used-kernel (make-term-in-const-form true-const)))
	   (not (term=? used-kernel (make-term-in-const-form false-const)))
	   (or (atom-form? used-formula) (synt-total? used-kernel)))
      (simp-with-kernel-aux num-goals proof maxgoal
			    negatom-or-eq-proof new-num-goals new-maxgoal
			    used-kernel bvar goal-formula-without-kernel))
     ((and (prime-form? used-formula)
	   (term-in-const-form? op)
	   (string=? "=" (const-to-name (term-in-const-form-to-const op)))
	   (let* ((args (term-in-app-form-to-args used-kernel))
		  (lhs (car args))
		  (rhs (cadr args))
		  (type (term-to-type lhs))
		  (var (type-to-new-var type))
		  (varterm (make-term-in-var-form var))
		  (simp-formula
		   (if left-to-right
		       (formula-gen-subst goal-formula lhs varterm)
		       (formula-gen-subst goal-formula rhs varterm))))
	     (not (formula=? simp-formula goal-formula))))
      (let* ((args (term-in-app-form-to-args used-kernel))
	     (lhs (car args))
	     (rhs (cadr args))
	     (type (term-to-type lhs))
	     (var (type-to-new-var type))
	     (varterm (make-term-in-var-form var))
	     (simp-formula
	      (if left-to-right
		  (formula-gen-subst goal-formula lhs varterm)
		  (formula-gen-subst goal-formula rhs varterm)))
	     (all-formula (mk-all var simp-formula))
	     (new-goal ;A(rhs) or A(lhs)
	      (context-and-ncvars-and-formula-to-new-goal
	       context ncvars
	       (formula-subst simp-formula var
			      (if left-to-right rhs lhs))))
	     (new-num-goal
	      (make-num-goal
	       (+ 1 maxgoal) new-goal drop-info hypname-info ignore-deco-flag))
	     (new-proof ;of A(lhs) or A(rhs)
	      (mk-proof-in-elim-form
	       (if
		left-to-right
		(compat-rev-at all-formula) ;allnc n,m(n=m -> A(m) -> A(n))
		(compat-at all-formula))    ;allnc n,m(n=m -> A(n) -> A(m))
	       lhs rhs negatom-or-eq-proof new-goal)))
	(make-pproof-state
	 (append (list new-num-goal) new-num-goals (cdr num-goals))
	 (goal-subst proof goal new-proof)
	 new-maxgoal)))
     ((and (predicate-form? used-prime-formula)
	   (let ((predicate (predicate-form-to-predicate used-prime-formula)))
	     (and (idpredconst-form? predicate)
		  (string=? "EqD" (idpredconst-to-name predicate))
		  (let* ((args (predicate-form-to-args used-prime-formula))
			 (lhs (car args))
			 (rhs (cadr args))
			 (type (term-to-type lhs))
			 (var (type-to-new-var type))
			 (varterm (make-term-in-var-form var))
			 (simp-formula
			  (if left-to-right
			      (formula-gen-subst goal-formula lhs varterm)
			      (formula-gen-subst goal-formula rhs varterm))))
		    (not (formula=? simp-formula goal-formula))))))
      (let* ((args (predicate-form-to-args used-prime-formula))
	     (lhs (car args))
	     (rhs (cadr args))
	     (type (term-to-type lhs))
	     (var (type-to-new-var type))
	     (varterm (make-term-in-var-form var))
	     (simp-formula
	      (if left-to-right
		  (formula-gen-subst goal-formula lhs varterm)
		  (formula-gen-subst goal-formula rhs varterm)))
	     (all-formula (mk-all var simp-formula))
	     (new-goal ;A(rhs) or A(lhs)
	      (context-and-ncvars-and-formula-to-new-goal
	       context ncvars
	       (formula-subst simp-formula var
			      (if left-to-right rhs lhs))))
	     (new-num-goal
	      (make-num-goal
	       (+ 1 maxgoal) new-goal drop-info hypname-info ignore-deco-flag))
	     (new-proof ;of A(lhs) or A(rhs)
	      (mk-proof-in-elim-form
	       (if
		left-to-right
		(eqd-compat-rev-at all-formula) ;allnc n,m(n=m -> A(m) -> A(n))
		(eqd-compat-at all-formula))    ;allnc n,m(n=m -> A(n) -> A(m))
	       lhs rhs negatom-or-eq-proof new-goal)))
	(make-pproof-state
	 (append (list new-num-goal) new-num-goals (cdr num-goals))
	 (goal-subst proof goal new-proof)
	 new-maxgoal)))
     ((and nkernel-present?
	   (not (term=? used-nkernel (make-term-in-const-form true-const)))
	   (not (term=? used-nkernel (make-term-in-const-form false-const)))
	   (or (atom-form? used-formula) (synt-total? used-nkernel)))
      (simp-with-kernel-aux num-goals proof maxgoal
			    negatom-or-eq-proof new-num-goals new-maxgoal
			    used-nkernel bvar ngoal-formula-without-nkernel))
     ((and (prime-form? used-formula)
	   (term-in-const-form? nop)
	   (string=? "=" (const-to-name (term-in-const-form-to-const nop)))
	   (let* ((args (term-in-app-form-to-args used-nkernel))
		  (lhs (car args))
		  (rhs (cadr args))
		  (type (term-to-type lhs))
		  (var (type-to-new-var type))
		  (varterm (make-term-in-var-form var))
		  (simp-formula
		   (if left-to-right
		       (formula-gen-subst goal-formula lhs varterm)
		       (formula-gen-subst goal-formula rhs varterm))))
	     (not (formula=? simp-formula goal-formula))))
      (let* ((args (term-in-app-form-to-args used-nkernel))
	     (lhs (car args))
	     (rhs (cadr args))
	     (type (term-to-type lhs))
	     (var (type-to-new-var type))
	     (varterm (make-term-in-var-form var))
	     (simp-formula
	      (if left-to-right
		  (formula-gen-subst goal-formula lhs varterm)
		  (formula-gen-subst goal-formula rhs varterm)))
	     (all-formula (mk-all var simp-formula))
	     (new-goal ;A(rhs) or A(lhs)
	      (context-and-ncvars-and-formula-to-new-goal
	       context ncvars
	       (formula-subst simp-formula var
			      (if left-to-right rhs lhs))))
	     (new-num-goal
	      (make-num-goal
	       (+ 1 maxgoal) new-goal drop-info hypname-info ignore-deco-flag))
	     (new-proof ;of A(lhs) or A(rhs)
	      (mk-proof-in-elim-form
	       (if
		left-to-right
		(compat-rev-at all-formula) ;allnc n,m(n=m -> A(m) -> A(n))
		(compat-at all-formula))    ;allnc n,m(n=m -> A(n) -> A(m))
	       lhs rhs negatom-or-eq-proof new-goal)))
	(make-pproof-state
	 (append (list new-num-goal) new-num-goals (cdr num-goals))
	 (goal-subst proof goal new-proof)
	 new-maxgoal)))
     ((and (predicate-form? used-nprime-formula)
	   (let ((predicate (predicate-form-to-predicate used-nprime-formula)))
	     (and (idpredconst-form? predicate)
		  (string=? "EqD" (idpredconst-to-name predicate))
		  (let* ((args (predicate-form-to-args used-nprime-formula))
			 (lhs (car args))
			 (rhs (cadr args))
			 (type (term-to-type lhs))
			 (var (type-to-new-var type))
			 (varterm (make-term-in-var-form var))
			 (simp-formula
			  (if left-to-right
			      (formula-gen-subst goal-formula lhs varterm)
			      (formula-gen-subst goal-formula rhs varterm))))
		    (not (formula=? simp-formula goal-formula))))))
      (let* ((args (predicate-form-to-args used-nprime-formula))
	     (lhs (car args))
	     (rhs (cadr args))
	     (type (term-to-type lhs))
	     (var (type-to-new-var type))
	     (varterm (make-term-in-var-form var))
	     (simp-formula
	      (if left-to-right
		  (formula-gen-subst goal-formula lhs varterm)
		  (formula-gen-subst goal-formula rhs varterm)))
	     (all-formula (mk-all var simp-formula))
	     (new-goal ;A(rhs) or A(lhs)
	      (context-and-ncvars-and-formula-to-new-goal
	       context ncvars
	       (formula-subst simp-formula var
			      (if left-to-right rhs lhs))))
	     (new-num-goal
	      (make-num-goal
	       (+ 1 maxgoal) new-goal drop-info hypname-info ignore-deco-flag))
	     (new-proof ;of A(lhs) or A(rhs)
	      (mk-proof-in-elim-form
	       (if
		left-to-right
		(eqd-compat-rev-at all-formula) ;allnc n,m(n=m -> A(m) -> A(n))
		(eqd-compat-at all-formula))    ;allnc n,m(n=m -> A(n) -> A(m))
	       lhs rhs negatom-or-eq-proof new-goal)))
	(make-pproof-state
	 (append (list new-num-goal) new-num-goals (cdr num-goals))
	 (goal-subst proof goal new-proof)
	 new-maxgoal)))
     (else (myerror "simp-with-intern" "goal cannot be simplified with"
		    used-formula)))))

(define (simp-with-kernel-aux num-goals proof maxgoal
			      negatom-or-eq-proof new-num-goals new-maxgoal
			      used-kernel bvar goal-formula-without-kernel)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (used-formula (proof-to-formula negatom-or-eq-proof))
	 (all-formula (mk-all bvar goal-formula-without-kernel)))
    (if
     (atom-form? used-formula)
     (let* ((new-goal ;A(True)
	     (context-and-ncvars-and-formula-to-new-goal
	      context ncvars
	      (formula-subst goal-formula-without-kernel bvar
			     (make-term-in-const-form true-const))))
	    (new-num-goal
	     (make-num-goal
	      (+ 1 maxgoal) new-goal drop-info hypname-info ignore-deco-flag))
	    (new-proof ;of A(r)
	     (mk-proof-in-elim-form
	      (compat-rev-at all-formula) ;allnc p^,q^(p^=q^ -> A(q^) -> A(p^))
	      used-kernel ;r
	      (make-term-in-const-form true-const)
	      (mk-proof-in-elim-form ;of r=True
	       (make-proof-in-aconst-form ;of all p(atom(p) -> p=True)
		atom-true-aconst)
	       used-kernel ;r
	       negatom-or-eq-proof) ;of atom(r)
	      new-goal))) ;A(True)
       (make-pproof-state
	(append (list new-num-goal) new-num-goals (cdr num-goals))
	(goal-subst proof goal new-proof)
	new-maxgoal))
     (let* ((info (assoc "AtomFalse" THEOREMS))
	    (atomfalse-aconst
	     (if info (cadr info)
		 (myerror "simp-with-intern" "AtomFalse missing:"
			  "all boole((boole -> F) -> boole=False)")))
	    (new-goal ;A(False)
	     (context-and-ncvars-and-formula-to-new-goal
	      context ncvars
	      (formula-subst goal-formula-without-kernel bvar
			     (make-term-in-const-form false-const))))
	    (new-num-goal
	     (make-num-goal
	      (+ 1 maxgoal) new-goal drop-info hypname-info ignore-deco-flag))
	    (new-proof ;of A(r)
	     (mk-proof-in-elim-form
	      (compat-rev-at all-formula) ;allnc p,q(p=q -> A(q) -> A(p))
	      used-kernel ;r
	      (make-term-in-const-form false-const)
	      (mk-proof-in-elim-form ;of r=False
	       (make-proof-in-aconst-form ;of all p(~p -> p=False)
		atomfalse-aconst)
	       used-kernel ;r
	       negatom-or-eq-proof) ;of ~r
	      new-goal))) ;A(False)
       (make-pproof-state
	(append
	 (list new-num-goal) new-num-goals (cdr num-goals))
	(goal-subst proof goal new-proof)
	new-maxgoal)))))

(define (simp opt-dir-or-x . x-and-xs-or-xs)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing"))))
	 (simp-result
	  (apply simp-intern
		 num-goals proof maxgoal opt-dir-or-x x-and-xs-or-xs)))
    (if (not simp-result)
	(begin (display-comment "no simplification possible")
	       (if COMMENT-FLAG (newline)))
	(begin
	  (set! PPROOF-STATE simp-result)
	  (pproof-state-history-push PPROOF-STATE)
	  (display-new-goals num-goals number)))))

(define (simp-intern num-goals proof
		     maxgoal . opt-dir-and-x-and-elab-path-and-terms)
  (let* ((opt-dir (if (null? opt-dir-and-x-and-elab-path-and-terms)
		      (myerror "simp-intern" "more arguments expected")
		      (car opt-dir-and-x-and-elab-path-and-terms)))
	 (left-to-right (not (and (string? opt-dir) (string=? "<-" opt-dir))))
	 (x-and-elab-path-and-terms
	  (if left-to-right
	      opt-dir-and-x-and-elab-path-and-terms
	      (cdr opt-dir-and-x-and-elab-path-and-terms)))
	 (x (if (null? x-and-elab-path-and-terms)
		(myerror "simp-intern" "more arguments expected")
		(car x-and-elab-path-and-terms)))
	 (elab-path-and-terms (cdr x-and-elab-path-and-terms))
	 (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (avars (context-to-avars context))
	 (maxhyp (length avars))
	 (goal-formula (goal-to-formula goal))
	 (leaf (if (formula-form? x)
		   (context-and-ncvars-and-formula-to-new-goal
		    context ncvars x)
		   (hyp-info-to-leaf num-goal x)))
	 (used-formula
	  (unfold-formula (if (formula-form? x) x (proof-to-formula leaf))))
	 (sig-vars (context-to-vars context))
	 (sig-tvars-and-sig-vars
	  (if (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS))
	      sig-vars
	      (append (formula-to-tvars used-formula) sig-vars)))
	 (elab-path (do ((l elab-path-and-terms (cdr l))
			 (res '() (if (memq (car l) '(left right))
				      (cons (car l) res)
				      res)))
			((null? l) (reverse res))))
	 (xs-and-vars-and-toinst1
	  (apply
	   fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
	   used-formula sig-tvars-and-sig-vars
	   goal-formula left-to-right
	   elab-path))
	 (xs-and-vars-and-toinst
	  (if xs-and-vars-and-toinst1
	      xs-and-vars-and-toinst1
	      (apply
	       fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
	       (normalize-formula used-formula)
	       sig-tvars-and-sig-vars
	       (normalize-formula goal-formula)
	       left-to-right
	       elab-path))))
    (if
     (not xs-and-vars-and-toinst)
     #f
     (let* ((xs (car xs-and-vars-and-toinst))
	    (vars (cadr xs-and-vars-and-toinst))
	    (toinst (caddr xs-and-vars-and-toinst))
	    (terms (do ((l elab-path-and-terms (cdr l))
			(res '() (if (memq (car l) '(left right))
				     res
				     (cons (car l) res))))
		       ((null? l) (reverse res))))
	    (subst (if (<= (length vars) (length terms))
		       (map list vars (list-head terms (length vars)))
		       empty-subst))
	    (subst-xs (map (lambda (x) (if (term-form? x)
					   (term-substitute x subst)
					   x))
			   xs))
	    (types (let ((info1 (assoc x THEOREMS))
			 (info2 (assoc x GLOBAL-ASSUMPTIONS))
			 (tsubst (list-transform-positive toinst
				   (lambda (x) (tvar-form? (car x))))))
		     (if
		      (and (or info1 info2) (pair? tsubst)) ;else '()
		      (let* ((aconst (if info1
					 (theorem-name-to-aconst x)
					 (global-assumption-name-to-aconst x)))
			     (fla (aconst-to-formula aconst))
			     (tvars (formula-to-tvars fla)))
			(map (lambda (tvar) (type-substitute tvar tsubst))
			     tvars))
		      '()))))
       (if (> (length vars) (length terms))
	   (apply myerror
		  "simp" "more terms expected, to be substituted for"
		  (list-tail vars (length terms))))
       (if (and COMMENT-FLAG (< (length vars) (length terms)))
	   (begin
	     (comment "warning: superfluous terms")
	     (for-each comment
		       (map term-to-string (list-tail terms (length vars))))))
       (apply simp-with-intern
	      (if left-to-right
		  (append (list num-goals proof maxgoal x)
			  (append types subst-xs))
		  (append (list num-goals proof maxgoal "<-" x)
			  (append types subst-xs))))))))

;; In the following definition of simprat-with x is one of the following.
;; - A number or string identifying a hypothesis form the context.
;; - The name of a theorem or global assumption, but not one whose final
;;   conclusion is a predicate variable.
;; - A closed proof.
;; - A formula with free variables from the context, generating a new goal.
;; Moreover xs is a list consisting of
;; - a number or string identifying a hypothesis form the context,
;; - the name of a theorem or global assumption,
;; - a closed proof,
;; - the string "?" (value of DEFAULT-GOAL-NAME), generating a new goal,
;; - a symbol left or right,
;; - a term, whose free variables are added to the context,
;; - a type, which is substituted for the 1st tvar,
;; - a comprehension term, which is substituted for the 1st pvar.
;; This generates a used formula lhs==rhs with lhs or its normal form present
;; in the goal.  Replace lhs by rhs.  In case "<-" exchange lhs by rhs.

(define (simprat-with opt-dir-or-x . x-and-xs-or-xs)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply simprat-with-intern
		 num-goals proof maxgoal opt-dir-or-x x-and-xs-or-xs))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (simprat-with-intern num-goals proof maxgoal . rest)
  (let* ((opt-dir-or-x
	  (if (null? rest)
	      (myerror "simprat-with-intern" "more arguments expected")
	      (car rest)))
	 (left-to-right
	  (not (and (string? opt-dir-or-x) (string=? "<-" opt-dir-or-x))))
	 (x-and-x-list (if left-to-right
			   rest
			   (cdr rest)))
	 (x (if (null? x-and-x-list)
		(myerror "simprat-with-intern" "more arguments expected")
		(car x-and-x-list)))
	 (x-list (cdr x-and-x-list))
	 (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (proof-and-new-num-goals-and-maxgoal
	  (if (and (string? x)
		   (let ((info (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS))))
		     (and info
			  (let* ((aconst (cadr info))
				 (aconst-formula (aconst-to-formula aconst))
				 (final-concl
				  (imp-impnc-all-allnc-form-to-final-conclusion
				   aconst-formula)))
			    (and (predicate-form? final-concl)
				 (pvar? (predicate-form-to-predicate
					 final-concl)))))))
	      (myerror "simprat-with-intern" "unexpected aconst name" x)
	      (apply x-and-x-list-to-proof-and-new-num-goals-and-maxgoal
		     num-goal (+ 1 maxgoal) x x-list)))
	 (eqv-proof (car proof-and-new-num-goals-and-maxgoal))
	 (new-num-goals (cadr proof-and-new-num-goals-and-maxgoal))
	 (new-maxgoal (caddr proof-and-new-num-goals-and-maxgoal))
	 (goal-formula (goal-to-formula goal))
	 (used-formula (proof-to-formula eqv-proof))
	 (used-prime-formula
	  (if (prime-form? used-formula) used-formula
	      (myerror "simprat-with-intern" "prime formula expected"
		       used-formula)))
	 (used-nprime-formula (normalize-formula used-prime-formula))
	 (used-kernel
	  (if (atom-form? used-prime-formula)
	      (atom-form-to-kernel used-prime-formula)
	      (myerror "simprat-with-intern" "atom formula expected"
		       used-prime-formula)))
	 (used-nkernel (nt used-kernel))
	 (op (term-in-app-form-to-final-op used-kernel))
	 (nop (term-in-app-form-to-final-op used-nkernel))
	 (ngoal-formula (nf goal-formula)))
    (cond
     ((and (prime-form? used-formula)
	   (term-in-const-form? op)
	   (string=? "RatEqv" (const-to-name (term-in-const-form-to-const op)))
	   (let* ((args (term-in-app-form-to-args used-kernel))
		  (lhs (car args))
		  (rhs (cadr args))
		  (type (term-to-type lhs))
		  (var (type-to-new-var type))
		  (varterm (make-term-in-var-form var))
		  (simprat-formula
		   (if left-to-right
		       (formula-gen-subst goal-formula lhs varterm)
		       (formula-gen-subst goal-formula rhs varterm))))
	     (not (formula=? simprat-formula goal-formula))))
      (let* ((args (term-in-app-form-to-args used-kernel))
	     (lhs (car args))
	     (rhs (cadr args))
	     (type (term-to-type lhs))
	     (var (type-to-new-var type))
	     (varterm (make-term-in-var-form var))
	     (simprat-formula ;A(var)
	      (if left-to-right
		  (formula-gen-subst goal-formula lhs varterm)
		  (formula-gen-subst goal-formula rhs varterm)))
	     (new (if left-to-right rhs lhs))
	     (old (if left-to-right lhs rhs))
	     (new-goal ;A(new)
	      (context-and-ncvars-and-formula-to-new-goal
	       context ncvars (formula-subst simprat-formula var new)))
	     (new-num-goal
	      (make-num-goal
	       (+ 1 maxgoal) new-goal drop-info hypname-info ignore-deco-flag))
	     (eqv-rev-proof ;of rhs==lhs
	       (mk-proof-in-elim-form
		(make-proof-in-aconst-form
		 (theorem-name-to-aconst "RatEqvSym"))
		lhs rhs eqv-proof))
	     (new-proof ;of A(old)
	      (mk-proof-in-elim-form
	       (rateqv-formula-compat-rev
		 simprat-formula var
		 (if left-to-right eqv-proof eqv-rev-proof) new-goal))))
	(make-pproof-state
	 (append (list new-num-goal) new-num-goals (cdr num-goals))
	 (goal-subst proof goal new-proof)
	 new-maxgoal)))
     ((and (prime-form? used-formula)
	   (term-in-const-form? nop)
	   (string=? "RatEqv" (const-to-name (term-in-const-form-to-const nop)))
	   (let* ((args (term-in-app-form-to-args used-nkernel))
		  (lhs (car args))
		  (rhs (cadr args))
		  (type (term-to-type lhs))
		  (var (type-to-new-var type))
		  (varterm (make-term-in-var-form var))
		  (simprat-formula
		   (if left-to-right
		       (formula-gen-subst goal-formula lhs varterm)
		       (formula-gen-subst goal-formula rhs varterm))))
	     (not (formula=? simprat-formula goal-formula))))
      (let* ((args (term-in-app-form-to-args used-nkernel))
	     (lhs (car args))
	     (rhs (cadr args))
	     (type (term-to-type lhs))
	     (var (type-to-new-var type))
	     (varterm (make-term-in-var-form var))
	     (simprat-formula ;A(var)
	      (if left-to-right
		  (formula-gen-subst goal-formula lhs varterm)
		  (formula-gen-subst goal-formula rhs varterm)))
	     (new (if left-to-right rhs lhs))
	     (old (if left-to-right lhs rhs))
	     (new-goal ;A(new)
	      (context-and-ncvars-and-formula-to-new-goal
	       context ncvars
	       (formula-subst simprat-formula var new)))
	     (new-num-goal
	      (make-num-goal
	       (+ 1 maxgoal) new-goal drop-info hypname-info ignore-deco-flag))
	     (eqv-rev-proof ;of rhs==lhs
	       (mk-proof-in-elim-form
		(make-proof-in-aconst-form
		 (theorem-name-to-aconst "RatEqvSym"))
		lhs rhs eqv-proof))
	     (new-proof ;of A(old)
	      (mk-proof-in-elim-form
	       (rateqv-formula-compat-rev
		 simprat-formula var
		 (if left-to-right eqv-proof eqv-rev-proof) new-goal))))
	(make-pproof-state
	 (append (list new-num-goal) new-num-goals (cdr num-goals))
	 (goal-subst proof goal new-proof)
	 new-maxgoal)))
     (else (myerror "simprat-with-intern" "goal cannot be simplified with"
		    used-formula)))))

;; Auxiliary functions

;; Given t(x), x, lhs, rhs and a proof of lhs==rhs, rateqv-term-compat
;; returns a proof of t(lhs)==t(rhs).  Here t(x), x, lhs, rhs are of
;; type rat.

(define (rateqv-term-compat term var term1 term2 eqv-proof)
  (cond
   ((not (member var (term-to-free term)))
    (make-proof-in-aconst-form truth-aconst)) ;a==a -> True is a rewrite rule
   ((term-in-var-form? term) eqv-proof) ;of term1==term2, i.e., lhs==rhs
   ((term-in-app-form? term)
    (let* ((op (term-in-app-form-to-final-op term))
	   (args (term-in-app-form-to-args term))
	   (name (if (not (term-in-const-form? op))
		     (myerror "rateqv-term-compat"
			      "term in constant form expected" op)
		     (string-append
		      (const-to-name (term-in-const-form-to-const op))
		      "Compat")))
	   (unary-compat-names
	    (list "RatUMinusCompat" "RatAbsCompat" "RatHalfCompat"
		  "RatUDivCompat"))
	   (binary-compat-names
	    (list "RatPlusCompat" "RatTimesCompat" "RatMinusCompat"
		  "RatDivCompat" "RatMaxCompat" "RatMinCompat")))
      (cond
       ((member name unary-compat-names)
	(mk-proof-in-elim-form ;of ~t(lhs)== ~t(rhs)
	 (make-proof-in-aconst-form ;of all a,b(a==b -> ~a== ~b))
	  (theorem-name-to-aconst name))
	 (term-subst (car args) var term1) ;t(lhs)
	 (term-subst (car args) var term2) ;t(rhs)
	 ;; (term-subst term var term1) ;t(lhs)
	 ;; (term-subst term var term2) ;t(rhs)
	 (rateqv-term-compat (car args) var term1 term2 eqv-proof)))
       ((member name binary-compat-names)
	(mk-proof-in-elim-form ;of t(lhs)+s(lhs)==t(rhs)+s(rhs)
	 (make-proof-in-aconst-form ;of all a,b,c,d(a==b -> c==d -> a+c==b+d))
	  (theorem-name-to-aconst name))
	 (term-subst (car args) var term1) ;t(lhs)
	 (term-subst (car args) var term2) ;t(rhs)
	 (term-subst (cadr args) var term1) ;s(lhs)
	 (term-subst (cadr args) var term2) ;s(rhs)
	 ;; (term-subst term var term1) ;t(lhs)+s(lhs)
	 ;; (term-subst term var term2) ;t(rhs)+s(rhs)
	 (rateqv-term-compat ;proves t(lhs)==t(rhs) from lhs==rhs by IH
	  (car args) var term1 term2 eqv-proof)
	 (rateqv-term-compat ;proves s(lhs)==s(rhs) from lhs==rhs by IH
	  (cadr args) var term1 term2 eqv-proof)))
       (else (apply myerror "rateqv-term-compat" name
		    "expected to be among" (append unary-compat-names
						   binary-compat-names))))))
   (else (myerror "rateqv-term-compat" "unexpected term" term))))

;; Given A(var), var, eqhyp: old==new, new-goal: A(new)
;; rateqv-formula-compat-rev returns a proof of A(old)

(define (rateqv-formula-compat-rev fla var eqhyp new-goal)
  (cond
   ((not (member var (formula-to-free fla))) new-goal)
   ((atom-form? fla)
    (let* ((kernel (atom-form-to-kernel fla)) ;t(var)<=s(var)
	   (op (if (not (term-in-app-form? kernel))
		   (myerror "rateqv-formula-compat-rev"
			    "term in application form expected" kernel)
		   (term-in-app-form-to-final-op kernel)))
	   (args (term-in-app-form-to-args kernel)) ;(t(var) s(var))
	   (name (if (not (term-in-const-form? op))
		     (myerror "rateqv-formula-compat-rev"
			      "term in constant form expected" op)
		     (string-append
		      (const-to-name (term-in-const-form-to-const op))
		      "Compat")))
	   (compat-names (list "RatLeCompat" "RatEqvCompat" "RatLtCompat"))
	   (old-and-new
	    (if (and (proof-form? eqhyp)
		     (atom-form? (proof-to-formula eqhyp))
		     (let ((kernel
			    (atom-form-to-kernel (proof-to-formula eqhyp))))
		       (and (term-in-app-form? kernel)
			    (let ((op (term-in-app-form-to-final-op kernel)))
			      (term-in-const-form? op)
			      (string=? "RatEqv"
					(const-to-name
					 (term-in-const-form-to-const op)))))))
		(term-in-app-form-to-args
		 (atom-form-to-kernel (proof-to-formula eqhyp)))
		(myerror "rateqv-formula-compat-rev" "eqhyp expected" eqhyp)))
	   (old (car old-and-new))
	   (new (cadr old-and-new)))
      (if
       (member name compat-names) ;all a,b,c,d(a==b -> c==d -> (a<=c)=(b<=d))
       (let* ((told (term-subst (car args) var old))
	      (tnew (term-subst (car args) var new))
	      (sold (term-subst (cadr args) var old))
	      (snew (term-subst (cadr args) var new))
	      (proof1 ;of told==tnew
	       (rateqv-term-compat (car args) var old new eqhyp))
	      (proof2 ;of sold==snew
	       (rateqv-term-compat (cadr args) var old new eqhyp))
	      (proof3 ;of (told<=sold)=(tnew<=snew)
	       (mk-proof-in-elim-form
		(make-proof-in-aconst-form (theorem-name-to-aconst name))
		;; all a,b,c,d(a==b -> c==d -> (a<=c)=(b<=d))
		told tnew sold snew proof1 proof2))
	      (eq-fla (proof-to-formula proof3))
	      (booleterms (term-in-app-form-to-args
			   (atom-form-to-kernel eq-fla)))
	      (booleterm1 (car booleterms)) ;told<=sold
	      (booleterm2 (cadr booleterms))) ;tnew<=snew
	 (mk-proof-in-elim-form
	  (make-proof-in-aconst-form
	   (theorem-name-to-aconst "BooleEqToAeqRight"))
	  ;; all boole1,boole2(boole1=boole2 -> boole2 -> boole1)
	  booleterm1 booleterm2 proof3 new-goal))
       (myerror "rateqv-formula-compat-rev"
		"RatLeCompat or RatEqvCompat or RatLtCompat expected"
		name))))
   (else (myerror "rateqv-formula-compat-rev" "not implemented for" fla))))

(define (simprat opt-dir-or-x . x-and-xs-or-xs)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing"))))
	 (simprat-result
	  (apply simprat-intern
		 num-goals proof maxgoal opt-dir-or-x x-and-xs-or-xs)))
    (if (not simprat-result)
	(begin (display-comment "no simplification possible")
	       (if COMMENT-FLAG (newline)))
	(begin
	  (set! PPROOF-STATE simprat-result)
	  (pproof-state-history-push PPROOF-STATE)
	  (display-new-goals num-goals number)))))

(define (simprat-intern num-goals proof
		     maxgoal . opt-dir-and-x-and-elab-path-and-terms)
  (let* ((opt-dir (if (null? opt-dir-and-x-and-elab-path-and-terms)
		      (myerror "simprat-intern" "more arguments expected")
		      (car opt-dir-and-x-and-elab-path-and-terms)))
	 (left-to-right (not (and (string? opt-dir) (string=? "<-" opt-dir))))
	 (x-and-elab-path-and-terms
	  (if left-to-right
	      opt-dir-and-x-and-elab-path-and-terms
	      (cdr opt-dir-and-x-and-elab-path-and-terms)))
	 (x (if (null? x-and-elab-path-and-terms)
		(myerror "simprat-intern" "more arguments expected")
		(car x-and-elab-path-and-terms)))
	 (elab-path-and-terms (cdr x-and-elab-path-and-terms))
	 (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (avars (context-to-avars context))
	 (maxhyp (length avars))
	 (goal-formula (goal-to-formula goal))
	 (leaf (if (formula-form? x)
		   (context-and-ncvars-and-formula-to-new-goal
		    context ncvars x)
		   (hyp-info-to-leaf num-goal x)))
	 (used-formula
	  (unfold-formula (if (formula-form? x) x (proof-to-formula leaf))))
	 (sig-vars (context-to-vars context))
	 (sig-tvars-and-sig-vars
	  (if (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS))
	      sig-vars
	      (append (formula-to-tvars used-formula) sig-vars)))
	 (elab-path (do ((l elab-path-and-terms (cdr l))
			 (res '() (if (memq (car l) '(left right))
				      (cons (car l) res)
				      res)))
			((null? l) (reverse res))))
	 (xs-and-vars-and-toinst1
	  (apply
	   fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
	   used-formula sig-tvars-and-sig-vars
	   goal-formula left-to-right
	   elab-path))
	 (xs-and-vars-and-toinst
	  (if xs-and-vars-and-toinst1
	      xs-and-vars-and-toinst1
	      (apply
	       fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
	       (normalize-formula used-formula)
	       sig-tvars-and-sig-vars
	       (normalize-formula goal-formula)
	       left-to-right
	       elab-path))))
    (if
     (not xs-and-vars-and-toinst)
     #f
     (let* ((xs (car xs-and-vars-and-toinst))
	    (vars (cadr xs-and-vars-and-toinst))
	    (toinst (caddr xs-and-vars-and-toinst))
	    (terms (do ((l elab-path-and-terms (cdr l))
			(res '() (if (memq (car l) '(left right))
				     res
				     (cons (car l) res))))
		       ((null? l) (reverse res))))
	    (subst (if (<= (length vars) (length terms))
		       (map list vars (list-head terms (length vars)))
		       empty-subst))
	    (subst-xs (map (lambda (x) (if (term-form? x)
					   (term-substitute x subst)
					   x))
			   xs))
	    (types (let ((info1 (assoc x THEOREMS))
			 (info2 (assoc x GLOBAL-ASSUMPTIONS))
			 (tsubst (list-transform-positive toinst
				   (lambda (x) (tvar-form? (car x))))))
		     (if
		      (and (or info1 info2) (pair? tsubst)) ;else '()
		      (let* ((aconst (if info1
					 (theorem-name-to-aconst x)
					 (global-assumption-name-to-aconst x)))
			     (fla (aconst-to-formula aconst))
			     (tvars (formula-to-tvars fla)))
			(map (lambda (tvar) (type-substitute tvar tsubst))
			     tvars))
		      '()))))
       (if (> (length vars) (length terms))
	   (apply myerror
		  "simprat-intern" "more terms expected, to be substituted for"
		  (list-tail vars (length terms))))
       (if (and COMMENT-FLAG (< (length vars) (length terms)))
	   (begin
	     (comment "warning: superfluous terms")
	     (for-each comment
		       (map term-to-string (list-tail terms (length vars))))))
       (apply simprat-with-intern
	      (if left-to-right
		  (append (list num-goals proof maxgoal x)
			  (append types subst-xs))
		  (append (list num-goals proof maxgoal "<-" x)
			  (append types subst-xs))))))))

;; In the following definition of simpreal-with x is one of the following.
;; - A number or string identifying a hypothesis form the context.
;; - The name of a theorem or global assumption, but not one whose final
;;   conclusion is a predicate variable.
;; - A closed proof.
;; - A formula with free variables from the context, generating a new goal.
;; Moreover xs is a list consisting of
;; - a number or string identifying a hypothesis form the context,
;; - the name of a theorem or global assumption,
;; - a closed proof,
;; - the string "?" (value of DEFAULT-GOAL-NAME), generating a new goal,
;; - a symbol left or right,
;; - a term, whose free variables are added to the context,
;; - a type, which is substituted for the 1st tvar,
;; - a comprehension term, which is substituted for the 1st pvar.
;; This generates a used formula lhs==rhs with lhs or its normal form present
;; in the goal.  Replace lhs by rhs.  In case "<-" exchange lhs by rhs.

(define (simpreal-with opt-dir-or-x . x-and-xs-or-xs)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply simpreal-with-intern
		 num-goals proof maxgoal opt-dir-or-x x-and-xs-or-xs))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (simpreal-with-intern num-goals proof maxgoal . rest)
  (let* ((opt-dir-or-x
	  (if (null? rest)
	      (myerror "simpreal-with-intern" "more arguments expected")
	      (car rest)))
	 (left-to-right
	  (not (and (string? opt-dir-or-x) (string=? "<-" opt-dir-or-x))))
	 (x-and-x-list (if left-to-right
			   rest
			   (cdr rest)))
	 (x (if (null? x-and-x-list)
		(myerror "simpreal-with-intern" "more arguments expected")
		(car x-and-x-list)))
	 (x-list (cdr x-and-x-list))
	 (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (proof-and-new-num-goals-and-maxgoal
	  (if (and (string? x)
		   (let ((info (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS))))
		     (and info
			  (let* ((aconst (cadr info))
				 (aconst-formula (aconst-to-formula aconst))
				 (final-concl
				  (imp-impnc-all-allnc-form-to-final-conclusion
				   aconst-formula)))
			    (and (predicate-form? final-concl)
				 (pvar? (predicate-form-to-predicate
					 final-concl)))))))
	      (myerror "simpreal-with-intern" "unexpected aconst name" x)
	      (apply x-and-x-list-to-proof-and-new-num-goals-and-maxgoal
		     num-goal (+ 1 maxgoal) x x-list)))
	 (eq-proof (car proof-and-new-num-goals-and-maxgoal))
	 (new-num-goals (cadr proof-and-new-num-goals-and-maxgoal))
	 (new-maxgoal (caddr proof-and-new-num-goals-and-maxgoal))
	 (goal-formula (goal-to-formula goal))
	 (used-formula (proof-to-formula eq-proof))
	 (used-nformula (normalize-formula used-formula))
	 (ngoal-formula (nf goal-formula)))
    (cond
     ((and (predicate-form? used-formula)
	   (idpredconst-form? (predicate-form-to-predicate used-formula))
	   (string=? "RealEq" (idpredconst-to-name
			       (predicate-form-to-predicate used-formula)))
	   (let* ((args (predicate-form-to-args used-formula))
		  ;; (args (term-in-app-form-to-args used-kernel))
		  (lhs (car args))
		  (rhs (cadr args))
		  (type (term-to-type lhs))
		  (var (type-to-new-var type))
		  (varterm (make-term-in-var-form var))
		  (simpreal-formula
		   (if left-to-right
		       (formula-gen-subst goal-formula lhs varterm)
		       (formula-gen-subst goal-formula rhs varterm))))
	     (not (formula=? simpreal-formula goal-formula))))
      (let* ((args (predicate-form-to-args used-formula))
	     ;; (args (term-in-app-form-to-args used-kernel))
	     (lhs (car args))
	     (rhs (cadr args))
	     (type (term-to-type lhs))
	     (var (type-to-new-var type))
	     (varterm (make-term-in-var-form var))
	     (simpreal-formula
	      (if left-to-right
		  (formula-gen-subst goal-formula lhs varterm)
		  (formula-gen-subst goal-formula rhs varterm)))
	     (new-goal ;A(rhs) or A(lhs)
	      (context-and-ncvars-and-formula-to-new-goal
	       context ncvars
	       (formula-subst simpreal-formula var
			      (if left-to-right rhs lhs))))
	     (new-num-goal
	      (make-num-goal
	       (+ 1 maxgoal) new-goal drop-info hypname-info ignore-deco-flag))
	     (new-proof ;of A(lhs) or A(rhs)
	      (mk-proof-in-elim-form
	       (realeq-formula-compat
		 simpreal-formula var
		 (if left-to-right lhs rhs)
		 (if left-to-right rhs lhs)
		 (if left-to-right
		     eq-proof
		     (mk-proof-in-elim-form
		      (make-proof-in-aconst-form
		       (theorem-name-to-aconst "RealEqSym"))
		      lhs rhs eq-proof)) context new-goal))))
	(make-pproof-state
	 (append (list new-num-goal) new-num-goals (cdr num-goals))
	 (goal-subst proof goal new-proof)
	 new-maxgoal)))
     ((and (predicate-form? used-nformula)
	   (idpredconst-form? (predicate-form-to-predicate used-nformula))
	   (string=? "RealEq" (idpredconst-to-name
			       (predicate-form-to-predicate used-nformula)))
	   (let* ((args (predicate-form-to-args used-nformula))
		  (lhs (car args))
		  (rhs (cadr args))
		  (type (term-to-type lhs))
		  (var (type-to-new-var type))
		  (varterm (make-term-in-var-form var))
		  (simpreal-formula
		   (if left-to-right
		       (formula-gen-subst goal-formula lhs varterm)
		       (formula-gen-subst goal-formula rhs varterm))))
	     (not (formula=? simpreal-formula goal-formula))))
      (let* ((args (predicate-form-to-args used-nformula))
	     (lhs (car args))
	     (rhs (cadr args))
	     (type (term-to-type lhs))
	     (var (type-to-new-var type))
	     (varterm (make-term-in-var-form var))
	     (simpreal-formula
	      (if left-to-right
		  (formula-gen-subst goal-formula lhs varterm)
		  (formula-gen-subst goal-formula rhs varterm)))
	     ;; (all-formula (mk-all var simpreal-formula))
	     (new-goal ;A(rhs) or A(lhs)
	      (context-and-ncvars-and-formula-to-new-goal
	       context ncvars
	       (formula-subst simpreal-formula var
			      (if left-to-right rhs lhs))))
	     (new-num-goal
	      (make-num-goal
	       (+ 1 maxgoal) new-goal drop-info hypname-info ignore-deco-flag))
	     (new-proof ;of A(lhs) or A(rhs)
	      (mk-proof-in-elim-form
	       (realeq-formula-compat
		 simpreal-formula var
		 (if left-to-right lhs rhs)
		 (if left-to-right rhs lhs)
		 (if left-to-right
		     eq-proof
		     (mk-proof-in-elim-form
		      (make-proof-in-aconst-form
		       (theorem-name-to-aconst "RealEqSym"))
		      lhs rhs eq-proof)) context new-goal))))
	(make-pproof-state
	 (append (list new-num-goal) new-num-goals (cdr num-goals))
	 (goal-subst proof goal new-proof)
	 new-maxgoal)))
     (else (myerror "simpreal-with-intern" "goal cannot be simplified with"
		    used-formula)))))

;; Auxiliary functions

;; Given t(var), var, lhs, rhs, an eq-proof of lhs===rhs or of the
;; formula all n lhs n===rhs n and a context.  Here t(var) is of type
;; rea and var, lhs, rhs are of type rea or nat=>rea.  Then
;; realeq-term-compat returns a proof of t(lhs)===t(rhs).  The context
;; is necessary to prove Real r and then reflexivity r===r for r
;; without x.  This needs RealUMinusCompat RealUDivCompat
;; RealAbsCompat RealExpCompat AvCompat VaCompat
;; RealPlusCompat RealTimesCompat RealMaxCompat RealMinCompat.

(define (realeq-term-compat term var term1 term2 eq-proof context)
  (cond
   ((not (member var (term-to-free term))) ;we prove r===r
    (let ((realproof (context-and-term-to-realproof context term)))
      (mk-proof-in-elim-form
       (make-proof-in-aconst-form (theorem-name-to-aconst "RealEqRefl"))
       term realproof)))
   ((term-in-var-form? term) eq-proof) ;of term1===term2, i.e., lhs===rhs
   ((term-in-app-form? term)
    (let ((op (term-in-app-form-to-op term)))
      (cond
       ((term=? op var) ;then arg is without var
	(make-proof-in-all-elim-form eq-proof (term-in-app-form-to-arg term)))
       ((term-in-abst-form? op) ;rec call with subst-kernel
       	(realeq-term-compat (term-to-one-step-beta-reduct term)
       	 var term1 term2 eq-proof context))
       (else
	(let* ((op (term-in-app-form-to-final-op term))
	       (args (term-in-app-form-to-args term))
	       (name (if (not (term-in-const-form? op))
			 (myerror "realeq-term-compat"
				  "term in constant form expected" op)
			 (string-append
			  (const-to-name (term-in-const-form-to-const op))
			  "Compat")))
	       (unary-compat-names
		(list "RealNNegCompat" "RealUMinusCompat" "RealUDivCompat"
		      "RealAbsCompat" "RealExpCompat"
		      "AvCompat" "VaCompat" ))
	       (binary-compat-names
		(list "RealPlusCompat" "RealTimesCompat"
		      "RealMaxCompat" "RealMinCompat")))
	  (cond
	   ((member name unary-compat-names)
	    (cond
	     ((string=? name "RealUDivCompat")
	      (mk-proof-in-elim-form ;of RealUDiv lhs p===RealUDiv rhs p
	       (make-proof-in-aconst-form ;of all x,y,p(x==y -> Pxp -> Pyp ->
					;RealUDix x p===RealUDiv y p)
		(theorem-name-to-aconst name))
	       (term-subst (car args) var term1) ;t(lhs)
	       (term-subst (car args) var term2) ;t(rhs)
	       (cadr args)
	       (realeq-term-compat (car args) var term1 term2 eq-proof context)
	       (context-and-term-and-bd-to-abspos-proof
		context term1 (cadr args))
	       (context-and-term-and-bd-to-abspos-proof
		context term2 (cadr args))))
	     ((string=? name "RealExpCompat")
	      (mk-proof-in-elim-form ;of t(lhs)===t(rhs), here lhs**n===rhs**n
	       (make-proof-in-aconst-form ;of all x,y,n(x==y -> x**n===y**n)
		(theorem-name-to-aconst name))
	       (term-subst (car args) var term1) ;t(lhs)
	       (term-subst (car args) var term2) ;t(rhs)
	       (cadr args)
	       (realeq-term-compat
		(car args) var term1 term2 eq-proof context)))
	     ((string=? name "AvCompat")
	      (mk-proof-in-elim-form ;of t(lhs)===t(rhs), here Av s x===Av s y
	       (make-proof-in-aconst-form ;of all x,y,s(x==y -> Av s x===Av s y)
		(theorem-name-to-aconst name))
	       (term-subst (cadr args) var term1) ;t(lhs)
	       (term-subst (cadr args) var term2) ;t(rhs)
	       (car args)
	       (realeq-term-compat
		(cadr args) var term1 term2 eq-proof context)))
	     ((string=? name "VaCompat")
	      (mk-proof-in-elim-form ;of t(lhs)===t(rhs), here Va s x===Va s y
	       (make-proof-in-aconst-form ;of all x,y,s(x==y -> Va s x===Va s y)
		(theorem-name-to-aconst name))
	       (term-subst (cadr args) var term1) ;t(lhs)
	       (term-subst (cadr args) var term2) ;t(rhs)
	       (car args)
	       (realeq-term-compat
		(cadr args) var term1 term2 eq-proof context)))
	     (else
	      (mk-proof-in-elim-form ;of ~t(lhs)=== ~t(rhs)
	       (make-proof-in-aconst-form ;of all x,y(x===y -> ~x=== ~y))
		(theorem-name-to-aconst name))
	       (term-subst (car args) var term1) ;t(lhs)
	       (term-subst (car args) var term2) ;t(rhs)
	       (realeq-term-compat
		(car args) var term1 term2 eq-proof context)))))
	   ((member name binary-compat-names)
	    (mk-proof-in-elim-form ;of t(lhs)+s(lhs)===t(rhs)+s(rhs)
	     (make-proof-in-aconst-form ;of all x,y,z,z1(x===y -> z===z1 ->
					; x+z===y+z1))
	      (theorem-name-to-aconst name))
	     (term-subst (car args) var term1) ;t(lhs)
	     (term-subst (car args) var term2) ;t(rhs)
	     (term-subst (cadr args) var term1) ;s(lhs)
	     (term-subst (cadr args) var term2) ;s(rhs)
	     (realeq-term-compat ;proves t(lhs)===t(rhs) from lhs===rhs by IH
	      (car args) var term1 term2 eq-proof context)
	     (realeq-term-compat ;proves s(lhs)===s(rhs) from lhs===rhs by IH
	      (cadr args) var term1 term2 eq-proof context)))
	   (else (apply myerror "realeq-term-compat" name
			"expected to be among"
			(append unary-compat-names
				binary-compat-names)))))))))
   (else (myerror "realeq-term-compat" "unexpected term" term))))

;; context-and-term-to-realproof returns either a proof of Real(term) or #f

(define (context-and-term-to-realproof context term)
  (let* ((avars (context-to-avars context))
	 (relevant-avars ;relevant idpcs I with term instance of an argument
	  (list-transform-positive avars
	    (lambda (avar)
	      (let* ((fla (avar-to-formula avar))
		     (vars (all-allnc-form-to-vars fla))
		     (kernel (all-allnc-form-to-final-kernel fla)))
		(and
		 (predicate-form? kernel)
		 (let ((pred (predicate-form-to-predicate kernel))
		       (args (predicate-form-to-args kernel)))
		   (and
		    (idpredconst-form? pred)
		    (let* ((name (idpredconst-to-name pred))
			   (extended-name (string-append name "ToReal"))
			   (applied-args ;for xs we need (xs n) with n new
			    (map (lambda (arg)
				   (if (and (arrow-form? (term-to-type arg))
					    (equal? (py "nat")
						    (arrow-form-to-arg-type
						     (term-to-type arg))))
				       (make-term-in-app-form
					arg (make-term-in-var-form
					     (type-to-new-var
					      (arrow-form-to-arg-type
					       (term-to-type arg)))))
				       arg))
				 args))
			   (matching-substs-or-f
			    (map (lambda (arg applied-arg)
				   (let* ((arg-vars (term-to-free arg))
					  (sig-vars (set-minus arg-vars vars)))
				     (apply match applied-arg term sig-vars)))
				 args applied-args)))
		      (and
		       (apply or-op matching-substs-or-f)
		       (or (member name (list "Real" "RealEq" "RealNNeg"
					      "RealLe" "RealConv"))
			   (assoc
			    extended-name
			    (append THEOREMS GLOBAL-ASSUMPTIONS))))))))))))
	 (name-avar-alist
	  (map (lambda (avar)
		 (let* ((fla (avar-to-formula avar))
			(kernel (all-allnc-form-to-final-kernel fla))
			(pred (predicate-form-to-predicate kernel))
			(name (idpredconst-to-name pred)))
		   (list name avar)))
	       relevant-avars)))
    (cond
     ((and ;term given as constant Cauchy sequence
       (term-in-app-form? term)
       (let ((op (term-in-app-form-to-final-op term))
	     (args (term-in-app-form-to-args term)))
	 (and (term-in-const-form? op)
	      (string=? (const-to-name (term-in-const-form-to-const op))
			"RealConstr")
	      (term-in-abst-form? (car args))
	      (not (member (term-in-abst-form-to-var (car args))
			   (term-to-free
			    (term-in-abst-form-to-kernel (car args))))))))
      (mk-proof-in-elim-form
       (make-proof-in-aconst-form (theorem-name-to-aconst "RealRat"))
       (term-in-abst-form-to-kernel (car (term-in-app-form-to-args term)))))
     ((pair? name-avar-alist) ;ex idpc-avars of the from I(..,term,..)
      (cond ;proof from the first such avar
       ((assoc "Real" name-avar-alist)
	(let* ((info (assoc "Real" name-avar-alist))
	       (avar (cadr info))
	       (fla (avar-to-formula avar))
	       (vars (all-allnc-form-to-vars fla))
	       (kernel (all-allnc-form-to-final-kernel fla))
	       (arg (car (predicate-form-to-args kernel)))
	       (arg-vars (term-to-free arg))
	       (sig-vars (set-minus arg-vars vars))
	       (subst (apply match arg term sig-vars))
	       (terms (map (lambda (var)
			     (let ((info (assoc var subst)))
			       (if info
				   (cadr info)
				   (make-term-in-var-form var))))
			   vars)))
	  (apply mk-proof-in-elim-form (make-proof-in-avar-form avar) terms)))
       ((assoc "RealEq" name-avar-alist)
	(let* ((info (assoc "RealEq" name-avar-alist))
	       (avar (cadr info))
	       (fla (avar-to-formula avar))
	       (vars (all-allnc-form-to-vars fla))
	       (kernel (all-allnc-form-to-final-kernel fla))
	       (args (predicate-form-to-args kernel))
	       (arg1 (car args))
	       (arg2 (cadr args))
	       (arg1-vars (term-to-free arg1))
	       (sig1-vars (set-minus arg1-vars vars))
	       (subst1 (apply match arg1 term sig1-vars)))
	  (if subst1
	      (let* ((terms (map (lambda (var)
				   (let ((info (assoc var subst1)))
				     (if info
					 (cadr info)
					 (make-term-in-var-form var))))
				 vars))
		     (eq-proof
		      (apply
		       mk-proof-in-elim-form
		       (make-proof-in-avar-form avar) terms)))
		(mk-proof-in-elim-form
		 (make-proof-in-aconst-form
		  (theorem-name-to-aconst "RealEqToReal0"))
		 term (term-substitute arg2 subst1) eq-proof))
	      (let* ((arg2-vars (term-to-free arg2))
		     (sig2-vars (set-minus arg2-vars vars))
		     (subst2 (apply match arg2 term sig2-vars))
		     (terms (map (lambda (var)
				   (let ((info (assoc var subst2)))
				     (if info
					 (cadr info)
					 (make-term-in-var-form var))))
				 vars))
		     (eq-proof
		      (apply
		       mk-proof-in-elim-form
		       (make-proof-in-avar-form avar) terms)))
		(mk-proof-in-elim-form
		 (make-proof-in-aconst-form
		  (theorem-name-to-aconst "RealEqToReal1"))
		 (term-substitute arg1 subst2) term eq-proof)))))
       ((assoc "RealNNeg" name-avar-alist)
	(let* ((info (assoc "RealNNeg" name-avar-alist))
	       (avar (cadr info))
	       (fla (avar-to-formula avar))
	       (vars (all-allnc-form-to-vars fla))
	       (kernel (all-allnc-form-to-final-kernel fla))
	       (args (predicate-form-to-args kernel))
	       (arg (car args))
	       (arg-vars (term-to-free arg))
	       (sig-vars (set-minus arg-vars vars))
	       (subst (apply match arg term sig-vars))
	       (terms (map (lambda (var)
			     (let ((info (assoc var subst)))
			       (if info
				   (cadr info)
				   (make-term-in-var-form var))))
			   vars))
	       (nneg-proof (apply mk-proof-in-elim-form
				  (make-proof-in-avar-form avar) terms)))
	  (mk-proof-in-elim-form
	   (make-proof-in-aconst-form
	    (theorem-name-to-aconst "RealNNegElim0"))
	   (term-substitute arg subst) nneg-proof)))
       ((assoc "RealLe" name-avar-alist)
	(let* ((info (assoc "RealLe" name-avar-alist))
	       (avar (cadr info))
	       (fla (avar-to-formula avar))
	       (vars (all-allnc-form-to-vars fla))
	       (kernel (all-allnc-form-to-final-kernel fla))
	       (args (predicate-form-to-args kernel))
	       (arg1 (car args))
	       (arg2 (cadr args))
	       (arg1-vars (term-to-free arg1))
	       (sig1-vars (set-minus arg1-vars vars))
	       (subst1 (apply match arg1 term sig1-vars)))
	  (if subst1
	      (let* ((terms (map (lambda (var)
				   (let ((info (assoc var subst1)))
				     (if info
					 (cadr info)
					 (make-term-in-var-form var))))
				 vars))
		     (le-proof
		      (apply
		       mk-proof-in-elim-form
		       (make-proof-in-avar-form avar) terms)))
		(mk-proof-in-elim-form
		 (make-proof-in-aconst-form
		  (theorem-name-to-aconst "RealLeElim0"))
		 term (term-substitute arg2 subst1) le-proof))
	      (let* ((arg2-vars (term-to-free arg2))
		     (sig2-vars (set-minus arg2-vars vars))
		     (subst2 (apply match arg2 term sig2-vars))
		     (terms (map (lambda (var)
				   (let ((info (assoc var subst2)))
				     (if info
					 (cadr info)
					 (make-term-in-var-form var))))
				 vars))
		     (le-proof
		      (apply
		       mk-proof-in-elim-form
		       (make-proof-in-avar-form avar) terms)))
		(mk-proof-in-elim-form
		 (make-proof-in-aconst-form
		  (theorem-name-to-aconst "RealLeElim1"))
		 (term-substitute arg1 subst2) term le-proof)))))
       ((assoc "RealConv" name-avar-alist)
	(let* ((info (assoc "RealConv" name-avar-alist))
	       (avar (cadr info))
	       (fla (avar-to-formula avar))
	       (vars (all-allnc-form-to-vars fla))
	       (kernel (all-allnc-form-to-final-kernel fla))
	       (args (predicate-form-to-args kernel))
	       (arg1 (car args))
	       (arg2 (cadr args))
	       (arg3 (caddr args))
	       (arg2-vars (term-to-free arg2))
	       (sig2-vars (set-minus arg2-vars vars))
	       (subst2 (apply match arg2 term sig2-vars)))
	  (if subst2
	      (let* ((terms (map (lambda (var)
				   (let ((info (assoc var subst2)))
				     (if info
					 (cadr info)
					 (make-term-in-var-form var))))
				 vars))
		     (conv-proof
		      (apply mk-proof-in-elim-form
			     (make-proof-in-avar-form avar) terms)))
		(mk-proof-in-elim-form
		 (make-proof-in-aconst-form
		  (theorem-name-to-aconst "RealConvElim2"))
		 (term-substitute arg1 subst2)
		 term (term-substitute arg3 subst2) conv-proof))
	      (let* ((arg1-vars (term-to-free arg1))
		     (sig1-vars (set-minus arg1-vars vars))
		     (nat-var (type-to-new-var (py "nat")))
		     (nat-var-term (make-term-in-var-form nat-var))
		     (applied-arg1 (make-term-in-app-form arg1 nat-var-term))
		     (subst1 (apply match applied-arg1 term sig1-vars))
		     (terms (map (lambda (var)
				   (let ((info (assoc var subst1)))
				     (if info
					 (cadr info)
					 (make-term-in-var-form var))))
				 vars))
		     (conv-proof
		      (apply mk-proof-in-elim-form
			     (make-proof-in-avar-form avar) terms)))
		(mk-proof-in-elim-form
		 (make-proof-in-aconst-form
		  (theorem-name-to-aconst "RealConvElim1"))
		 (term-substitute arg1 subst1)
		 (term-substitute arg2 subst1)
		 (term-substitute arg3 subst1)
		 conv-proof
		 (term-substitute nat-var-term subst1))))))
       (else
	(let ((shortened-name-avar-alist ;only those with ToReal aconst
	       (list-transform-positive name-avar-alist
		 (lambda (item)
		   (let* ((name (car item))
			  (extended-name (string-append name "ToReal")))
		     (assoc extended-name
			    (append THEOREMS GLOBAL-ASSUMPTIONS)))))))
	  (and
	   (pair? shortened-name-avar-alist) ;build proof, else rec call
	   (let* ((item (car shortened-name-avar-alist))
		  (name (car item))
		  (extended-name (string-append name "ToReal"))
		  (avar (cadr item)))
	     (mk-proof-in-elim-form
	      (make-proof-in-aconst-form
	       (if (assoc extended-name THEOREMS)
		   (theorem-name-to-aconst extended-name)
		   (global-assumption-name-to-aconst extended-name)))
	      term (make-proof-in-avar-form avar))))))))
     ((and ;RealUMinusReal etc with rec call
       (term-in-app-form? term)
       (let ((op (term-in-app-form-to-final-op term))
	     (args (term-in-app-form-to-args term)))
	 (and (term-in-const-form? op)
	      (let ((name (const-to-name (term-in-const-form-to-const op))))
		(member name '("RealPlus" "RealUMinus" "RealMinus" "RealTimes"
			       "RealUDiv" "RealDiv" "RealAbs" "RealExp"
			       "Av" "Va"
			       "RealMax" "RealMin" "RealSum"))))))
      (let* ((op (term-in-app-form-to-final-op term))
	     (args (term-in-app-form-to-args term))
	     (name (const-to-name (term-in-const-form-to-const op))))
	(cond
	 ((member name '("RealUMinus" "RealAbs"))
	  (let ((prev (context-and-term-to-realproof
		       context (car args))))
	    (and
	     prev
	     (mk-proof-in-elim-form
	      (make-proof-in-aconst-form
	       (theorem-name-to-aconst (string-append name "Real")))
	      (car args) prev))))
	 ((member name '("RealExp"))
	  (let ((prev (context-and-term-to-realproof context (car args))))
	    (and
	     prev
	     (mk-proof-in-elim-form
	      (make-proof-in-aconst-form
	       (theorem-name-to-aconst (string-append name "Real")))
	      (car args) (cadr args) prev))))
	 ((member name '("Av" "Va"))
	  (let ((prev (context-and-term-to-realproof context (cadr args))))
	    (and
	     prev
	     (mk-proof-in-elim-form
	      (make-proof-in-aconst-form
	       (theorem-name-to-aconst (string-append name "Real")))
	      (cadr args) (car args) prev))))
	 ((member name '("RealUDiv"))
	  (let ((prev (context-and-term-to-realproof context (car args)))
		(prevpos (context-and-term-and-bd-to-abspos-proof
			  context (car args) (cadr args))))
	    (and
	     prev
	     (mk-proof-in-elim-form
	      (make-proof-in-aconst-form
	       (theorem-name-to-aconst (string-append name "Real")))
	      (car args) (cadr args) prev prevpos))))
	 ((member name '("RealSum"))
	  (let* ((natvar (type-to-new-var (py "nat")))
		 (natvarterm (make-term-in-var-form natvar))
		 (appterm (make-term-in-app-form (caddr args) natvarterm)) ;xs l
		 (extended-context (append context (list natvar)))
		 (prev (context-and-term-to-realproof
			extended-context appterm)))
	    (and prev
		 (mk-proof-in-elim-form
		  (make-proof-in-aconst-form
		   (theorem-name-to-aconst (string-append name "Real")))
		  (car args) (cadr args) (caddr args)
		  (make-proof-in-all-intro-form natvar prev)))))
	 ((member name '("RealPlus" "RealMinus" "RealTimes"
			 "RealDiv" "RealMax" "RealMin"))
	  (let ((prev1 (context-and-term-to-realproof
			context (car args)))
		(prev2 (context-and-term-to-realproof
			context (cadr args))))
	    (and
	     prev1 prev2
	     (mk-proof-in-elim-form
	      (make-proof-in-aconst-form
	       (theorem-name-to-aconst (string-append name "Real")))
	      (car args) (cadr args) prev1 prev2))))
	 (else (myerror "context-and-term-to-realproof"
			"not implemented for" name)))))
     ((and (term-in-app-form? term)
	   (not (term-in-beta-normal-form? term)))
      (let ((nterm (term-to-beta-nf term)))
	(context-and-term-to-realproof context nterm)))
     (else (myerror "context-and-term-to-realproof"
		    "No realproof found for" term)))))

;; Code discarded 2022-02-26
;; ;; Given t(var), var, lhs, rhs, an eq-proof of lhs===rhs or of the
;; ;; formula all n lhs n===rhs n and a context.  Here t(var) is of type
;; ;; rea and var, lhs, rhs are of type rea or nat=>rea.  Then
;; ;; realeq-term-compat returns a proof of t(lhs)===t(rhs).  The context
;; ;; is necessary to prove Real r and then reflexivity r===r for r
;; ;; without x.  This needs RealUMinusCompat RealUDivCompat
;; ;; RealAbsCompat RealExpCompat RealPlusCompat RealTimesCompat
;; ;; RealMaxCompat RealMinCompat.

;; (define (realeq-term-compat term var term1 term2 eq-proof context)
;;   (cond
;;    ((not (member var (term-to-free term))) ;we prove r===r
;;     (let ((realproof (context-and-term-to-realproof context term)))
;;       (mk-proof-in-elim-form
;;        (make-proof-in-aconst-form (theorem-name-to-aconst "RealEqRefl"))
;;        term realproof)))
;;    ((term-in-var-form? term) eq-proof) ;of term1===term2, i.e., lhs===rhs
;;    ((term-in-app-form? term)
;;     (let ((op (term-in-app-form-to-op term)))
;;       (cond
;;        ((term=? op var) ;then arg is without var
;; 	(make-proof-in-all-elim-form eq-proof (term-in-app-form-to-arg term)))
;;        ((term-in-abst-form? op) ;rec call with subst-kernel
;;        	(realeq-term-compat (term-to-one-step-beta-reduct term)
;;        	 var term1 term2 eq-proof context))
;;        (else
;; 	(let* ((op (term-in-app-form-to-final-op term))
;; 	       (args (term-in-app-form-to-args term))
;; 	       (name (if (not (term-in-const-form? op))
;; 			 (myerror "realeq-term-compat"
;; 				  "term in constant form expected" op)
;; 			 (string-append
;; 			  (const-to-name (term-in-const-form-to-const op))
;; 			  "Compat")))
;; 	       (unary-compat-names
;; 		(list "RealNNegCompat" "RealUMinusCompat" "RealUDivCompat"
;; 		      "RealAbsCompat" "RealExpCompat"))
;; 	       (binary-compat-names
;; 		(list "RealPlusCompat" "RealTimesCompat"
;; 		      "RealMaxCompat" "RealMinCompat")))
;; 	  (cond
;; 	   ((member name unary-compat-names)
;; 	    (cond
;; 	     ((string=? name "RealUDivCompat")
;; 	      (mk-proof-in-elim-form ;of RealUDiv lhs p===RealUDiv rhs p
;; 	       (make-proof-in-aconst-form ;of all x,y,p(x==y -> Pxp -> Pyp ->
;; 					;RealUDix x p===RealUDiv y p)
;; 		(theorem-name-to-aconst name))
;; 	       (term-subst (car args) var term1) ;t(lhs)
;; 	       (term-subst (car args) var term2) ;t(rhs)
;; 	       (cadr args)
;; 	       (realeq-term-compat (car args) var term1 term2 eq-proof context)
;; 	       (context-and-term-and-bd-to-abspos-proof
;; 		context term1 (cadr args))
;; 	       (context-and-term-and-bd-to-abspos-proof
;; 		context term2 (cadr args))))
;; 	     ((string=? name "RealExpCompat")
;; 	      (mk-proof-in-elim-form ;of t(lhs)===t(rhs), here lhs**n===rhs**n
;; 	       (make-proof-in-aconst-form ;of all x,y,n(x==y -> x**n===y**n)
;; 		(theorem-name-to-aconst name))
;; 	       (term-subst (car args) var term1) ;t(lhs)
;; 	       (term-subst (car args) var term2) ;t(rhs)
;; 	       (cadr args)
;; 	       (realeq-term-compat
;; 		(car args) var term1 term2 eq-proof context)))
;; 	     (else
;; 	      (mk-proof-in-elim-form ;of ~t(lhs)=== ~t(rhs)
;; 	       (make-proof-in-aconst-form ;of all x,y(x===y -> ~x=== ~y))
;; 		(theorem-name-to-aconst name))
;; 	       (term-subst (car args) var term1) ;t(lhs)
;; 	       (term-subst (car args) var term2) ;t(rhs)
;; 	       (realeq-term-compat
;; 		(car args) var term1 term2 eq-proof context)))))
;; 	   ((member name binary-compat-names)
;; 	    (mk-proof-in-elim-form ;of t(lhs)+s(lhs)===t(rhs)+s(rhs)
;; 	     (make-proof-in-aconst-form ;of all x,y,z,z1(x===y -> z===z1 ->
;; 					; x+z===y+z1))
;; 	      (theorem-name-to-aconst name))
;; 	     (term-subst (car args) var term1) ;t(lhs)
;; 	     (term-subst (car args) var term2) ;t(rhs)
;; 	     (term-subst (cadr args) var term1) ;s(lhs)
;; 	     (term-subst (cadr args) var term2) ;s(rhs)
;; 	     (realeq-term-compat ;proves t(lhs)===t(rhs) from lhs===rhs by IH
;; 	      (car args) var term1 term2 eq-proof context)
;; 	     (realeq-term-compat ;proves s(lhs)===s(rhs) from lhs===rhs by IH
;; 	      (cadr args) var term1 term2 eq-proof context)))
;; 	   (else (apply myerror "realeq-term-compat" name
;; 			"expected to be among"
;; 			(append unary-compat-names
;; 				binary-compat-names)))))))))
;;    (else (myerror "realeq-term-compat" "unexpected term" term))))

;; ;; Code discarded 2021-02-24
;; ;; (define (realeq-term-compat term var term1 term2 eq-proof context)
;; ;;   (cond
;; ;;    ((not (member var (term-to-free term))) ;we prove r===r
;; ;;     (let ((realproof (context-and-term-to-realproof context term)))
;; ;;       (mk-proof-in-elim-form
;; ;;        (make-proof-in-aconst-form (theorem-name-to-aconst "RealEqRefl"))
;; ;;        term realproof)))
;; ;;    ((term-in-var-form? term) eq-proof) ;of term1===term2, i.e., lhs===rhs
;; ;;    ((term-in-app-form? term)
;; ;;     (let* ((op (term-in-app-form-to-final-op term))
;; ;; 	   (args (term-in-app-form-to-args term))
;; ;; 	   (name (if (not (term-in-const-form? op))
;; ;; 		     (myerror "realeq-term-compat"
;; ;; 			      "term in constant form expected" op)
;; ;; 		     (string-append
;; ;; 		      (const-to-name (term-in-const-form-to-const op))
;; ;; 		      "Compat")))
;; ;; 	   (unary-compat-names
;; ;; 	    (list "RealNNegCompat" "RealUMinusCompat" "RealUDivCompat"
;; ;; 		  "RealAbsCompat" "RealExpCompat"))
;; ;; 	   (binary-compat-names
;; ;; 	    (list "RealPlusCompat" "RealTimesCompat"
;; ;; 		  "RealMaxCompat" "RealMinCompat")))
;; ;;       (cond
;; ;;        ((member name unary-compat-names)
;; ;; 	(cond
;; ;; 	 ((string=? name "RealUDivCompat")
;; ;; 	  (mk-proof-in-elim-form ;of RealUDiv lhs p===RealUDiv rhs p
;; ;; 	   (make-proof-in-aconst-form ;of all x,y,p(x==y -> P|x|p -> P|y|p ->
;; ;; 					;RealUDix x p===RealUDiv y p)
;; ;; 	    (theorem-name-to-aconst name))
;; ;; 	   (term-subst (car args) var term1) ;t(lhs)
;; ;; 	   (term-subst (car args) var term2) ;t(rhs)
;; ;; 	   (cadr args)
;; ;; 	   (realeq-term-compat (car args) var term1 term2 eq-proof context)
;; ;; 	   (context-and-term-and-bd-to-abspos-proof context term1 (cadr args))
;; ;; 	   (context-and-term-and-bd-to-abspos-proof context term2 (cadr args))))
;; ;; 	 ((string=? name "RealExpCompat")
;; ;; 	  (mk-proof-in-elim-form ;of t(lhs)===t(rhs), here lhs**n===rhs**n
;; ;; 	   (make-proof-in-aconst-form ;of all x,y,n(x==y -> x**n===y**n)
;; ;; 	    (theorem-name-to-aconst name))
;; ;; 	   (term-subst (car args) var term1) ;t(lhs)
;; ;; 	   (term-subst (car args) var term2) ;t(rhs)
;; ;; 	   (cadr args)
;; ;; 	   (realeq-term-compat (car args) var term1 term2 eq-proof context)))
;; ;; 	 (else
;; ;; 	  (mk-proof-in-elim-form ;of ~t(lhs)=== ~t(rhs)
;; ;; 	   (make-proof-in-aconst-form ;of all x,y(x===y -> ~x=== ~y))
;; ;; 	    (theorem-name-to-aconst name))
;; ;; 	   (term-subst (car args) var term1) ;t(lhs)
;; ;; 	   (term-subst (car args) var term2) ;t(rhs)
;; ;; 	   (realeq-term-compat (car args) var term1 term2 eq-proof context)))))
;; ;;        ((member name binary-compat-names)
;; ;; 	(mk-proof-in-elim-form ;of t(lhs)+s(lhs)===t(rhs)+s(rhs)
;; ;; 	 (make-proof-in-aconst-form ;of all x,y,z,z1(x===y -> z===z1 ->
;; ;; 					; x+z===y+z1))
;; ;; 	  (theorem-name-to-aconst name))
;; ;; 	 (term-subst (car args) var term1) ;t(lhs)
;; ;; 	 (term-subst (car args) var term2) ;t(rhs)
;; ;; 	 (term-subst (cadr args) var term1) ;s(lhs)
;; ;; 	 (term-subst (cadr args) var term2) ;s(rhs)
;; ;; 	 (realeq-term-compat ;proves t(lhs)===t(rhs) from lhs===rhs by IH
;; ;; 	  (car args) var term1 term2 eq-proof context)
;; ;; 	 (realeq-term-compat ;proves s(lhs)===s(rhs) from lhs===rhs by IH
;; ;; 	  (cadr args) var term1 term2 eq-proof context)))
;; ;;        (else (apply myerror "realeq-term-compat" name
;; ;; 		    "expected to be among" (append unary-compat-names
;; ;; 						   binary-compat-names))))))
;; ;;    (else (myerror "realeq-term-compat" "unexpected term" term))))

;; ;; context-and-term-to-realproof returns either a proof of Real(term) or #f

;; (define (context-and-term-to-realproof context term)
;;   (let* ((avars (context-to-avars context))
;; 	 (relevant-avars ;relevant idpcs I with term instance of an argument
;; 	  (list-transform-positive avars
;; 	    (lambda (avar)
;; 	      (let* ((fla (avar-to-formula avar))
;; 		     (vars (all-allnc-form-to-vars fla))
;; 		     (kernel (all-allnc-form-to-final-kernel fla)))
;; 		(and
;; 		 (predicate-form? kernel)
;; 		 (let ((pred (predicate-form-to-predicate kernel))
;; 		       (args (predicate-form-to-args kernel)))
;; 		   (and
;; 		    (idpredconst-form? pred)
;; 		    (let* ((name (idpredconst-to-name pred))
;; 			   (extended-name (string-append name "ToReal"))
;; 			   (applied-args ;for xs we need (xs n) with n new
;; 			    (map (lambda (arg)
;; 				   (if (and (arrow-form? (term-to-type arg))
;; 					    (equal? (py "nat")
;; 						    (arrow-form-to-arg-type
;; 						     (term-to-type arg))))
;; 				       (make-term-in-app-form
;; 					arg (make-term-in-var-form
;; 					     (type-to-new-var
;; 					      (arrow-form-to-arg-type
;; 					       (term-to-type arg)))))
;; 				       arg))
;; 				 args))
;; 			   (matching-substs-or-f
;; 			    (map (lambda (arg applied-arg)
;; 				   (let* ((arg-vars (term-to-free arg))
;; 					  (sig-vars (set-minus arg-vars vars)))
;; 				     (apply match applied-arg term sig-vars)))
;; 				 args applied-args)))
;; 		      (and
;; 		       (apply or-op matching-substs-or-f)
;; 		       (or (member name (list "Real" "RealEq" "RealNNeg"
;; 					      "RealLe" "RealConv"))
;; 			   (assoc
;; 			    extended-name
;; 			    (append THEOREMS GLOBAL-ASSUMPTIONS))))))))))))
;; 	 (name-avar-alist
;; 	  (map (lambda (avar)
;; 		 (let* ((fla (avar-to-formula avar))
;; 			(kernel (all-allnc-form-to-final-kernel fla))
;; 			(pred (predicate-form-to-predicate kernel))
;; 			(name (idpredconst-to-name pred)))
;; 		   (list name avar)))
;; 	       relevant-avars)))
;;     (cond
;;      ((and ;term given as constant Cauchy sequence
;;        (term-in-app-form? term)
;;        (let ((op (term-in-app-form-to-final-op term))
;; 	     (args (term-in-app-form-to-args term)))
;; 	 (and (term-in-const-form? op)
;; 	      (string=? (const-to-name (term-in-const-form-to-const op))
;; 			"RealConstr")
;; 	      (term-in-abst-form? (car args))
;; 	      (not (member (term-in-abst-form-to-var (car args))
;; 			   (term-to-free
;; 			    (term-in-abst-form-to-kernel (car args))))))))
;;       (mk-proof-in-elim-form
;;        (make-proof-in-aconst-form (theorem-name-to-aconst "RealRat"))
;;        (term-in-abst-form-to-kernel (car (term-in-app-form-to-args term)))))
;;      ((pair? name-avar-alist) ;ex idpc-avars of the from I(..,term,..)
;;       (cond ;proof from the first such avar
;;        ((assoc "Real" name-avar-alist)
;; 	(let* ((info (assoc "Real" name-avar-alist))
;; 	       (avar (cadr info))
;; 	       (fla (avar-to-formula avar))
;; 	       (vars (all-allnc-form-to-vars fla))
;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; 	       (arg (car (predicate-form-to-args kernel)))
;; 	       (arg-vars (term-to-free arg))
;; 	       (sig-vars (set-minus arg-vars vars))
;; 	       (subst (apply match arg term sig-vars))
;; 	       (terms (map (lambda (var)
;; 			     (let ((info (assoc var subst)))
;; 			       (if info
;; 				   (cadr info)
;; 				   (make-term-in-var-form var))))
;; 			   vars)))
;; 	  (apply mk-proof-in-elim-form (make-proof-in-avar-form avar) terms)))
;;        ((assoc "RealEq" name-avar-alist)
;; 	(let* ((info (assoc "RealEq" name-avar-alist))
;; 	       (avar (cadr info))
;; 	       (fla (avar-to-formula avar))
;; 	       (vars (all-allnc-form-to-vars fla))
;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; 	       (args (predicate-form-to-args kernel))
;; 	       (arg1 (car args))
;; 	       (arg2 (cadr args))
;; 	       (arg1-vars (term-to-free arg1))
;; 	       (sig1-vars (set-minus arg1-vars vars))
;; 	       (subst1 (apply match arg1 term sig1-vars)))
;; 	  (if subst1
;; 	      (let* ((terms (map (lambda (var)
;; 				   (let ((info (assoc var subst1)))
;; 				     (if info
;; 					 (cadr info)
;; 					 (make-term-in-var-form var))))
;; 				 vars))
;; 		     (eq-proof
;; 		      (apply
;; 		       mk-proof-in-elim-form
;; 		       (make-proof-in-avar-form avar) terms)))
;; 		(mk-proof-in-elim-form
;; 		 (make-proof-in-aconst-form
;; 		  (theorem-name-to-aconst "RealEqToReal0"))
;; 		 term (term-substitute arg2 subst1) eq-proof))
;; 	      (let* ((arg2-vars (term-to-free arg2))
;; 		     (sig2-vars (set-minus arg2-vars vars))
;; 		     (subst2 (apply match arg2 term sig2-vars))
;; 		     (terms (map (lambda (var)
;; 				   (let ((info (assoc var subst2)))
;; 				     (if info
;; 					 (cadr info)
;; 					 (make-term-in-var-form var))))
;; 				 vars))
;; 		     (eq-proof
;; 		      (apply
;; 		       mk-proof-in-elim-form
;; 		       (make-proof-in-avar-form avar) terms)))
;; 		(mk-proof-in-elim-form
;; 		 (make-proof-in-aconst-form
;; 		  (theorem-name-to-aconst "RealEqToReal1"))
;; 		 (term-substitute arg1 subst2) term eq-proof)))))
;;        ((assoc "RealNNeg" name-avar-alist)
;; 	(let* ((info (assoc "RealNNeg" name-avar-alist))
;; 	       (avar (cadr info))
;; 	       (fla (avar-to-formula avar))
;; 	       (vars (all-allnc-form-to-vars fla))
;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; 	       (args (predicate-form-to-args kernel))
;; 	       (arg (car args))
;; 	       (arg-vars (term-to-free arg))
;; 	       (sig-vars (set-minus arg-vars vars))
;; 	       (subst (apply match arg term sig-vars))
;; 	       (terms (map (lambda (var)
;; 			     (let ((info (assoc var subst)))
;; 			       (if info
;; 				   (cadr info)
;; 				   (make-term-in-var-form var))))
;; 			   vars))
;; 	       (nneg-proof (apply mk-proof-in-elim-form
;; 				  (make-proof-in-avar-form avar) terms)))
;; 	  (mk-proof-in-elim-form
;; 	   (make-proof-in-aconst-form
;; 	    (theorem-name-to-aconst "RealNNegElim0"))
;; 	   (term-substitute arg subst) nneg-proof)))
;;        ((assoc "RealLe" name-avar-alist)
;; 	(let* ((info (assoc "RealLe" name-avar-alist))
;; 	       (avar (cadr info))
;; 	       (fla (avar-to-formula avar))
;; 	       (vars (all-allnc-form-to-vars fla))
;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; 	       (args (predicate-form-to-args kernel))
;; 	       (arg1 (car args))
;; 	       (arg2 (cadr args))
;; 	       (arg1-vars (term-to-free arg1))
;; 	       (sig1-vars (set-minus arg1-vars vars))
;; 	       (subst1 (apply match arg1 term sig1-vars)))
;; 	  (if subst1
;; 	      (let* ((terms (map (lambda (var)
;; 				   (let ((info (assoc var subst1)))
;; 				     (if info
;; 					 (cadr info)
;; 					 (make-term-in-var-form var))))
;; 				 vars))
;; 		     (le-proof
;; 		      (apply
;; 		       mk-proof-in-elim-form
;; 		       (make-proof-in-avar-form avar) terms)))
;; 		(mk-proof-in-elim-form
;; 		 (make-proof-in-aconst-form
;; 		  (theorem-name-to-aconst "RealLeElim0"))
;; 		 term (term-substitute arg2 subst1) le-proof))
;; 	      (let* ((arg2-vars (term-to-free arg2))
;; 		     (sig2-vars (set-minus arg2-vars vars))
;; 		     (subst2 (apply match arg2 term sig2-vars))
;; 		     (terms (map (lambda (var)
;; 				   (let ((info (assoc var subst2)))
;; 				     (if info
;; 					 (cadr info)
;; 					 (make-term-in-var-form var))))
;; 				 vars))
;; 		     (le-proof
;; 		      (apply
;; 		       mk-proof-in-elim-form
;; 		       (make-proof-in-avar-form avar) terms)))
;; 		(mk-proof-in-elim-form
;; 		 (make-proof-in-aconst-form
;; 		  (theorem-name-to-aconst "RealLeElim1"))
;; 		 (term-substitute arg1 subst2) term le-proof)))))
;;        ((assoc "RealConv" name-avar-alist)
;; 	(let* ((info (assoc "RealConv" name-avar-alist))
;; 	       (avar (cadr info))
;; 	       (fla (avar-to-formula avar))
;; 	       (vars (all-allnc-form-to-vars fla))
;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; 	       (args (predicate-form-to-args kernel))
;; 	       (arg1 (car args))
;; 	       (arg2 (cadr args))
;; 	       (arg3 (caddr args))
;; 	       (arg2-vars (term-to-free arg2))
;; 	       (sig2-vars (set-minus arg2-vars vars))
;; 	       (subst2 (apply match arg2 term sig2-vars)))
;; 	  (if subst2
;; 	      (let* ((terms (map (lambda (var)
;; 				   (let ((info (assoc var subst2)))
;; 				     (if info
;; 					 (cadr info)
;; 					 (make-term-in-var-form var))))
;; 				 vars))
;; 		     (conv-proof
;; 		      (apply mk-proof-in-elim-form
;; 			     (make-proof-in-avar-form avar) terms)))
;; 		(mk-proof-in-elim-form
;; 		 (make-proof-in-aconst-form
;; 		  (theorem-name-to-aconst "RealConvElim2"))
;; 		 (term-substitute arg1 subst2)
;; 		 term (term-substitute arg3 subst2) conv-proof))
;; 	      (let* ((arg1-vars (term-to-free arg1))
;; 		     (sig1-vars (set-minus arg1-vars vars))
;; 		     (nat-var (type-to-new-var (py "nat")))
;; 		     (nat-var-term (make-term-in-var-form nat-var))
;; 		     (applied-arg1 (make-term-in-app-form arg1 nat-var-term))
;; 		     (subst1 (apply match applied-arg1 term sig1-vars))
;; 		     (terms (map (lambda (var)
;; 				   (let ((info (assoc var subst1)))
;; 				     (if info
;; 					 (cadr info)
;; 					 (make-term-in-var-form var))))
;; 				 vars))
;; 		     (conv-proof
;; 		      (apply mk-proof-in-elim-form
;; 			     (make-proof-in-avar-form avar) terms)))
;; 		(mk-proof-in-elim-form
;; 		 (make-proof-in-aconst-form
;; 		  (theorem-name-to-aconst "RealConvElim1"))
;; 		 (term-substitute arg1 subst1)
;; 		 (term-substitute arg2 subst1)
;; 		 (term-substitute arg3 subst1)
;; 		 conv-proof
;; 		 (term-substitute nat-var-term subst1))))))
;;        (else
;; 	(let ((shortened-name-avar-alist ;only those with ToReal aconst
;; 	       (list-transform-positive name-avar-alist
;; 		 (lambda (item)
;; 		   (let* ((name (car item))
;; 			  (extended-name (string-append name "ToReal")))
;; 		     (assoc extended-name
;; 			    (append THEOREMS GLOBAL-ASSUMPTIONS)))))))
;; 	  (and
;; 	   (pair? shortened-name-avar-alist) ;build proof, else rec call
;; 	   (let* ((item (car shortened-name-avar-alist))
;; 		  (name (car item))
;; 		  (extended-name (string-append name "ToReal"))
;; 		  (avar (cadr item)))
;; 	     (mk-proof-in-elim-form
;; 	      (make-proof-in-aconst-form
;; 	       (if (assoc extended-name THEOREMS)
;; 		   (theorem-name-to-aconst extended-name)
;; 		   (global-assumption-name-to-aconst extended-name)))
;; 	      term (make-proof-in-avar-form avar))))))))
;;      ((and ;RealUMinusReal etc with rec call
;;        (term-in-app-form? term)
;;        (let ((op (term-in-app-form-to-final-op term))
;; 	     (args (term-in-app-form-to-args term)))
;; 	 (and (term-in-const-form? op)
;; 	      (let ((name (const-to-name (term-in-const-form-to-const op))))
;; 		(member name '("RealPlus" "RealUMinus" "RealMinus" "RealTimes"
;; 			       "RealUDiv" "RealDiv" "RealAbs" "RealExp"
;; 			       "RealMax" "RealMin" "RealSum"))))))
;;       (let* ((op (term-in-app-form-to-final-op term))
;; 	     (args (term-in-app-form-to-args term))
;; 	     (name (const-to-name (term-in-const-form-to-const op))))
;; 	(cond
;; 	 ((member name '("RealUMinus" "RealAbs"))
;; 	  (let ((prev (context-and-term-to-realproof
;; 		       context (car args))))
;; 	    (and
;; 	     prev
;; 	     (mk-proof-in-elim-form
;; 	      (make-proof-in-aconst-form
;; 	       (theorem-name-to-aconst (string-append name "Real")))
;; 	      (car args) prev))))
;; 	 ((member name '("RealExp"))
;; 	  (let ((prev (context-and-term-to-realproof context (car args))))
;; 	    (and
;; 	     prev
;; 	     (mk-proof-in-elim-form
;; 	      (make-proof-in-aconst-form
;; 	       (theorem-name-to-aconst (string-append name "Real")))
;; 	      (car args) (cadr args) prev))))
;; 	 ((member name '("RealUDiv"))
;; 	  (let ((prev (context-and-term-to-realproof context (car args)))
;; 		(prevpos (context-and-term-and-bd-to-abspos-proof
;; 			  context (car args) (cadr args))))
;; 	    (and
;; 	     prev
;; 	     (mk-proof-in-elim-form
;; 	      (make-proof-in-aconst-form
;; 	       (theorem-name-to-aconst (string-append name "Real")))
;; 	      (car args) (cadr args) prev prevpos))))
;; 	 ((member name '("RealSum"))
;; 	  (let* ((natvar (type-to-new-var (py "nat")))
;; 		 (natvarterm (make-term-in-var-form natvar))
;; 		 (appterm (make-term-in-app-form (caddr args) natvarterm)) ;xs l
;; 		 (extended-context (append context (list natvar)))
;; 		 (prev (context-and-term-to-realproof
;; 			extended-context appterm)))
;; 	    (and prev
;; 		 (mk-proof-in-elim-form
;; 		  (make-proof-in-aconst-form
;; 		   (theorem-name-to-aconst (string-append name "Real")))
;; 		  (car args) (cadr args) (caddr args)
;; 		  (make-proof-in-all-intro-form natvar prev)))))
;; 	 ((member name '("RealPlus" "RealMinus" "RealTimes"
;; 			 "RealDiv" "RealMax" "RealMin"))
;; 	  (let ((prev1 (context-and-term-to-realproof
;; 			context (car args)))
;; 		(prev2 (context-and-term-to-realproof
;; 			context (cadr args))))
;; 	    (and
;; 	     prev1 prev2
;; 	     (mk-proof-in-elim-form
;; 	      (make-proof-in-aconst-form
;; 	       (theorem-name-to-aconst (string-append name "Real")))
;; 	      (car args) (cadr args) prev1 prev2))))
;; 	 (else (myerror "context-and-term-to-realproof"
;; 			"not implemented for" name)))))
;;      ((and (term-in-app-form? term)
;; 	   (not (term-in-beta-normal-form? term)))
;;       (let ((nterm (term-to-beta-nf term)))
;; 	(context-and-term-to-realproof context nterm)))
;;      (else (myerror "context-and-term-to-realproof"
;; 		    "No realproof found for" term)))))

;; ;; Code discarded 2021-02-24
;; ;; (define (context-and-term-to-realproof context term)
;; ;;   (let* ((avars (context-to-avars context))
;; ;; 	 (relevant-avars ;relevant idpcs I with term instance of an argument
;; ;; 	  (list-transform-positive avars
;; ;; 	    (lambda (avar)
;; ;; 	      (let* ((fla (avar-to-formula avar))
;; ;; 		     (vars (all-allnc-form-to-vars fla))
;; ;; 		     (kernel (all-allnc-form-to-final-kernel fla)))
;; ;; 		(and
;; ;; 		 (predicate-form? kernel)
;; ;; 		 (let ((pred (predicate-form-to-predicate kernel))
;; ;; 		       (args (predicate-form-to-args kernel)))
;; ;; 		   (and
;; ;; 		    (idpredconst-form? pred)
;; ;; 		    (let* ((name (idpredconst-to-name pred))
;; ;; 			   (extended-name (string-append name "ToReal"))
;; ;; 			   (matching-substs-or-f
;; ;; 			    (map (lambda (arg)
;; ;; 				   (let* ((arg-vars (term-to-free arg))
;; ;; 					  (sig-vars (set-minus arg-vars vars)))
;; ;; 				     (apply match arg term sig-vars)))
;; ;; 				 args)))
;; ;; 		      (and
;; ;; 		       (apply or-op matching-substs-or-f)
;; ;; 		       (or (member
;; ;; 			    name (list "Real" "RealEq" "RealNNeg" "RealLe"))
;; ;; 			   (assoc
;; ;; 			    extended-name
;; ;; 			    (append THEOREMS GLOBAL-ASSUMPTIONS))))))))))))
;; ;; 	 (name-avar-alist
;; ;; 	  (map (lambda (avar)
;; ;; 		 (let* ((fla (avar-to-formula avar))
;; ;; 			(kernel (all-allnc-form-to-final-kernel fla))
;; ;; 			(pred (predicate-form-to-predicate kernel))
;; ;; 			(name (idpredconst-to-name pred)))
;; ;; 		   (list name avar)))
;; ;; 	       relevant-avars)))
;; ;;     (cond
;; ;;      ((and ;term given as constant Cauchy sequence
;; ;;        (term-in-app-form? term)
;; ;;        (let ((op (term-in-app-form-to-final-op term))
;; ;; 	     (args (term-in-app-form-to-args term)))
;; ;; 	 (and (term-in-const-form? op)
;; ;; 	      (string=? (const-to-name (term-in-const-form-to-const op))
;; ;; 			"RealConstr")
;; ;; 	      (term-in-abst-form? (car args))
;; ;; 	      (not (member (term-in-abst-form-to-var (car args))
;; ;; 			   (term-to-free
;; ;; 			    (term-in-abst-form-to-kernel (car args))))))))
;; ;;       (mk-proof-in-elim-form
;; ;;        (make-proof-in-aconst-form (theorem-name-to-aconst "RealRat"))
;; ;;        (term-in-abst-form-to-kernel (car (term-in-app-form-to-args term)))))
;; ;;      ((pair? name-avar-alist) ;ex idpc-avars of the from I(..,term,..)
;; ;;       (cond ;proof from the first such avar
;; ;;        ((assoc "Real" name-avar-alist)
;; ;; 	(let* ((info (assoc "Real" name-avar-alist))
;; ;; 	       (avar (cadr info))
;; ;; 	       (fla (avar-to-formula avar))
;; ;; 	       (vars (all-allnc-form-to-vars fla))
;; ;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; ;; 	       (arg (car (predicate-form-to-args kernel)))
;; ;; 	       (arg-vars (term-to-free arg))
;; ;; 	       (sig-vars (set-minus arg-vars vars))
;; ;; 	       (subst (apply match arg term sig-vars))
;; ;; 	       (terms (map (lambda (var)
;; ;; 			     (let ((info (assoc var subst)))
;; ;; 			       (if info
;; ;; 				   (cadr info)
;; ;; 				   (make-term-in-var-form var))))
;; ;; 			   vars)))
;; ;; 	  (apply mk-proof-in-elim-form (make-proof-in-avar-form avar) terms)))
;; ;;        ((assoc "RealEq" name-avar-alist)
;; ;; 	(let* ((info (assoc "RealEq" name-avar-alist))
;; ;; 	       (avar (cadr info))
;; ;; 	       (fla (avar-to-formula avar))
;; ;; 	       (vars (all-allnc-form-to-vars fla))
;; ;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; ;; 	       (args (predicate-form-to-args kernel))
;; ;; 	       (arg1 (car args))
;; ;; 	       (arg2 (cadr args))
;; ;; 	       (arg1-vars (term-to-free arg1))
;; ;; 	       (sig1-vars (set-minus arg1-vars vars))
;; ;; 	       (subst1 (apply match arg1 term sig1-vars)))
;; ;; 	  (if subst1
;; ;; 	      (let* ((terms (map (lambda (var)
;; ;; 				   (let ((info (assoc var subst1)))
;; ;; 				     (if info
;; ;; 					 (cadr info)
;; ;; 					 (make-term-in-var-form var))))
;; ;; 				 vars))
;; ;; 		     (eq-proof
;; ;; 		      (apply
;; ;; 		       mk-proof-in-elim-form
;; ;; 		       (make-proof-in-avar-form avar) terms)))
;; ;; 		(mk-proof-in-elim-form
;; ;; 		 (make-proof-in-aconst-form
;; ;; 		  (theorem-name-to-aconst "RealEqToReal0"))
;; ;; 		 term (term-substitute arg2 subst1) eq-proof))
;; ;; 	      (let* ((arg2-vars (term-to-free arg2))
;; ;; 		     (sig2-vars (set-minus arg2-vars vars))
;; ;; 		     (subst2 (apply match arg2 term sig2-vars))
;; ;; 		     (terms (map (lambda (var)
;; ;; 				   (let ((info (assoc var subst2)))
;; ;; 				     (if info
;; ;; 					 (cadr info)
;; ;; 					 (make-term-in-var-form var))))
;; ;; 				 vars))
;; ;; 		     (eq-proof
;; ;; 		      (apply
;; ;; 		       mk-proof-in-elim-form
;; ;; 		       (make-proof-in-avar-form avar) terms)))
;; ;; 		(mk-proof-in-elim-form
;; ;; 		 (make-proof-in-aconst-form
;; ;; 		  (theorem-name-to-aconst "RealEqToReal1"))
;; ;; 		 (term-substitute arg1 subst2) term eq-proof)))))
;; ;;        ((assoc "RealNNeg" name-avar-alist)
;; ;; 	(let* ((info (assoc "RealNNeg" name-avar-alist))
;; ;; 	       (avar (cadr info))
;; ;; 	       (fla (avar-to-formula avar))
;; ;; 	       (vars (all-allnc-form-to-vars fla))
;; ;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; ;; 	       (args (predicate-form-to-args kernel))
;; ;; 	       (arg (car args))
;; ;; 	       (arg-vars (term-to-free arg))
;; ;; 	       (sig-vars (set-minus arg-vars vars))
;; ;; 	       (subst (apply match arg term sig-vars))
;; ;; 	       (terms (map (lambda (var)
;; ;; 			     (let ((info (assoc var subst)))
;; ;; 			       (if info
;; ;; 				   (cadr info)
;; ;; 				   (make-term-in-var-form var))))
;; ;; 			   vars))
;; ;; 	       (nneg-proof (apply mk-proof-in-elim-form
;; ;; 				  (make-proof-in-avar-form avar) terms)))
;; ;; 	  (mk-proof-in-elim-form
;; ;; 	   (make-proof-in-aconst-form
;; ;; 	    (theorem-name-to-aconst "RealNNegElim0"))
;; ;; 	   (term-substitute arg subst) nneg-proof)))
;; ;;        ((assoc "RealLe" name-avar-alist)
;; ;; 	(let* ((info (assoc "RealLe" name-avar-alist))
;; ;; 	       (avar (cadr info))
;; ;; 	       (fla (avar-to-formula avar))
;; ;; 	       (vars (all-allnc-form-to-vars fla))
;; ;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; ;; 	       (args (predicate-form-to-args kernel))
;; ;; 	       (arg1 (car args))
;; ;; 	       (arg2 (cadr args))
;; ;; 	       (arg1-vars (term-to-free arg1))
;; ;; 	       (sig1-vars (set-minus arg1-vars vars))
;; ;; 	       (subst1 (apply match arg1 term sig1-vars)))
;; ;; 	  (if subst1
;; ;; 	      (let* ((terms (map (lambda (var)
;; ;; 				   (let ((info (assoc var subst1)))
;; ;; 				     (if info
;; ;; 					 (cadr info)
;; ;; 					 (make-term-in-var-form var))))
;; ;; 				 vars))
;; ;; 		     (le-proof
;; ;; 		      (apply
;; ;; 		       mk-proof-in-elim-form
;; ;; 		       (make-proof-in-avar-form avar) terms)))
;; ;; 		(mk-proof-in-elim-form
;; ;; 		 (make-proof-in-aconst-form
;; ;; 		  (theorem-name-to-aconst "RealLeElim0"))
;; ;; 		 term (term-substitute arg2 subst1) le-proof))
;; ;; 	      (let* ((arg2-vars (term-to-free arg2))
;; ;; 		     (sig2-vars (set-minus arg2-vars vars))
;; ;; 		     (subst2 (apply match arg2 term sig2-vars))
;; ;; 		     (terms (map (lambda (var)
;; ;; 				   (let ((info (assoc var subst2)))
;; ;; 				     (if info
;; ;; 					 (cadr info)
;; ;; 					 (make-term-in-var-form var))))
;; ;; 				 vars))
;; ;; 		     (le-proof
;; ;; 		      (apply
;; ;; 		       mk-proof-in-elim-form
;; ;; 		       (make-proof-in-avar-form avar) terms)))
;; ;; 		(mk-proof-in-elim-form
;; ;; 		 (make-proof-in-aconst-form
;; ;; 		  (theorem-name-to-aconst "RealLeElim1"))
;; ;; 		 (term-substitute arg1 subst2) term le-proof)))))
;; ;;        (else
;; ;; 	(let ((shortened-name-avar-alist ;only those with ToReal aconst
;; ;; 	       (list-transform-positive name-avar-alist
;; ;; 		 (lambda (item)
;; ;; 		   (let* ((name (car item))
;; ;; 			  (extended-name (string-append name "ToReal")))
;; ;; 		     (assoc extended-name
;; ;; 			    (append THEOREMS GLOBAL-ASSUMPTIONS)))))))
;; ;; 	  (and
;; ;; 	   (pair? shortened-name-avar-alist) ;build proof, else rec call
;; ;; 	   (let* ((item (car shortened-name-avar-alist))
;; ;; 		  (name (car item))
;; ;; 		  (extended-name (string-append name "ToReal"))
;; ;; 		  (avar (cadr item)))
;; ;; 	     (mk-proof-in-elim-form
;; ;; 	      (make-proof-in-aconst-form
;; ;; 	       (if (assoc extended-name THEOREMS)
;; ;; 		   (theorem-name-to-aconst extended-name)
;; ;; 		   (global-assumption-name-to-aconst extended-name)))
;; ;; 	      term (make-proof-in-avar-form avar))))))))
;; ;;      ((and ;RealUMinusReal etc with rec call
;; ;;        (term-in-app-form? term)
;; ;;        (let ((op (term-in-app-form-to-final-op term))
;; ;; 	     (args (term-in-app-form-to-args term)))
;; ;; 	 (and (term-in-const-form? op)
;; ;; 	      (let ((name (const-to-name (term-in-const-form-to-const op))))
;; ;; 		(member name '("RealPlus" "RealUMinus" "RealMinus" "RealTimes"
;; ;; 			       "RealUDiv" "RealDiv" "RealAbs" "RealExp"
;; ;; 			       "RealMax" "RealMin"))))))
;; ;;       (let* ((op (term-in-app-form-to-final-op term))
;; ;; 	     (args (term-in-app-form-to-args term))
;; ;; 	     (name (const-to-name (term-in-const-form-to-const op))))
;; ;; 	(cond
;; ;; 	 ((member name '("RealUMinus" "RealAbs"))
;; ;; 	  (let ((prev (context-and-term-to-realproof
;; ;; 		       context (car args))))
;; ;; 	    (and
;; ;; 	     prev
;; ;; 	     (mk-proof-in-elim-form
;; ;; 	      (make-proof-in-aconst-form
;; ;; 	       (theorem-name-to-aconst (string-append name "Real")))
;; ;; 	      (car args) prev))))
;; ;; 	 ((member name '("RealExp"))
;; ;; 	  (let ((prev (context-and-term-to-realproof context (car args))))
;; ;; 	    (and
;; ;; 	     prev
;; ;; 	     (mk-proof-in-elim-form
;; ;; 	      (make-proof-in-aconst-form
;; ;; 	       (theorem-name-to-aconst (string-append name "Real")))
;; ;; 	      (car args) (cadr args) prev))))
;; ;; 	 ((member name '("RealUDiv"))
;; ;; 	  (let ((prev (context-and-term-to-realproof context (car args)))
;; ;; 		(prevpos (context-and-term-and-bd-to-abspos-proof
;; ;; 			  context (car args) (cadr args))))
;; ;; 	    (and
;; ;; 	     prev
;; ;; 	     (mk-proof-in-elim-form
;; ;; 	      (make-proof-in-aconst-form
;; ;; 	       (theorem-name-to-aconst (string-append name "Real")))
;; ;; 	      (car args) (cadr args) prev prevpos))))
;; ;; 	 ((member name '("RealPlus" "RealMinus" "RealTimes"
;; ;; 			 "RealDiv" "RealMax" "RealMin"))
;; ;; 	  (let ((prev1 (context-and-term-to-realproof
;; ;; 			context (car args)))
;; ;; 		(prev2 (context-and-term-to-realproof
;; ;; 			context (cadr args))))
;; ;; 	    (and
;; ;; 	     prev1 prev2
;; ;; 	     (mk-proof-in-elim-form
;; ;; 	      (make-proof-in-aconst-form
;; ;; 	       (theorem-name-to-aconst (string-append name "Real")))
;; ;; 	      (car args) (cadr args) prev1 prev2))))
;; ;; 	 (else (myerror "context-and-term-to-realproof"
;; ;; 			"not implemented for" name)))))
;; ;;      (else (myerror "context-and-term-to-realproof"
;; ;; 		    "No realproof found for" term)))))

;; context-and-term-and-bd-to-abspos-proof searches for a proof of
;; RealPos abs term bd from the context.  It returns #f if none is
;; found.  It looks for an avar u:allnc vars RealPos arg1 arg2 and
;; first for a subst mapping arg1 -> abs term and arg2 -> bd.  Take
;; this avar-proof.  Else it looks for a subst mapping arg1 -> term
;; and arg2 -> bd.  This gives a proof of RealPos term bd.  Now use
;; RealPosToPosAbs to infer RealPos abs term bd.

(define (context-and-term-and-bd-to-abspos-proof context term bd)
  (do ((avars (context-to-avars context) (cdr avars))
       (res
	#f
	(let* ((avar (car avars))
	       (fla (avar-to-formula avar))
	       (vars (all-allnc-form-to-vars fla))
	       (kernel (all-allnc-form-to-final-kernel fla)))
	  (if
	   (not (atom-form? kernel))
	   res
	   (let* ((boolean-kernel (atom-form-to-kernel kernel))
		  (op (term-in-app-form-to-final-op boolean-kernel))
		  (args (term-in-app-form-to-args boolean-kernel))
		  (arg-vars (term-to-free boolean-kernel))
		  (sig-vars (set-minus arg-vars vars)))
	     (if
	      (or (not (term-in-const-form? op))
		  (not (string=?
			(const-to-name (term-in-const-form-to-const op))
			"RealPos")))
	      res
	      (let* ((absterm (make-term-in-app-form
			       (pt "RealAbs") term))
		     (matching-subst-or-f ;turns args into (absterm bd)
		      (apply match-list args (list absterm bd) sig-vars)))
		(if
		 matching-subst-or-f ;build proof from avar
		 (let ((terms
			(map (lambda (var)
			       (let ((info (assoc var matching-subst-or-f)))
				 (if info
				     (cadr info)
				     (make-term-in-var-form var))))
			     vars)))
		   (apply mk-proof-in-elim-form
			  (make-proof-in-avar-form avar)
			  terms)) ;else
		 (let ((matching-subst2-or-f ;turns args into (term bd)
			(apply match-list args (list term bd) sig-vars)))
		   (if
		    matching-subst2-or-f ;use RealPosToPosAbs to build proof
		    (let* ((terms
			    (map (lambda (var)
				   (let ((info (assoc var
						      matching-subst2-or-f)))
				     (if info
					 (cadr info)
					 (make-term-in-var-form var))))
				 vars))
			   (proof1 ;of RealPos term bd
			    (apply mk-proof-in-elim-form
				   (make-proof-in-avar-form avar)
				   terms)))
		      (mk-proof-in-elim-form
		       (make-proof-in-aconst-form
			(theorem-name-to-aconst "RealPosToPosAbs"))
		       bd term proof1))
		    res))))))))))
      ;; ((or res (null? avars)) res)))
      ((or res (null? avars))
       (if res res
	   (myerror "context-and-term-and-bd-to-abspos-proof"
		    "no abspos proof found for" term bd)))))

;; Code discarded 2021-01-16
;; (define (context-and-term-and-bd-to-abspos-proof context term bd)
;;   (let* ((avars (context-to-avars context))
;; 	 (pos-avars
;; 	  (list-transform-positive avars
;; 	    (lambda (avar)
;; 	      (let* ((fla (avar-to-formula avar))
;; 		     (vars (all-allnc-form-to-vars fla))
;; 		     (kernel (all-allnc-form-to-final-kernel fla)))
;; 		(and
;; 		 (atom-form? kernel)
;; 		 (let* ((boolean-kernel (atom-form-to-kernel kernel))
;; 			(op (term-in-app-form-to-final-op boolean-kernel))
;; 			(args (term-in-app-form-to-args boolean-kernel)))
;; 		   (and
;; 		    (term-in-const-form? op)
;; 		    (string=?
;; 		     (const-to-name (term-in-const-form-to-const op))
;; 		     "RealPos")
;; 		    (let ((matching-substs-or-f
;; 			   (map (lambda (arg)
;; 				  (let* ((arg-vars (term-to-free arg))
;; 					 (sig-vars (set-minus arg-vars vars)))
;; 				    (apply match arg term sig-vars)))
;; 				args)))
;; 		      (apply or-op matching-substs-or-f)))))))))
;; 	 (abspos-avars
;; 	  (list-transform-positive pos-avars
;; 	    (lambda (avar)
;; 	      (let* ((fla (avar-to-formula avar))
;; 		     (vars (all-allnc-form-to-vars fla))
;; 		     (kernel (all-allnc-form-to-final-kernel fla))
;; 		     (args (predicate-form-to-args kernel)))
;; 		(and (term-in-app-form? (car args))
;; 		     (term-in-const-form?
;; 		      (term-in-app-form-to-final-op (car args)))
;; 		     (string=?
;; 		      "RealAbs"
;; 		      (const-to-name
;; 		       (term-in-const-form-to-const
;; 			(term-in-app-form-to-final-op (car args)))))))))))
;;     (cond
;;      ((pair? abspos-avars) ;ex avar RealPos(abs term)bd.  Take 1st
;;       (let* ((avar (car abspos-avars))
;; 	     (fla (avar-to-formula avar))
;; 	     (vars (all-allnc-form-to-vars fla))
;; 	     (kernel (all-allnc-form-to-final-kernel fla)) ;RealPos(abs term)bd
;; 	     (args (predicate-form-to-args kernel)) ;(abs term) bd
;; 	     (arg1 (car args))
;; 	     (arg2 (cadr args))
;; 	     (arg1-vars (term-to-free arg1))
;; 	     (arg2-vars (term-to-free arg2))
;; 	     (sig-vars (set-minus (append arg1-vars arg2-vars) vars))
;; 	     (pred-fla (make-predicate-formula
;; 			(predicate-form-to-predicate kernel) term bd))
;; 	     (subst (apply match kernel pred-fla sig-vars))
;; 	     (terms (map (lambda (var)
;; 			   (let ((info (assoc var subst)))
;; 			     (if info
;; 				 (cadr info)
;; 				 (make-term-in-var-form var))))
;; 			 vars)))
;; 	(apply mk-proof-in-elim-form (make-proof-in-avar-form avar) terms)))
;;      ((pair? pos-avars) ;ex avar RealPos term bd.  Apply RealPosToPosAbs to 1st
;;       (let* ((avar (car abspos-avars))
;; 	     (fla (avar-to-formula avar))
;; 	     (vars (all-allnc-form-to-vars fla))
;; 	     (kernel (all-allnc-form-to-final-kernel fla)) ;RealPos term bd
;; 	     (args (predicate-form-to-args kernel)) ;term bd
;; 	     (arg1 (car args))
;; 	     (arg2 (cadr args))
;; 	     (arg1-vars (term-to-free arg1))
;; 	     (arg2-vars (term-to-free arg2))
;; 	     (sig-vars (set-minus (append arg1-vars arg2-vars) vars))
;; 	     (pred-fla (make-predicate-formula
;; 			(predicate-form-to-predicate kernel) term bd))
;; 	     (subst (apply match kernel pred-fla sig-vars))
;; 	     (terms (map (lambda (var)
;; 			   (let ((info (assoc var subst)))
;; 			     (if info
;; 				 (cadr info)
;; 				 (make-term-in-var-form var))))
;; 			 vars))
;; 	     (proof1 (apply mk-proof-in-elim-form
;; 			    (make-proof-in-avar-form avar) terms)))
;; 	(apply mk-proof-in-elim-form
;; 	       (make-proof-in-aconst-form
;; 		(theorem-name-to-aconst "RealPosToPosAbs"))
;; 	       bd term proof1)))
;;      (else (myerror "context-and-term-and-bd-to-abspos-proof"
;; 		    "no abspos proof found for" term bd)))))

;; Code discarded 2021-01-11
;; (define (realeq-term-compat term var term1 term2 eq-proof context)
;;   (cond
;;    ((not (member var (term-to-free term))) ;we prove r===r
;;     (let ((realproof (context-and-term-to-realproof context term)))
;;       (mk-proof-in-elim-form
;;        (make-proof-in-aconst-form (theorem-name-to-aconst "RealEqRefl"))
;;        term realproof)))
;;    ((term-in-var-form? term) eq-proof) ;of term1===term2, i.e., lhs===rhs
;;    ((term-in-app-form? term)
;;     (let* ((op (term-in-app-form-to-final-op term))
;; 	   (args (term-in-app-form-to-args term))
;; 	   (name (if (not (term-in-const-form? op))
;; 		     (myerror "realeq-term-compat"
;; 			      "term in constant form expected" op)
;; 		     (string-append
;; 		      (const-to-name (term-in-const-form-to-const op))
;; 		      "Compat")))
;; 	   (unary-compat-names
;; 	    (list "RealNNegCompat" "RealUMinusCompat" "RealAbsCompat"))
;; 	   (binary-compat-names
;; 	    (list "RealPlusCompat" "RealTimesCompat")))
;;       (cond
;;        ((member name unary-compat-names)
;; 	(mk-proof-in-elim-form ;of ~t(lhs)=== ~t(rhs)
;; 	 (make-proof-in-aconst-form ;of all x,y(x===y -> ~x=== ~y))
;; 	  (theorem-name-to-aconst name))
;; 	 (term-subst (car args) var term1) ;t(lhs)
;; 	 (term-subst (car args) var term2) ;t(rhs)
;; 	 (realeq-term-compat (car args) var term1 term2 eq-proof context)))
;;        ((member name binary-compat-names)
;; 	(mk-proof-in-elim-form ;of t(lhs)+s(lhs)===t(rhs)+s(rhs)
;; 	 (make-proof-in-aconst-form ;of all x,y,z,z1(x===y -> z===z1 ->
;; 					; x+z===y+z1))
;; 	  (theorem-name-to-aconst name))
;; 	 (term-subst (car args) var term1) ;t(lhs)
;; 	 (term-subst (car args) var term2) ;t(rhs)
;; 	 (term-subst (cadr args) var term1) ;s(lhs)
;; 	 (term-subst (cadr args) var term2) ;s(rhs)
;; 	 (realeq-term-compat ;proves t(lhs)===t(rhs) from lhs===rhs by IH
;; 	  (car args) var term1 term2 eq-proof context)
;; 	 (realeq-term-compat ;proves s(lhs)===s(rhs) from lhs===rhs by IH
;; 	  (cadr args) var term1 term2 eq-proof context)))
;;        (else (apply myerror "realeq-term-compat" name
;; 		    "expected to be among" (append unary-compat-names
;; 						   binary-compat-names))))))
;;    (else (myerror "realeq-term-compat" "unexpected term" term))))

;; ;; context-and-term-to-realproof returns either a proof of Real(term) or #f

;; (define (context-and-term-to-realproof context term)
;;   (let* ((avars (context-to-avars context))
;; 	 (relevant-avars ;relevant idpcs I with term instance of an argument
;; 	  (list-transform-positive avars
;; 	    (lambda (avar)
;; 	      (let* ((fla (avar-to-formula avar))
;; 		     (vars (all-allnc-form-to-vars fla))
;; 		     (kernel (all-allnc-form-to-final-kernel fla)))
;; 		(and
;; 		 (predicate-form? kernel)
;; 		 (let ((pred (predicate-form-to-predicate kernel))
;; 		       (args (predicate-form-to-args kernel)))
;; 		   (and
;; 		    (idpredconst-form? pred)
;; 		    (let* ((name (idpredconst-to-name pred))
;; 			   (extended-name (string-append name "ToReal"))
;; 			   (matching-substs-or-f
;; 			    (map (lambda (arg)
;; 				   (let* ((arg-vars (term-to-free arg))
;; 					  (sig-vars (set-minus arg-vars vars)))
;; 				     (apply match arg term sig-vars)))
;; 				 args)))
;; 		      (and
;; 		       (apply or-op matching-substs-or-f)
;; 		       (or (member
;; 			    name (list "Real" "RealEq" "RealNNeg" "RealLe"))
;; 			   (assoc
;; 			    extended-name
;; 			    (append THEOREMS GLOBAL-ASSUMPTIONS))))))))))))
;; 	 (name-avar-alist
;; 	  (map (lambda (avar)
;; 		 (let* ((fla (avar-to-formula avar))
;; 			(kernel (all-allnc-form-to-final-kernel fla))
;; 			(pred (predicate-form-to-predicate kernel))
;; 			(name (idpredconst-to-name pred)))
;; 		   (list name avar)))
;; 	       relevant-avars)))
;;     (cond
;;      ((and ;term given as constant Cauchy sequence
;;        (term-in-app-form? term)
;;        (let ((op (term-in-app-form-to-final-op term))
;; 	     (args (term-in-app-form-to-args term)))
;; 	 (and (term-in-const-form? op)
;; 	      (string=? (const-to-name (term-in-const-form-to-const op))
;; 			"RealConstr")
;; 	      (term-in-abst-form? (car args))
;; 	      (not (member (term-in-abst-form-to-var (car args))
;; 			   (term-to-free
;; 			    (term-in-abst-form-to-kernel (car args))))))))
;;       (mk-proof-in-elim-form
;;        (make-proof-in-aconst-form (theorem-name-to-aconst "RealRat"))
;;        (term-in-abst-form-to-kernel (car (term-in-app-form-to-args term)))))
;;      ((pair? name-avar-alist) ;ex idpc-avars of the from I(..,term,..)
;;       (cond ;proof from the first such avar
;;        ((assoc "Real" name-avar-alist)
;; 	(let* ((info (assoc "Real" name-avar-alist))
;; 	       (avar (cadr info))
;; 	       (fla (avar-to-formula avar))
;; 	       (vars (all-allnc-form-to-vars fla))
;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; 	       (arg (car (predicate-form-to-args kernel)))
;; 	       (arg-vars (term-to-free arg))
;; 	       (sig-vars (set-minus arg-vars vars))
;; 	       (subst (apply match arg term sig-vars))
;; 	       (terms (map (lambda (var)
;; 			     (let ((info (assoc var subst)))
;; 			       (if info
;; 				   (cadr info)
;; 				   (make-term-in-var-form var))))
;; 			   vars)))
;; 	  (apply mk-proof-in-elim-form (make-proof-in-avar-form avar) terms)))
;;        ((assoc "RealEq" name-avar-alist)
;; 	(let* ((info (assoc "RealEq" name-avar-alist))
;; 	       (avar (cadr info))
;; 	       (fla (avar-to-formula avar))
;; 	       (vars (all-allnc-form-to-vars fla))
;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; 	       (args (predicate-form-to-args kernel))
;; 	       (arg1 (car args))
;; 	       (arg2 (cadr args))
;; 	       (arg1-vars (term-to-free arg1))
;; 	       (sig1-vars (set-minus arg1-vars vars))
;; 	       (subst1 (apply match arg1 term sig1-vars)))
;; 	  (if subst1
;; 	      (let* ((terms (map (lambda (var)
;; 				   (let ((info (assoc var subst1)))
;; 				     (if info
;; 					 (cadr info)
;; 					 (make-term-in-var-form var))))
;; 				 vars))
;; 		     (eq-proof
;; 		      (apply
;; 		       mk-proof-in-elim-form
;; 		       (make-proof-in-avar-form avar) terms)))
;; 		(mk-proof-in-elim-form
;; 		 (make-proof-in-aconst-form
;; 		  (theorem-name-to-aconst "RealEqElim0"))
;; 		 term (term-substitute arg2 subst1) eq-proof))
;; 	      (let* ((arg2-vars (term-to-free arg2))
;; 		     (sig2-vars (set-minus arg2-vars vars))
;; 		     (subst2 (apply match arg2 term sig2-vars))
;; 		     (terms (map (lambda (var)
;; 				   (let ((info (assoc var subst2)))
;; 				     (if info
;; 					 (cadr info)
;; 					 (make-term-in-var-form var))))
;; 				 vars))
;; 		     (eq-proof
;; 		      (apply
;; 		       mk-proof-in-elim-form
;; 		       (make-proof-in-avar-form avar) terms)))
;; 		(mk-proof-in-elim-form
;; 		 (make-proof-in-aconst-form
;; 		  (theorem-name-to-aconst "RealEqElim1"))
;; 		 (term-substitute arg1 subst2) term eq-proof)))))
;;        ((assoc "RealNNeg" name-avar-alist)
;; 	(let* ((info (assoc "RealNNeg" name-avar-alist))
;; 	       (avar (cadr info))
;; 	       (fla (avar-to-formula avar))
;; 	       (vars (all-allnc-form-to-vars fla))
;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; 	       (args (predicate-form-to-args kernel))
;; 	       (arg (car args))
;; 	       (arg-vars (term-to-free arg))
;; 	       (sig-vars (set-minus arg-vars vars))
;; 	       (subst (apply match arg term sig-vars))
;; 	       (terms (map (lambda (var)
;; 			     (let ((info (assoc var subst)))
;; 			       (if info
;; 				   (cadr info)
;; 				   (make-term-in-var-form var))))
;; 			   vars))
;; 	       (nneg-proof (apply mk-proof-in-elim-form
;; 				  (make-proof-in-avar-form avar) terms)))
;; 	  (mk-proof-in-elim-form
;; 	   (make-proof-in-aconst-form
;; 	    (theorem-name-to-aconst "RealNNegElim0"))
;; 	   (term-substitute arg subst) nneg-proof)))
;;        ((assoc "RealLe" name-avar-alist)
;; 	(let* ((info (assoc "RealLe" name-avar-alist))
;; 	       (avar (cadr info))
;; 	       (fla (avar-to-formula avar))
;; 	       (vars (all-allnc-form-to-vars fla))
;; 	       (kernel (all-allnc-form-to-final-kernel fla))
;; 	       (args (predicate-form-to-args kernel))
;; 	       (arg1 (car args))
;; 	       (arg2 (cadr args))
;; 	       (arg1-vars (term-to-free arg1))
;; 	       (sig1-vars (set-minus arg1-vars vars))
;; 	       (subst1 (apply match arg1 term sig1-vars)))
;; 	  (if subst1
;; 	      (let* ((terms (map (lambda (var)
;; 				   (let ((info (assoc var subst1)))
;; 				     (if info
;; 					 (cadr info)
;; 					 (make-term-in-var-form var))))
;; 				 vars))
;; 		     (le-proof
;; 		      (apply
;; 		       mk-proof-in-elim-form
;; 		       (make-proof-in-avar-form avar) terms)))
;; 		(mk-proof-in-elim-form
;; 		 (make-proof-in-aconst-form
;; 		  (theorem-name-to-aconst "RealLeElim0"))
;; 		 term (term-substitute arg2 subst1) le-proof))
;; 	      (let* ((arg2-vars (term-to-free arg2))
;; 		     (sig2-vars (set-minus arg2-vars vars))
;; 		     (subst2 (apply match arg2 term sig2-vars))
;; 		     (terms (map (lambda (var)
;; 				   (let ((info (assoc var subst2)))
;; 				     (if info
;; 					 (cadr info)
;; 					 (make-term-in-var-form var))))
;; 				 vars))
;; 		     (le-proof
;; 		      (apply
;; 		       mk-proof-in-elim-form
;; 		       (make-proof-in-avar-form avar) terms)))
;; 		(mk-proof-in-elim-form
;; 		 (make-proof-in-aconst-form
;; 		  (theorem-name-to-aconst "RealLeElim1"))
;; 		 (term-substitute arg1 subst2) term le-proof)))))
;;        (else
;; 	(let ((shortened-name-avar-alist ;only those with ToReal aconst
;; 	       (list-transform-positive name-avar-alist
;; 		 (lambda (item)
;; 		   (let* ((name (car item))
;; 			  (extended-name (string-append name "ToReal")))
;; 		     (assoc extended-name
;; 			    (append THEOREMS GLOBAL-ASSUMPTIONS)))))))
;; 	  (and
;; 	   (pair? shortened-name-avar-alist) ;build proof, else rec call
;; 	   (let* ((item (car shortened-name-avar-alist))
;; 		  (name (car item))
;; 		  (extended-name (string-append name "ToReal"))
;; 		  (avar (cadr item)))
;; 	     (mk-proof-in-elim-form
;; 	      (make-proof-in-aconst-form
;; 	       (if (assoc extended-name THEOREMS)
;; 		   (theorem-name-to-aconst extended-name)
;; 		   (global-assumption-name-to-aconst extended-name)))
;; 	      term (make-proof-in-avar-form avar))))))))
;;      ((and ;RealUMinusReal etc with rec call
;;        (term-in-app-form? term)
;;        (let ((op (term-in-app-form-to-final-op term))
;; 	     (args (term-in-app-form-to-args term)))
;; 	 (and (term-in-const-form? op)
;; 	      (let ((name (const-to-name (term-in-const-form-to-const op))))
;; 		(member name '("RealUMinus" "RealAbs" "RealPlus" "RealMinus"
;; 			       "RealTimes" "RealDiv" "RealMax" "RealMin"))))))
;;       (let* ((op (term-in-app-form-to-final-op term))
;; 	     (args (term-in-app-form-to-args term))
;; 	     (name (const-to-name (term-in-const-form-to-const op))))
;; 	(cond
;; 	 ((member name '("RealUMinus" "RealAbs"))
;; 	  (let ((prev (context-and-term-to-realproof
;; 		       context (car args))))
;; 	    (and
;; 	     prev
;; 	     (mk-proof-in-elim-form
;; 	      (make-proof-in-aconst-form
;; 	       (theorem-name-to-aconst (string-append name "Real")))
;; 	      (car args) prev))))
;; 	 ((member name '("RealPlus" "RealMinus" "RealTimes"
;; 			 "RealDiv" "RealMax" "RealMin"))
;; 	  (let ((prev1 (context-and-term-to-realproof
;; 			context (car args)))
;; 		(prev2 (context-and-term-to-realproof
;; 			context (cadr args))))
;; 	    (and
;; 	     prev1 prev2
;; 	     (mk-proof-in-elim-form
;; 	      (make-proof-in-aconst-form
;; 	       (theorem-name-to-aconst (string-append name "Real")))
;; 	      (car args) (cadr args) prev1 prev2))))
;; 	 (else (myerror "context-and-term-to-realproof"
;; 			"not implemented for" name)))))
;;      (else (myerror "context-and-term-to-realproof"
;; 		    "No realproof found for" term)))))

(define (realproof)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing"))))
	 (search-result (realproof-intern num-goals proof maxgoal)))
    (if (not search-result)
	(begin (display-comment "no proof found")
	       (if COMMENT-FLAG (newline)))
	(begin
	  (set! PPROOF-STATE search-result)
	  (pproof-state-history-push PPROOF-STATE)
	  (if
	   COMMENT-FLAG
	   (begin
	     (display-comment "ok, " DEFAULT-GOAL-NAME "_"
			      (number-to-string number)
			      " is proved.")
	     (if (null? (pproof-state-to-num-goals))
		 (begin (display "  Proof finished.") (newline))
		 (begin (display "  The active goal now is") (newline)
			(display-num-goal
			 (car (pproof-state-to-num-goals)))))))))))  

(define (realproof-intern num-goals proof maxgoal)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (formula (goal-to-formula goal))
	 (pred (if (predicate-form? formula)
		   (predicate-form-to-predicate formula)
		   (myerror "realproof-intern" "predicate form expected"
			    formula)))
	 (term (if (and (idpredconst-form? pred)
			(string=? "Real" (idpredconst-to-name pred)))
		   (car (predicate-form-to-args formula))
		   (myerror "realproof-intern" "Real term expected" formula)))
 	 (proof1 (context-and-term-to-realproof context term)))
    (if (not proof1)
	#f
	(make-pproof-state (cdr num-goals)
			   (goal-subst proof goal proof1)
			   maxgoal))))

;; Given A(var), var, lhs, rhs and an eq-proof of lhs===rhs or of the
;; formula all n lhs n===rhs n and a context.  We also have a new-goal
;; of A(rhs).  Then realeq-formula-compat returns a proof of A(lhs).
;; Here A(var) is an inductive predicate (for instance I, CoI, CoG)
;; and var, lhs, rhs are of type rea or nat=>rea.  This needs
;; RealEqCompat RealNNegCompat RealLeCompat RealConvCompat and
;; compatibility theorems for inductive predicate constants.

(define (realeq-formula-compat fla var term1 term2 eq-proof context new-goal)
  (cond
   ((not (member var (formula-to-free fla))) new-goal)
   ((predicate-form? fla) ;CoI t(x) or t(x)<<=s(x)
    (let* ((pred (predicate-form-to-predicate fla))
	   (args (predicate-form-to-args fla))) ;t(x) or (t(x) s(x))
      (if
       (idpredconst-form? pred)
       (let* ((name (idpredconst-to-name pred))
	      (theorem-name (string-append name "Compat"))
	      (aconst (theorem-name-to-aconst theorem-name))
	      (eq-rev-proof ;of rhs===lhs
	       (mk-proof-in-elim-form
		(make-proof-in-aconst-form
		 (theorem-name-to-aconst "RealEqSym"))
		term1 term2 eq-proof))
	      (l (length args)))
	 (cond
	  ((= 1 l) ;CoICompat allnc x,y(x===y -> CoI x -> CoI y)
	   (let* ((tlhs (term-subst (car args) var term1))
		  (trhs (term-subst (car args) var term2))
		  (proof1 ;of trhs===tlhs
		   (cond
		    ((term=? trhs tlhs)
		     (let ((realproof-or-f
			    (context-and-term-to-realproof context trhs)))
		       (if realproof-or-f
			   (mk-proof-in-elim-form
			    (make-proof-in-aconst-form
			     (theorem-name-to-aconst "RealEqRefl"))
			    trhs realproof-or-f)
			   (myerror "realeq-formula-compat" "First put"
				    (make-predicate-formula
				     (make-idpredconst "Real" '() '()) trhs)
				    "into the context, using assert"))))
		    ((formula=? (make-predicate-formula
				 (make-idpredconst "RealEq" '() '())
				 trhs tlhs)
				(proof-to-formula eq-proof))
		     eq-proof)
		    ((formula=? (make-predicate-formula
				 (make-idpredconst "RealEq" '() '())
				 trhs tlhs)
				(proof-to-formula eq-rev-proof))
		     eq-rev-proof)
		    (else (realeq-term-compat
			   (car args) var term2 term1 eq-rev-proof context)))))
	     (mk-proof-in-elim-form
	      (make-proof-in-aconst-form aconst)
	      trhs tlhs proof1 new-goal)))
	  ((= 2 l) ;RealLeCompat all x,y,z,z0(x===y -> z===z0 ->
	 				; x<<=z -> y<<=z0)
	   (let* ((tlhs (term-subst (car args) var term1))
		  (trhs (term-subst (car args) var term2))
		  (slhs (term-subst (cadr args) var term1))
		  (srhs (term-subst (cadr args) var term2))
		  (proof1 ;of trhs===tlhs
		   (cond
		    ((term=? trhs tlhs)
		     (let ((realproof-or-f
			    (context-and-term-to-realproof context trhs)))
		       (if realproof-or-f
			   (mk-proof-in-elim-form
			    (make-proof-in-aconst-form
			     (theorem-name-to-aconst "RealEqRefl"))
			    trhs realproof-or-f)
			   (myerror "realeq-formula-compat" "First put"
				    (make-predicate-formula
				     (make-idpredconst "Real" '() '()) trhs)
				    "into the context, using assert"))))
		    ((formula=? (make-predicate-formula
				 (make-idpredconst "RealEq" '() '())
				 trhs tlhs)
				(proof-to-formula eq-proof))
		     eq-proof)
		    ((formula=? (make-predicate-formula
				 (make-idpredconst "RealEq" '() '())
				 trhs tlhs)
				(proof-to-formula eq-rev-proof))
		     eq-rev-proof)
		    (else (realeq-term-compat
			   (car args) var term2 term1 eq-rev-proof context))))
		  (proof2 ;of srhs===slhs
		   (cond
		    ((term=? srhs slhs)
		     (let ((realproof-or-f
			    (context-and-term-to-realproof context srhs)))
		       (if realproof-or-f
			   (mk-proof-in-elim-form
			    (make-proof-in-aconst-form
			     (theorem-name-to-aconst "RealEqRefl"))
			    srhs realproof-or-f)
			   (myerror "realeq-formula-compat" "First put"
				    (make-predicate-formula
				     (make-idpredconst "Real" '() '()) srhs)
				    "in the context, using assert"))))
		    ((formula=? (make-predicate-formula
				 (make-idpredconst "RealEq" '() '())
				 srhs slhs)
				(proof-to-formula eq-proof))
		     eq-proof)
		    ((formula=? (make-predicate-formula
				 (make-idpredconst "RealEq" '() '())
				 srhs slhs)
				(proof-to-formula eq-rev-proof))
		     eq-rev-proof)
		    (else (realeq-term-compat
			   (cadr args) var term2 term1 eq-rev-proof context)))))
	     (mk-proof-in-elim-form
	      (make-proof-in-aconst-form aconst)
	      trhs tlhs srhs slhs proof1 proof2 new-goal)))
	  ((= 3 l) ;RealConvCompat: all xs,x,M,ys,y,N(all n xs n===ys n ->
					;x===y -> all p M p=N p ->
					;RealConv xs x M -> RealConv ys y N)
	   (let* ((tlhs (term-subst (car args) var term1))
		  (trhs (term-subst (car args) var term2))
		  (slhs (term-subst (cadr args) var term1))
		  (srhs (term-subst (cadr args) var term2))
		  (rlhs (term-subst (caddr args) var term1)) ;empty subst
		  (rrhs (term-subst (caddr args) var term2))
		  (proof1 ;of all n tlhs n===trhs n
		   (let* ((natvar (type-to-new-var (py "nat")))
			  (natvarterm (make-term-in-var-form natvar))
			  (appterm
			   (make-term-in-app-form (car args) natvarterm)))
		     (make-proof-in-all-intro-form
		      natvar (realeq-term-compat
			      appterm var term1 term2 eq-proof context))))
		  (proof2 ;of slhs===srhs
		   (cond
		    ((term=? srhs slhs)
		     (let ((realproof-or-f
			    (context-and-term-to-realproof context srhs)))
		       (if realproof-or-f
			   (mk-proof-in-elim-form
			    (make-proof-in-aconst-form
			     (theorem-name-to-aconst "RealEqRefl"))
			    srhs realproof-or-f)
			   (myerror "realeq-formula-compat" "First put"
				    (make-predicate-formula
				     (make-idpredconst "Real" '() '()) srhs)
				    "in the context, using assert"))))
		    ((formula=? (make-predicate-formula
				 (make-idpredconst "RealEq" '() '())
				 srhs slhs)
				(proof-to-formula eq-proof))
		     eq-proof)
		    ((formula=? (make-predicate-formula
				 (make-idpredconst "RealEq" '() '())
				 srhs slhs)
				(proof-to-formula eq-rev-proof))
		     eq-rev-proof)
		    (else (realeq-term-compat
			   (cadr args) var term2 term1 eq-rev-proof context))))
		  (proof3 ;of all n rlhs n===rrhs n, both equal to (caddr args)
		   (make-proof-in-all-intro-form ;pf all p M p=N p
		    (pv "p") (make-proof-in-aconst-form truth-aconst))))
	     (mk-proof-in-elim-form
	      (make-proof-in-aconst-form aconst)
	      trhs srhs rrhs tlhs slhs rlhs proof1 proof2 proof3 new-goal)))
	  (else (myerror "realeq-formula-compat" "arity 1,2 or 3 expected"
	 		 name))))
       (myerror "realeq-formula-compat" "idpredconst expected" fla))))
   (else (myerror "realeq-formula-compat" "not implemented for formula" fla))))

;; Code discarded 2021-02-21
;; (define (realeq-formula-compat fla var term1 term2 eq-proof context new-goal)
;;   (cond
;;    ((not (member var (formula-to-free fla))) new-goal)
;;    ((predicate-form? fla) ;CoI t(x) or t(x)<<=s(x)
;;     (let* ((pred (predicate-form-to-predicate fla))
;; 	   (args (predicate-form-to-args fla))) ;t(x) or (t(x) s(x))
;;       (if
;;        (idpredconst-form? pred)
;;        (let* ((name (idpredconst-to-name pred))
;; 	      (theorem-name (string-append name "Compat"))
;; 	      (aconst (theorem-name-to-aconst theorem-name))
;; 	      (eq-rev-proof ;of rhs===lhs
;; 	       (mk-proof-in-elim-form
;; 		(make-proof-in-aconst-form
;; 		 (theorem-name-to-aconst "RealEqSym"))
;; 		term1 term2 eq-proof))
;; 	      (l (length args)))
;; 	 (cond
;; 	  ((= 1 l) ;CoICompat allnc x,y(x===y -> CoI x -> CoI y)
;; 	   (let* ((tlhs (term-subst (car args) var term1))
;; 		  (trhs (term-subst (car args) var term2))
;; 		  (proof1 ;of trhs===tlhs
;; 		   (cond
;; 		    ((term=? trhs tlhs)
;; 		     (let ((realproof-or-f
;; 			    (context-and-term-to-realproof context trhs)))
;; 		       (if realproof-or-f
;; 			   (mk-proof-in-elim-form
;; 			    (make-proof-in-aconst-form
;; 			     (theorem-name-to-aconst "RealEqRefl"))
;; 			    trhs realproof-or-f)
;; 			   (myerror "realeq-formula-compat" "First put"
;; 				    (make-predicate-formula
;; 				     (make-idpredconst "Real" '() '()) trhs)
;; 				    "into the context, using assert"))))
;; 		    ((formula=? (make-predicate-formula
;; 				 (make-idpredconst "RealEq" '() '())
;; 				 trhs tlhs)
;; 				(proof-to-formula eq-proof))
;; 		     eq-proof)
;; 		    ((formula=? (make-predicate-formula
;; 				 (make-idpredconst "RealEq" '() '())
;; 				 trhs tlhs)
;; 				(proof-to-formula eq-rev-proof))
;; 		     eq-rev-proof)
;; 		    (else (realeq-term-compat
;; 			   (car args) var term2 term1 eq-rev-proof context)))))
;; 	     (mk-proof-in-elim-form
;; 	      (make-proof-in-aconst-form aconst)
;; 	      trhs tlhs proof1 new-goal)))
;; 	  ((= 2 l) ;RealLeCompat all x,y,z,z0(x===y -> z===z0 ->
;; 	 				; x<<=z -> y<<=z0)
;; 	   (let* ((tlhs (term-subst (car args) var term1))
;; 		  (trhs (term-subst (car args) var term2))
;; 		  (slhs (term-subst (cadr args) var term1))
;; 		  (srhs (term-subst (cadr args) var term2))
;; 		  (proof1 ;of trhs===tlhs
;; 		   (cond
;; 		    ((term=? trhs tlhs)
;; 		     (let ((realproof-or-f
;; 			    (context-and-term-to-realproof context trhs)))
;; 		       (if realproof-or-f
;; 			   (mk-proof-in-elim-form
;; 			    (make-proof-in-aconst-form
;; 			     (theorem-name-to-aconst "RealEqRefl"))
;; 			    trhs realproof-or-f)
;; 			   (myerror "realeq-formula-compat" "First put"
;; 				    (make-predicate-formula
;; 				     (make-idpredconst "Real" '() '()) trhs)
;; 				    "into the context, using assert"))))
;; 		    ((formula=? (make-predicate-formula
;; 				 (make-idpredconst "RealEq" '() '())
;; 				 trhs tlhs)
;; 				(proof-to-formula eq-proof))
;; 		     eq-proof)
;; 		    ((formula=? (make-predicate-formula
;; 				 (make-idpredconst "RealEq" '() '())
;; 				 trhs tlhs)
;; 				(proof-to-formula eq-rev-proof))
;; 		     eq-rev-proof)
;; 		    (else (realeq-term-compat
;; 			   (car args) var term2 term1 eq-rev-proof context))))
;; 		  (proof2 ;of srhs===slhs
;; 		   (cond
;; 		    ((term=? srhs slhs)
;; 		     (let ((realproof-or-f
;; 			    (context-and-term-to-realproof context srhs)))
;; 		       (if realproof-or-f
;; 			   (mk-proof-in-elim-form
;; 			    (make-proof-in-aconst-form
;; 			     (theorem-name-to-aconst "RealEqRefl"))
;; 			    srhs realproof-or-f)
;; 			   (myerror "realeq-formula-compat" "First put"
;; 				    (make-predicate-formula
;; 				     (make-idpredconst "Real" '() '()) srhs)
;; 				    "in the context, using assert"))))
;; 		    ((formula=? (make-predicate-formula
;; 				 (make-idpredconst "RealEq" '() '())
;; 				 srhs slhs)
;; 				(proof-to-formula eq-proof))
;; 		     eq-proof)
;; 		    ((formula=? (make-predicate-formula
;; 				 (make-idpredconst "RealEq" '() '())
;; 				 srhs slhs)
;; 				(proof-to-formula eq-rev-proof))
;; 		     eq-rev-proof)
;; 		    (else (realeq-term-compat
;; 			   (cadr args) var term2 term1 eq-rev-proof context)))))
;; 	     (mk-proof-in-elim-form
;; 	      (make-proof-in-aconst-form aconst)
;; 	      trhs tlhs srhs slhs proof1 proof2 new-goal)))
;; 	  (else (myerror "realeq-formula-compat" "arity 1 or 2 expected"
;; 	 		 name))))
;;        (myerror "realeq-formula-compat" "idpredconst expected" fla))))
;;    (else (myerror "realeq-formula-compat" "not implemented for formula" fla))))

(define (simpreal opt-dir-or-x . x-and-xs-or-xs)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing"))))
	 (simpreal-result
	  (apply simpreal-intern
		 num-goals proof maxgoal opt-dir-or-x x-and-xs-or-xs)))
    (if (not simpreal-result)
	(begin (display-comment "no simplification possible")
	       (if COMMENT-FLAG (newline)))
	(begin
	  (set! PPROOF-STATE simpreal-result)
	  (pproof-state-history-push PPROOF-STATE)
	  (display-new-goals num-goals number)))))

(define (simpreal-intern num-goals proof
			 maxgoal . opt-dir-and-x-and-elab-path-and-terms)
  (let* ((opt-dir (if (null? opt-dir-and-x-and-elab-path-and-terms)
		      (myerror "simpreal-intern" "more arguments expected")
		      (car opt-dir-and-x-and-elab-path-and-terms)))
	 (left-to-right (not (and (string? opt-dir) (string=? "<-" opt-dir))))
	 (x-and-elab-path-and-terms
	  (if left-to-right
	      opt-dir-and-x-and-elab-path-and-terms
	      (cdr opt-dir-and-x-and-elab-path-and-terms)))
	 (x (if (null? x-and-elab-path-and-terms)
		(myerror "simpreal-intern" "more arguments expected")
		(car x-and-elab-path-and-terms)))
	 (elab-path-and-terms (cdr x-and-elab-path-and-terms))
	 (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (avars (context-to-avars context))
	 (maxhyp (length avars))
	 (goal-formula (goal-to-formula goal))
	 (leaf (if (formula-form? x)
		   (context-and-ncvars-and-formula-to-new-goal
		    context ncvars x)
		   (hyp-info-to-leaf num-goal x)))
	 (used-formula
	  (unfold-formula (if (formula-form? x) x (proof-to-formula leaf))))
	 (sig-vars (context-to-vars context))
	 (sig-tvars-and-sig-vars
	  (if (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS))
	      sig-vars
	      (append (formula-to-tvars used-formula) sig-vars)))
	 (elab-path (do ((l elab-path-and-terms (cdr l))
			 (res '() (if (memq (car l) '(left right))
				      (cons (car l) res)
				      res)))
			((null? l) (reverse res))))
	 (xs-and-vars-and-toinst1
	  (apply
	   fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
	   used-formula sig-tvars-and-sig-vars
	   goal-formula left-to-right
	   elab-path))
	 (xs-and-vars-and-toinst
	  (if xs-and-vars-and-toinst1
	      xs-and-vars-and-toinst1
	      (apply
	       fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
	       (normalize-formula used-formula)
	       sig-tvars-and-sig-vars
	       (normalize-formula goal-formula)
	       left-to-right
	       elab-path))))
    (if
     (not xs-and-vars-and-toinst)
     #f
     (let* ((xs (car xs-and-vars-and-toinst))
	    (vars (cadr xs-and-vars-and-toinst))
	    (toinst (caddr xs-and-vars-and-toinst))
	    (terms (do ((l elab-path-and-terms (cdr l))
			(res '() (if (memq (car l) '(left right))
				     res
				     (cons (car l) res))))
		       ((null? l) (reverse res))))
	    (subst (if (<= (length vars) (length terms))
		       (map list vars (list-head terms (length vars)))
		       empty-subst))
	    (subst-xs (map (lambda (x) (if (term-form? x)
					   (term-substitute x subst)
					   x))
			   xs))
	    (types (let ((info1 (assoc x THEOREMS))
			 (info2 (assoc x GLOBAL-ASSUMPTIONS))
			 (tsubst (list-transform-positive toinst
				   (lambda (x) (tvar-form? (car x))))))
		     (if
		      (and (or info1 info2) (pair? tsubst)) ;else '()
		      (let* ((aconst (if info1
					 (theorem-name-to-aconst x)
					 (global-assumption-name-to-aconst x)))
			     (fla (aconst-to-formula aconst))
			     (tvars (formula-to-tvars fla)))
			(map (lambda (tvar) (type-substitute tvar tsubst))
			     tvars))
		      '()))))
       (if (> (length vars) (length terms))
	   (apply myerror
		  "simpreal-intern" "more terms expected, to be substituted for"
		  (list-tail vars (length terms))))
       (if (and COMMENT-FLAG (< (length vars) (length terms)))
	   (begin
	     (comment "warning: superfluous terms")
	     (for-each comment
		       (map term-to-string (list-tail terms (length vars))))))
       (apply simpreal-with-intern
	      (if left-to-right
		  (append (list num-goals proof maxgoal x)
			  (append types subst-xs))
		  (append (list num-goals proof maxgoal "<-" x)
			  (append types subst-xs))))))))

;; Let alleq-fla be all n lhs(n)===rhs(n).
;; term-and-alleq-fla-to-first-sumeq-fla-or-f added searches for the
;; first occurrence of RealSum t1 t2([n]t(lhs(n))) in term and returns
;; the sumeq-formula RealSum t1 t2([n]t(lhs(n)))===RealSum t1
;; t2([n]t(rhs(n))).  In case no such occurrence is found #f is returned.

(define (term-and-alleq-fla-to-first-sumeq-fla-or-f term alleq-fla)
  (if
   (not (term-in-app-form? term)) #f
   (let ((op (term-in-app-form-to-op term))
	 (arg (term-in-app-form-to-arg term))
	 (binary-names (list "RealPlus" "RealTimes" "RealMax" "RealMin")))
     (if
      (member (all-allnc-form-to-var alleq-fla) (term-to-free term)) ;rename
      (let* ((n (var-to-new-var (all-allnc-form-to-var alleq-fla)))
	     (eq-fla (term-subst (all-allnc-form-to-kernel alleq-fla)
				 (all-allnc-form-to-var alleq-fla)
				 (make-term-in-var-form n))))
	(term-and-alleq-fla-to-first-sumeq-fla-or-f term (make-all n eq-fla)))
      (let* ((n (all-allnc-form-to-var alleq-fla))
	     (eq-fla (imp-impnc-all-allnc-form-to-final-conclusion alleq-fla))
	     ;; (eq-fla (all-allnc-form-to-kernel alleq-fla))
	     (lhs-and-rhs (eq-formula-to-lhs-and-rhs eq-fla))
	     (lhs (car lhs-and-rhs))
	     (rhs (cadr lhs-and-rhs)))
	(cond
	 ((and (term-in-const-form? op)
	       (string=? "RealUMinus" (const-to-name
				       (term-in-const-form-to-const op))))
	  (term-and-alleq-fla-to-first-sumeq-fla-or-f arg alleq-fla))
	 ((and (term-in-app-form? op)
	       (term-in-const-form? (term-in-app-form-to-op op)))
	  (cond
	   ((member (const-to-name (term-in-const-form-to-const
				    (term-in-app-form-to-op op))) binary-names)
	    (let* ((oparg (term-in-app-form-to-arg op))
		   (prev1 (term-and-alleq-fla-to-first-sumeq-fla-or-f
			   oparg alleq-fla)))
	      (if prev1 prev1
		  (term-and-alleq-fla-to-first-sumeq-fla-or-f arg alleq-fla))))
	   ((string=? "RealExp" (const-to-name (term-in-const-form-to-const
						(term-in-app-form-to-op op))))
	    (let ((oparg (term-in-app-form-to-arg op)))
	      (term-and-alleq-fla-to-first-sumeq-fla-or-f oparg alleq-fla)))
	   (else #f)))
	 ((and (term-in-app-form? op)
	       (term-in-app-form? (term-in-app-form-to-op op)))
	  (let* ((final-op (term-in-app-form-to-op (term-in-app-form-to-op op)))
		 (n1 (term-in-app-form-to-arg (term-in-app-form-to-op op)))
		 (n2 (term-in-app-form-to-arg op)))
	    (if
	     (and (term-in-const-form? final-op)
		  (string=? "RealSum" (const-to-name
				       (term-in-const-form-to-const final-op)))
		  (term-in-abst-form? arg))
	     (let* ((var (term-in-abst-form-to-var arg))
		    (kernel (term-in-abst-form-to-kernel arg))
		    (rseq-arg
		     (if (equal? n var) arg ;else rename with n
			 (make-term-in-abst-form
			  n (term-subst kernel var (make-term-in-var-form n)))))
		    (rseq-kernel (term-in-abst-form-to-kernel rseq-arg))
		    (x (type-to-new-var (term-to-type lhs)))
		    ;; (x (type-to-new-var (py "rea")))
		    (decomp-or-f ;t(x) such that t(lhs) is rseq-kernel, n in lhs
		     (term-and-var-and-subterm-to-first-decomp-or-f
		      rseq-kernel x lhs)))
	       (if
		decomp-or-f ;return sumeq-fla
		(let* ((lkernel	(term-subst decomp-or-f x lhs)) ;t(lhs)
		       (rkernel	(term-subst decomp-or-f x rhs)) ;t(rhs)
		       (lterm (make-term-in-abst-form n lkernel)) ;[n]t(lhs)
		       (rterm (make-term-in-abst-form n rkernel)) ;[n]t(rhs)
		       (lsum (mk-term-in-app-form (pt "RealSum") n1 n2 lterm))
		       (rsum (mk-term-in-app-form (pt "RealSum") n1 n2 rterm)))
		  (make-predicate-formula
		   '(idpredconst "RealEq" () ()) lsum rsum))
		#f))
	     #f)))
	 (else #f)))))))

;; Test
;; (define alleq-fla (pf "all n x**n*y===y*x**n"))
;; (define term (pt "RealSum n1 n2([n]z+x**n*y)"))
;; (pp (term-and-alleq-fla-to-first-sumeq-fla-or-f term alleq-fla))
;; (define term (pt "~(RealSum n1 n2([n]z+x**n*y))"))
;; (pp (term-and-alleq-fla-to-first-sumeq-fla-or-f term alleq-fla)) ;ok
;; (define term (pt "RealExp(RealSum n1 n2([n]z+x**n*y))(Succ(Succ Zero))"))
;; (pp (term-and-alleq-fla-to-first-sumeq-fla-or-f term alleq-fla)) ;ok
;; (pp term)

;; simprsum calls simpreal-with with a sumeq-fla
;; RealSum t1 t2([n]t(lhs(n)))===RealSum t1 t2([n]t(rhs(n))) obtained by
;; term-and-alleq-fla-to-first-sumeq-fla-or-f

(define (simprsum opt-dir-or-alleq-fla . alleq-fla-and-xs-or-xs)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (goal-formula (goal-to-formula goal))
	 (terms (if (predicate-form? goal-formula)
		    (predicate-form-to-args goal-formula)
		    (myerror "simprsum"
			     "predicate form expected" goal-formula)))
	 (left-to-right (formula-form? opt-dir-or-alleq-fla))
	 (alleq-fla (if left-to-right
			opt-dir-or-alleq-fla
			(car alleq-fla-and-xs-or-xs)))
	 (xs (if left-to-right
		 alleq-fla-and-xs-or-xs
		 (cdr alleq-fla-and-xs-or-xs)))
	 (sumeq-fla-or-f
	  (cond
	   ((= 2 (length terms))
	    (let ((prev1 (term-and-alleq-fla-to-first-sumeq-fla-or-f
			  (car terms) alleq-fla)))
	      (if prev1 prev1
		  (term-and-alleq-fla-to-first-sumeq-fla-or-f
		   (cadr terms) alleq-fla))))
	   ((= 1 (length terms))
	    (term-and-alleq-fla-to-first-sumeq-fla-or-f (car terms) alleq-fla))
	   (else (myerror "simprsum" "unary or binary predicate form expected"
			  goal-formula)))))
    (if sumeq-fla-or-f
	(let* ((opt-dir-or-sumeq-fla (if left-to-right sumeq-fla-or-f "<-"))
	       (sumeq-fla-and-xs-or-xs
		(if left-to-right xs (cons sumeq-fla xs))))
	  (apply simpreal-with
		 (cons opt-dir-or-sumeq-fla sumeq-fla-and-xs-or-xs)))
	(myerror "simprsum" "simplification not possible"))))

;; ;; Test
;; (set-goal "all x,y(Real x -> Real y -> 
;;  RealSum Zero(Succ Zero)([n]x**n*y)===y+y*x)")
;; (assume "x" "y" "Rx" "Ry")
;; (simprsum (pf "all n x**n*y===y*x**n"))
;; (ng #t)
;; (simpreal "RealOneTimes")
;; (simpreal "RealTimesOne")
;; (use "RealEqRefl")
;; (autoreal)
;; ;; 4
;; (use "RealSumCompat")
;; (ng #t)
;; (assume "l" "Useless1" "Useless2")
;; (use "RealTimesComm")
;; (autoreal)
;; ;; Proof finished.
;; (cdp)

;; It is convenient to automate (the easy cases of an) interactive
;; proof development by iterating \texttt{realproof} as long as it is
;; successful in finding a proof.  Then the first goal where it failed
;; is presented as the new goal.

(define (autoreal)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (autoreal-result (autoreal-intern num-goals proof maxgoal)))
    (set! PPROOF-STATE autoreal-result)
    (pproof-state-history-push PPROOF-STATE)
    (if
     COMMENT-FLAG
     (if (null? (pproof-state-to-num-goals))
	 (begin (display-comment "Proof finished.") (newline))
	 (begin (display-comment "  The active goal now is") (newline)
		(display-num-goal (car (pproof-state-to-num-goals))))))))

(define (autoreal-intern num-goals proof maxgoal)
  (do ((prev-res (list num-goals proof maxgoal) res)
       (res (realproof-intern num-goals proof maxgoal)
	    (apply realproof-intern res)))
      ((or (not res)
	   (null? (pproof-state-to-num-goals res))
					;or realproof not applicable
	   (let* ((num-goals (car res))
		  (num-goal
		   (if (pair? num-goals) (car num-goals)
		       (myerror "goal missing")))
		  (goal (num-goal-to-goal num-goal))
		  (formula (goal-to-formula goal)))
	     (not (and (predicate-form? formula)
		       (let ((pred (predicate-form-to-predicate formula)))
			 (and (idpredconst-form? pred)
			      (string=? "Real" (idpredconst-to-name pred))))))))
       (display-comment)
       (if (not res)
	   prev-res
	   res))))

;; fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data is #f if
;; (a) no atomic or negated atomic head of formula and also (b) no lhs
;; (resp. rhs) of an equality head of formula is a pattern in the goal
;; formula.  Otherwise the following data are returned: (1) the
;; arguments xs for the hypothesis x that produce the instance, (2)
;; vars (from xs) whose instantiations cannot be inferred, hence need
;; to be provided, (3) a tosubst that produces the instance.

(define (fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
	 used-formula sig-tvars-and-sig-vars goal-formula
	 left-to-right . opt-eq-pvars-and-elab-path)
  (let* ((eq-pvars (list-transform-positive opt-eq-pvars-and-elab-path
		     (lambda (x) (pvar-form? x))))
	 (elab-path (list-transform-positive opt-eq-pvars-and-elab-path
		      (lambda (x) (not (pvar-form? x)))))
	 (match-res
	  (cond
	   ((imp-form? used-formula)
	    (let ((prem (imp-form-to-premise used-formula))
		  (concl (imp-form-to-conclusion used-formula)))
	      (and (atom-form? prem)
		   (classical-formula=? falsity concl)
		   (let ((kernel (atom-form-to-kernel prem)))
		     (first-match sig-tvars-and-sig-vars
				  kernel goal-formula)))))
	   ((impnc-form? used-formula)
	    (let ((prem (impnc-form-to-premise used-formula))
		  (concl (impnc-form-to-conclusion used-formula)))
	      (and (atom-form? prem)
		   (classical-formula=? falsity concl)
		   (let ((kernel (atom-form-to-kernel prem)))
		     (first-match sig-tvars-and-sig-vars
				  kernel goal-formula)))))
	   ((atom-form? used-formula)
	    (let* ((kernel (atom-form-to-kernel used-formula))
		   (op (term-in-app-form-to-final-op kernel))
		   (res (first-match sig-tvars-and-sig-vars
				     kernel goal-formula)))
	      (if res res
		  (if (and (term-in-const-form? op)
			   (member (const-to-name
				    (term-in-const-form-to-const op))
				   (list "=" "RatEqv")))
		      (let* ((args (term-in-app-form-to-args kernel))
			     (lhs (car args))
			     (rhs (cadr args)))
			(if left-to-right
			    (first-match sig-tvars-and-sig-vars
					 lhs goal-formula)
			    (first-match sig-tvars-and-sig-vars
					 rhs goal-formula)))
		      #f))))
	   ((predicate-form? used-formula)
	    (let ((predicate (predicate-form-to-predicate used-formula)))
	      (cond
	       ((idpredconst-form? predicate)
		(if (member (idpredconst-to-name predicate)
			    (list "EqD" "RealEq"))
		    (let* ((args (predicate-form-to-args used-formula))
			   (lhs (car args))
			   (rhs (cadr args)))
		      (if left-to-right
			  (first-match sig-tvars-and-sig-vars
				       lhs goal-formula)
			  (first-match sig-tvars-and-sig-vars
				       rhs goal-formula)))
		    #f))
	       ((pvar-form? predicate)
		(if (member predicate eq-pvars)
		    (let* ((args (predicate-form-to-args used-formula))
			   (lhs (car args))
			   (rhs (cadr args)))
		      (if left-to-right
			  (first-match sig-tvars-and-sig-vars
				       lhs goal-formula)
			  (first-match sig-tvars-and-sig-vars
				       rhs goal-formula)))
		    #f))
	       (else #f))))
	   (else #f))))
    (if
     match-res
     (list '() '() match-res)
     (cond
      ((atom-form? used-formula) #f)
      ((ex-form? used-formula) #f)
      ((imp-form? used-formula)
       (let* ((concl (imp-form-to-conclusion used-formula))
	      (prev
	       (apply
		fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
		concl sig-tvars-and-sig-vars
		goal-formula left-to-right
		opt-eq-pvars-and-elab-path)))
	 (if (not prev)
	     #f
	     (let* ((xs (car prev))
		    (vars (cadr prev))
		    (toinst (caddr prev)))
	       (list (cons DEFAULT-GOAL-NAME xs) vars toinst)))))
      ((impnc-form? used-formula)
       (let* ((concl (impnc-form-to-conclusion used-formula))
	      (prev
	       (apply
		fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
		concl sig-tvars-and-sig-vars
		goal-formula left-to-right
		opt-eq-pvars-and-elab-path)))
	 (if (not prev)
	     #f
	     (let* ((xs (car prev))
		    (vars (cadr prev))
		    (toinst (caddr prev)))
	       (list (cons DEFAULT-GOAL-NAME xs) vars toinst)))))
      ((all-form? used-formula)
       (let* ((var (all-form-to-var used-formula))
	      (kernel (all-form-to-kernel used-formula))
	      (new-var (var-to-new-var var))
	      (new-kernel
	       (formula-subst kernel var (make-term-in-var-form new-var)))
	      (prev
	       (apply
		fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
		new-kernel sig-tvars-and-sig-vars
		goal-formula left-to-right
		opt-eq-pvars-and-elab-path)))
	 (if (not prev)
	     #f
	     (let* ((xs (car prev))
		    (vars (cadr prev))
		    (toinst (caddr prev))
		    (info (assoc new-var toinst)))
	       (if
		info ;instance found by matching
		(list ;insert instance into xs
		 (cons (cadr info) xs) vars toinst)
		(list ;else insert new-var into xs, and new-var to vars
		 (cons (make-term-in-var-form new-var) xs)
		 (cons new-var vars)
		 toinst))))))
      ((allnc-form? used-formula)
       (let* ((var (allnc-form-to-var used-formula))
	      (kernel (allnc-form-to-kernel used-formula))
	      (new-var (var-to-new-var var))
	      (new-kernel
	       (formula-subst kernel var (make-term-in-var-form new-var)))
	      (prev
	       (apply
		fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
		new-kernel sig-tvars-and-sig-vars
		goal-formula left-to-right
		opt-eq-pvars-and-elab-path)))
	 (if (not prev)
	     #f
	     (let* ((xs (car prev))
		    (vars (cadr prev))
		    (toinst (caddr prev))
		    (info (assoc new-var toinst)))
	       (if
		info ;instance found by matching
		(list ;insert instance into xs
		 (cons (cadr info) xs) vars toinst)
		(list ;else insert new-var into xs, and new-var to vars
		 (cons (make-term-in-var-form new-var) xs)
		 (cons new-var vars)
		 toinst))))))
      ((or (and-form? used-formula)
	   (andd-form? used-formula)
	   (andl-form? used-formula)
	   (andr-form? used-formula)
	   (andnc-form? used-formula))
       (let ((left-conjunct (bicon-form-to-left used-formula))
	     (right-conjunct (bicon-form-to-right used-formula)))
	 (if
	  (pair? elab-path)
	  (let* ((direction (car elab-path))
		 (conjunct (cond ((eq? 'left direction) left-conjunct)
				 ((eq? 'right direction) right-conjunct)
				 (else (myerror "left or right expected"
						direction))))
		 (prev
		  (apply
		   fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
		   conjunct sig-tvars-and-sig-vars
		   goal-formula left-to-right
		   (append eq-pvars (cdr elab-path)))))
	    (if (not prev)
		#f
		(let* ((xs (car prev))
		       (vars (cadr prev))
		       (toinst (caddr prev)))
		  (list (cons direction xs) vars toinst))))
	  (let ((prev1
		 (fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
		  left-conjunct sig-tvars-and-sig-vars
		  goal-formula left-to-right)))
	    (if
	     prev1
	     (let* ((xs (car prev1))
		    (vars (cadr prev1))
		    (toinst (caddr prev1)))
	       (list (cons 'left xs) vars toinst))
	     (let ((prev2
		    (fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
		     right-conjunct sig-tvars-and-sig-vars
		     goal-formula left-to-right)))
	       (if prev2
		   (let* ((xs (car prev2))
			  (vars (cadr prev2))
			  (toinst (caddr prev2)))
		     (list (cons 'right xs) vars toinst))
		   #f)))))))
      ((predicate-form? used-formula) #f)
      (else (myerror
	     "fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data"
	     "formula expected"
	     used-formula))))))

(define (compat-at all-formula)
  (let* ((var1 (all-form-to-var all-formula))
	 (varterm1 (make-term-in-var-form var1))
	 (kernel (all-form-to-kernel all-formula))
	 (free (formula-to-free all-formula))
	 (type-of-var (var-to-type var1))
	 (type-of-var-is-finalg? (finalg? type-of-var))
	 (type (if type-of-var-is-finalg? type-of-var
		   (myerror "compat-at" "finitary algebra expected"
			    type-of-var)))
	 (var2 (if (t-deg-one? (var-to-t-deg var1))
		   (var-to-new-var var1)
		   (myerror "compat-at" "total variable expected" varterm1)))
	 (varterm2 (make-term-in-var-form var2))
	 (new-var (var-to-new-partial-var var1))
	 (new-kernel
	  (formula-subst kernel var1 (make-term-in-var-form new-var)))
	 (cterm (make-cterm new-var new-kernel))
	 (eqd-compat-aconst (theorem-name-to-aconst "EqDCompat"))
	 (uninst-formula (aconst-to-uninst-formula eqd-compat-aconst))
	 (tvar (var-to-type (allnc-form-to-var uninst-formula)))
	 (final-conclusion
	  (imp-impnc-all-allnc-form-to-final-conclusion uninst-formula))
	 (pvar (predicate-form-to-predicate final-conclusion))
	 (tsubst (make-subst tvar type))
	 (psubst (make-subst-wrt pvar-cterm-equal? pvar cterm))
	 (inst-eqd-compat-aconst
	  (make-aconst (aconst-to-name eqd-compat-aconst) ;"EqDCompat"
		       (aconst-to-kind eqd-compat-aconst) ;'theorem
		       uninst-formula
		       (append tsubst psubst)))
	 (=-to-eqd-aconst (finalg-to-=-to-eqd-aconst type))
	 (avar (formula-to-new-avar (make-= varterm1 varterm2)))
	 (elim-proof ;of n eqd m
	  (mk-proof-in-elim-form
	   (make-proof-in-aconst-form =-to-eqd-aconst)
	   varterm1 varterm2 (make-proof-in-avar-form avar))))
    (mk-proof-in-nc-intro-form
     var1 var2 avar
     (apply mk-proof-in-elim-form
	    (make-proof-in-aconst-form inst-eqd-compat-aconst)
	    (append (map make-term-in-var-form free)
		    (list varterm1 varterm2 elim-proof))))))

(define (compat-rev-at all-formula)
  (let* ((var1 (all-form-to-var all-formula))
	 (varterm1 (make-term-in-var-form var1))
	 (kernel (all-form-to-kernel all-formula))
	 (free (formula-to-free all-formula))
	 (type-of-var (var-to-type var1))
	 (type-of-var-is-finalg? (finalg? type-of-var))
	 (type (if type-of-var-is-finalg? type-of-var
		   (myerror "compat-at" "finitary algebra expected"
			    type-of-var)))
	 (var2 (if (t-deg-one? (var-to-t-deg var1))
		   (var-to-new-var var1)
		   (myerror "compat-at" "total variable expected" varterm1)))
	 (varterm2 (make-term-in-var-form var2))
	 (new-var (var-to-new-partial-var var1))
	 (new-kernel
	  (formula-subst kernel var1 (make-term-in-var-form new-var)))
	 (cterm (make-cterm new-var new-kernel))
	 (eqd-compat-aconst (theorem-name-to-aconst "EqDCompatRev"))
	 (uninst-formula (aconst-to-uninst-formula eqd-compat-aconst))
	 (tvar (var-to-type (allnc-form-to-var uninst-formula)))
	 (final-conclusion
	  (imp-impnc-all-allnc-form-to-final-conclusion uninst-formula))
	 (pvar (predicate-form-to-predicate final-conclusion))
	 (tsubst (make-subst tvar type))
	 (psubst (make-subst-wrt pvar-cterm-equal? pvar cterm))
	 (inst-eqd-compat-rev-aconst
	  (make-aconst (aconst-to-name eqd-compat-aconst) ;"EqDCompatRev"
		       (aconst-to-kind eqd-compat-aconst) ;'theorem
		       uninst-formula
		       (append tsubst psubst)))
	 (=-to-eqd-aconst (finalg-to-=-to-eqd-aconst type))
	 (avar (formula-to-new-avar (make-= varterm1 varterm2)))
	 (elim-proof ;of n eqd m
	  (mk-proof-in-elim-form
	   (make-proof-in-aconst-form =-to-eqd-aconst)
	   varterm1 varterm2 (make-proof-in-avar-form avar))))
    (mk-proof-in-nc-intro-form
     var1 var2 avar
     (apply mk-proof-in-elim-form
	    (make-proof-in-aconst-form inst-eqd-compat-rev-aconst)
	    (append (map make-term-in-var-form free)
		    (list varterm1 varterm2 elim-proof))))))

(define (finalg-to-string finalg)
  (let* ((alg-name (alg-form-to-name finalg))
	 (char-list (string->list alg-name))
	 (capitalized-alg-name
	  (list->string (cons (char-upcase (car char-list)) (cdr char-list))))
	 (types (alg-form-to-types finalg))
	 (capitalized-type-names (map finalg-to-string types)))
    (apply string-append capitalized-alg-name capitalized-type-names)))

;; (finalg-to-string (py "list nat")) ;ListNat

(define (finalg-to-=-to-eqd-aconst finalg)
  (if (not (finalg? finalg))
      (myerror "finalg-to-=-to-eqd-aconst" "finitary algebra expected" finalg))
  (let* ((string (finalg-to-string finalg))
	 (name (string-append string "EqToEqD")) ;e.g. ListNatEqToEqD
	 (info (assoc name THEOREMS)))
    (if info
	(cadr info) ;i.e., (theorem-name-to-aconst name)
	(let* ((var1 (type-to-new-var finalg))
	       (varterm1 (make-term-in-var-form var1))
	       (var2 (type-to-new-var finalg))
	       (varterm2 (make-term-in-var-form var2))
	       (formula
		(mk-all var1 var2 (make-imp (make-= varterm1 varterm2)
					    (make-eqd varterm1 varterm2)))))
	  (comment "warning: theorem " name " missing.")
	  (add-global-assumption name formula)
	  (global-assumption-name-to-aconst name)))))

(define (eqd-compat-at all-formula)
  (let* ((var (all-form-to-var all-formula))
	 (kernel (all-form-to-kernel all-formula))
	 (type (var-to-type var))
	 (partial? (t-deg-zero? (var-to-t-deg var)))
	 (new-var (if partial? var (var-to-new-partial-var var)))
	 (new-kernel
	  (if partial? kernel
	      (formula-subst kernel var (make-term-in-var-form new-var))))
	 (cterm (make-cterm new-var new-kernel))
	 (aconst (theorem-name-to-aconst "EqDCompat"))
	 (uninst-formula (aconst-to-uninst-formula aconst))
	 (tvar (var-to-type (allnc-form-to-var uninst-formula)))
	 (final-conclusion
	  (imp-impnc-all-allnc-form-to-final-conclusion uninst-formula))
	 (pvar (predicate-form-to-predicate final-conclusion))
	 (tsubst (make-subst tvar type))
	 (psubst (make-subst-wrt pvar-cterm-equal? pvar cterm))
	 (free (formula-to-free all-formula)))
    (apply mk-proof-in-elim-form
	   (make-proof-in-aconst-form
	    (make-aconst (aconst-to-name aconst) ;"EqDCompat"
			 (aconst-to-kind aconst) ;'theorem
			 uninst-formula
			 (append tsubst psubst)))
	   (map make-term-in-var-form free))))

(define (eqd-compat-rev-at all-formula)
  (let* ((var (all-form-to-var all-formula))
	 (kernel (all-form-to-kernel all-formula))
	 (type (var-to-type var))
	 (partial? (t-deg-zero? (var-to-t-deg var)))
	 (new-var (if partial? var (var-to-new-partial-var var)))
	 (new-kernel
	  (if partial? kernel
	      (formula-subst kernel var (make-term-in-var-form new-var))))
	 (cterm (make-cterm new-var new-kernel))
	 (aconst (theorem-name-to-aconst "EqDCompatRev"))
	 (uninst-formula (aconst-to-uninst-formula aconst))
	 (tvar (var-to-type (allnc-form-to-var uninst-formula)))
	 (final-conclusion
	  (imp-impnc-all-allnc-form-to-final-conclusion uninst-formula))
	 (pvar (predicate-form-to-predicate final-conclusion))
	 (tsubst (make-subst tvar type))
	 (psubst (make-subst-wrt pvar-cterm-equal? pvar cterm))
	 (free (formula-to-free all-formula)))
    (apply mk-proof-in-elim-form
	   (make-proof-in-aconst-form
	    (make-aconst (aconst-to-name aconst) ;"EqDCompatRev"
			 (aconst-to-kind aconst) ;'theorem
			 uninst-formula
			 (append tsubst psubst)))
	   (map make-term-in-var-form free))))

;; simphyp-with does for forward chaining the same as simp-with for
;; backward chaining.  It replaces the present goal by a new one, with
;; one additional hypothesis obtained by simplifying a previous one.
;; Notice that this effect could also be obtained by cut or assert.  In
;; the definition below of simphyp-with hyp is one of the following.
;; - A number or string identifying a hypothesis form the context.
;; - The name of a theorem or global assumption, but not one whose final
;;   conclusion is a predicate variable.
;; - A closed proof.
;; - A formula with free variables from the context, generating a new goal.
;; Moreover xs is a list consisting of
;; - a number or string identifying a hypothesis form the context,
;; - the name of a theorem or global assumption,
;; - a closed proof,
;; - the string "?" (value of DEFAULT-GOAL-NAME), generating a new goal,
;; - a symbol left or right,
;; - a term, whose free variables are added to the context,
;; - a type, which is substituted for the 1st tvar,
;; - a comprehension term, which is substituted for the 1st pvar.

;; This generates a used formula, which is to be an atom, a negated
;; atom or (lhs eqd rhs).  If it as a (negated)
;; atom, check whether the kernel or its normal form is present in the
;; hyp.  If so, replace it by True (False).  If it is an equality (lhs
;; = rhs) or (lhs eqd rhs) with lhs or its normal
;; form present in the hyp, replace lhs by rhs.  In case "<-" exchange
;; lhs by rhs.

(define (simphyp-with hyp opt-dir . rest)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply simphyp-with-intern
		 num-goals proof maxgoal hyp opt-dir rest))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (simphyp-with-intern num-goals proof maxgoal hyp . opt-dir-and-xs)
  (let* ((opt-dir (if (null? opt-dir-and-xs)
		      (myerror "simphyp-with-intern" "more arguments expected")
		      (car opt-dir-and-xs)))
	 (left-to-right (not (and (string? opt-dir) (string=? "<-" opt-dir))))
	 (x-and-x-list (if left-to-right
			   opt-dir-and-xs
			   (cdr opt-dir-and-xs)))
	 (x (if (null? x-and-x-list)
		(myerror "simphyp-with-intern" "more arguments expected")
		(car x-and-x-list)))
	 (x-list (cdr x-and-x-list))
	 (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (leaf (if (formula-form? hyp)
		   (context-and-ncvars-and-formula-to-new-goal
		    context ncvars hyp)
		   (hyp-info-to-leaf num-goal hyp)))
	 (new-num-goals-hyp
	  (if (formula-form? hyp) ;then a new goal is created
	      (list (make-num-goal (+ 1 maxgoal) leaf drop-info hypname-info
				   (or ignore-deco-flag
				       (formula-of-nulltype? hyp))))
	      '()))
	 (new-maxgoal-hyp (if (formula-form? hyp) (+ 1 maxgoal) maxgoal))
	 (proof-and-new-num-goals-and-maxgoal
	  (if (and (string? x)
		   (let ((info (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS))))
		     (and info
			  (let* ((aconst (cadr info))
				 (aconst-formula (aconst-to-formula aconst))
				 (final-concl
				  (imp-impnc-all-allnc-form-to-final-conclusion
				   aconst-formula)))
			    (and (predicate-form? final-concl)
				 (pvar? (predicate-form-to-predicate
					 final-concl)))))))
	      (myerror "simphyp-with-intern" "unexpected aconst name" x)
	      (apply x-and-x-list-to-proof-and-new-num-goals-and-maxgoal
		     num-goal (+ 1 new-maxgoal-hyp) x x-list)))
	 (negatom-or-eq-proof (car proof-and-new-num-goals-and-maxgoal))
	 (new-num-goals (append new-num-goals-hyp
				(cadr proof-and-new-num-goals-and-maxgoal)))
	 (new-maxgoal (caddr proof-and-new-num-goals-and-maxgoal))
	 (goal-formula (goal-to-formula goal))
	 (leaf-formula (proof-to-formula leaf))
	 (used-formula (proof-to-formula negatom-or-eq-proof))
	 (used-prime-formula
	  (cond ((prime-form? used-formula) used-formula)
		((and (imp-impnc-form? used-formula)
		      (atom-form? (imp-impnc-form-to-premise used-formula))
		      (classical-formula=?
		       falsity (imp-impnc-form-to-conclusion used-formula)))
		 (imp-form-to-premise used-formula))
		(else (myerror "simphyp-with-intern"
			       "negated atom or prime formula expected"
			       used-formula))))
	 (used-nprime-formula (normalize-formula used-prime-formula))
	 (bvar (type-to-new-var (make-alg "boole")))
	 (bvarterm (make-term-in-var-form bvar))
	 (used-kernel (if (atom-form? used-prime-formula)
			  (atom-form-to-kernel used-prime-formula)
			  bvarterm)) ;anything would do
	 (used-nkernel (nt used-kernel))
	 (op (term-in-app-form-to-final-op used-kernel))
	 (nop (term-in-app-form-to-final-op used-nkernel))
	 (leaf-formula-without-kernel
	  (if (atom-form? used-prime-formula)
	      (formula-gen-subst leaf-formula used-kernel bvarterm)
	      leaf-formula))
	 (nleaf-formula-without-nkernel
	  (if (atom-form? used-prime-formula)
	      (formula-gen-subst (nf leaf-formula) used-nkernel bvarterm)
	      leaf-formula))
	 (kernel-present? (not (classical-formula=?
				leaf-formula-without-kernel
				leaf-formula)))
	 (nkernel-present? (not (classical-formula=?
				 nleaf-formula-without-nkernel
				 leaf-formula))))
    (cond
     ((and kernel-present?
	   (not (term=? used-kernel (make-term-in-const-form true-const)))
	   (not (term=? used-kernel (make-term-in-const-form false-const)))
	   (or (atom-form? used-formula) (synt-total? used-kernel)))
      (simphyp-with-kernel-aux
       num-goals proof maxgoal negatom-or-eq-proof new-num-goals new-maxgoal
       used-kernel bvar leaf-formula-without-kernel leaf))
     ((and nkernel-present?
	   (not (term=? used-nkernel (make-term-in-const-form true-const)))
	   (not (term=? used-nkernel (make-term-in-const-form false-const)))
	   (or (atom-form? used-formula) (synt-total? used-nkernel)))
      (simphyp-with-kernel-aux
       num-goals proof maxgoal negatom-or-eq-proof new-num-goals new-maxgoal
       used-nkernel bvar nleaf-formula-without-nkernel leaf))
     ((and (prime-form? used-formula)
	   (term-in-const-form? op)
	   (string=? "=" (const-to-name (term-in-const-form-to-const op)))
	   (let* ((args (term-in-app-form-to-args used-kernel))
		  (lhs (car args))
		  (rhs (cadr args))
		  (type (term-to-type lhs))
		  (var (type-to-new-var type))
		  (varterm (make-term-in-var-form var))
		  (simphyp-formula
		   (if left-to-right
		       (formula-gen-subst leaf-formula lhs varterm)
		       (formula-gen-subst leaf-formula rhs varterm))))
	     (not (classical-formula=? simphyp-formula leaf-formula))))
      (let* ((args (term-in-app-form-to-args used-kernel))
	     (lhs (car args))
	     (rhs (cadr args))
	     (type (term-to-type lhs))
	     (var (type-to-new-var type))
	     (varterm (make-term-in-var-form var))
	     (simphyp-formula
	      (if left-to-right
		  (formula-gen-subst leaf-formula lhs varterm)
		  (formula-gen-subst leaf-formula rhs varterm)))
	     (all-formula (mk-all var simphyp-formula))
	     (proof-of-simphyp
	      (mk-proof-in-elim-form
	       (if
		left-to-right
		(compat-at all-formula)      ;allnc n,m(n=m -> A(n) -> A(m))
		(compat-rev-at all-formula)) ;allnc n,m(n=m -> A(m) -> A(n))
	       lhs rhs negatom-or-eq-proof leaf))
	     (simphyp-formula (proof-to-formula proof-of-simphyp))
	     (new-avar (formula-to-new-avar simphyp-formula DEFAULT-AVAR-NAME))
	     (new-goalformula
	      (context-and-ncvars-and-formula-to-formula
	       (append context (list new-avar)) ncvars goal-formula))
	     (new-goalvar (formula-to-new-avar new-goalformula
					       DEFAULT-AVAR-NAME))
	     (new-goal
	      (apply mk-goal-in-elim-form
		     (make-goal-in-avar-form new-goalvar)
		     (append context (list new-avar))))
	     (new-proof (make-proof-in-imp-elim-form
			 (make-proof-in-imp-intro-form new-avar new-goal)
			 proof-of-simphyp))
	     (new-num-goal (make-num-goal
			    (+ 1 maxgoal) new-goal drop-info hypname-info
			    ignore-deco-flag)))
	(make-pproof-state
	 (append (list new-num-goal) new-num-goals (cdr num-goals))
	 (goal-subst proof goal new-proof)
	 new-maxgoal)))
     ((and (prime-form? used-formula)
	   (term-in-const-form? nop)
	   (string=? "=" (const-to-name (term-in-const-form-to-const nop)))
	   (let* ((args (term-in-app-form-to-args used-nkernel))
		  (lhs (car args))
		  (rhs (cadr args))
		  (type (term-to-type lhs))
		  (var (type-to-new-var type))
		  (varterm (make-term-in-var-form var))
		  (simphyp-formula
		   (if left-to-right
		       (formula-gen-subst leaf-formula lhs varterm)
		       (formula-gen-subst leaf-formula rhs varterm))))
	     (not (classical-formula=? simphyp-formula leaf-formula))))
      (let* ((args (term-in-app-form-to-args used-nkernel))
	     (lhs (car args))
	     (rhs (cadr args))
	     (type (term-to-type lhs))
	     (var (type-to-new-var type))
	     (varterm (make-term-in-var-form var))
	     (simphyp-formula
	      (if left-to-right
		  (formula-gen-subst leaf-formula lhs varterm)
		  (formula-gen-subst leaf-formula rhs varterm)))
	     (all-formula (mk-all var simphyp-formula))
	     (proof-of-simphyp
	      (mk-proof-in-elim-form
	       (if
		left-to-right
		(compat-at all-formula)      ;allnc n,m(n=m -> A(n) -> A(m))
		(compat-rev-at all-formula)) ;allnc n,m(n=m -> A(m) -> A(n))
	       lhs rhs negatom-or-eq-proof leaf))
	     (simphyp-formula (proof-to-formula proof-of-simphyp))
	     (new-avar (formula-to-new-avar simphyp-formula DEFAULT-AVAR-NAME))
	     (new-goalformula
	      (context-and-ncvars-and-formula-to-formula
	       (append context (list new-avar)) ncvars goal-formula))
	     (new-goalvar (formula-to-new-avar new-goalformula
					       DEFAULT-AVAR-NAME))
	     (new-goal
	      (apply mk-goal-in-elim-form
		     (make-goal-in-avar-form new-goalvar)
		     (append context (list new-avar))))
	     (new-proof (make-proof-in-imp-elim-form
			 (make-proof-in-imp-intro-form new-avar new-goal)
			 proof-of-simphyp))
	     (new-num-goal (make-num-goal
			    (+ 1 maxgoal) new-goal drop-info hypname-info
			    ignore-deco-flag)))
	(make-pproof-state
	 (append (list new-num-goal) new-num-goals (cdr num-goals))
	 (goal-subst proof goal new-proof)
	 new-maxgoal)))
     ((and
       (predicate-form? used-prime-formula)
       (let ((predicate (predicate-form-to-predicate used-prime-formula)))
	 (and (idpredconst-form? predicate)
	      (string=? "EqD" (idpredconst-to-name predicate))
	      (let* ((args (predicate-form-to-args used-prime-formula))
		     (lhs (car args))
		     (rhs (cadr args))
		     (type (term-to-type lhs))
		     (var (type-to-new-var type))
		     (varterm (make-term-in-var-form var))
		     (simphyp-formula
		      (if left-to-right
			  (formula-gen-subst leaf-formula lhs varterm)
			  (formula-gen-subst leaf-formula rhs varterm))))
		(not (classical-formula=? simphyp-formula leaf-formula))))))
      (let* ((args (predicate-form-to-args used-prime-formula))
	     (lhs (car args))
	     (rhs (cadr args))
	     (type (term-to-type lhs))
	     (var (type-to-new-var type))
	     (varterm (make-term-in-var-form var))
	     (simphyp-formula
	      (if left-to-right
		  (formula-gen-subst leaf-formula lhs varterm)
		  (formula-gen-subst leaf-formula rhs varterm)))
	     (all-formula (mk-all var simphyp-formula))
	     (proof-of-simphyp
	      (mk-proof-in-elim-form
	       (if
		left-to-right
		(eqd-compat-at all-formula)     ;allnc n,m(n=m -> A(n) -> A(m))
		(eqd-compat-rev-at all-formula));allnc n,m(n=m -> A(m) -> A(n))
	       lhs rhs negatom-or-eq-proof leaf))
	     (simphyp-formula (proof-to-formula proof-of-simphyp))
	     (new-avar (formula-to-new-avar simphyp-formula DEFAULT-AVAR-NAME))
	     (new-goalformula
	      (context-and-ncvars-and-formula-to-formula
	       (append context (list new-avar)) ncvars goal-formula))
	     (new-goalvar (formula-to-new-avar new-goalformula
					       DEFAULT-AVAR-NAME))
	     (new-goal
	      (apply mk-goal-in-elim-form
		     (make-goal-in-avar-form new-goalvar)
		     (append context (list new-avar))))
	     (new-proof (make-proof-in-imp-elim-form
			 (make-proof-in-imp-intro-form new-avar new-goal)
			 proof-of-simphyp))
	     (new-num-goal (make-num-goal
			    (+ 1 maxgoal) new-goal drop-info hypname-info
			    ignore-deco-flag)))
	(make-pproof-state
	 (append (list new-num-goal) new-num-goals (cdr num-goals))
	 (goal-subst proof goal new-proof)
	 new-maxgoal)))
     ((and
       (predicate-form? used-nprime-formula)
       (let ((predicate (predicate-form-to-predicate used-nprime-formula)))
	 (and (idpredconst-form? predicate)
	      (string=? "EqD" (idpredconst-to-name predicate))
	      (let* ((args (predicate-form-to-args used-nprime-formula))
		     (lhs (car args))
		     (rhs (cadr args))
		     (type (term-to-type lhs))
		     (var (type-to-new-var type))
		     (varterm (make-term-in-var-form var))
		     (simphyp-formula
		      (if left-to-right
			  (formula-gen-subst leaf-formula lhs varterm)
			  (formula-gen-subst leaf-formula rhs varterm))))
		(not (classical-formula=? simphyp-formula leaf-formula))))))
      (let* ((args (predicate-form-to-args used-nprime-formula))
	     (lhs (car args))
	     (rhs (cadr args))
	     (type (term-to-type lhs))
	     (var (type-to-new-var type))
	     (varterm (make-term-in-var-form var))
	     (simphyp-formula
	      (if left-to-right
		  (formula-gen-subst leaf-formula lhs varterm)
		  (formula-gen-subst leaf-formula rhs varterm)))
	     (all-formula (mk-all var simphyp-formula))
	     (proof-of-simphyp
	      (mk-proof-in-elim-form
	       (if
		left-to-right
		(eqd-compat-at all-formula)     ;allnc n,m(n=m -> A(n) -> A(m))
		(eqd-compat-rev-at all-formula));allnc n,m(n=m -> A(m) -> A(n))
	       lhs rhs negatom-or-eq-proof leaf))
	     (simphyp-formula (proof-to-formula proof-of-simphyp))
	     (new-avar (formula-to-new-avar simphyp-formula DEFAULT-AVAR-NAME))
	     (new-goalformula
	      (context-and-ncvars-and-formula-to-formula
	       (append context (list new-avar)) ncvars goal-formula))
	     (new-goalvar (formula-to-new-avar new-goalformula
					       DEFAULT-AVAR-NAME))
	     (new-goal
	      (apply mk-goal-in-elim-form
		     (make-goal-in-avar-form new-goalvar)
		     (append context (list new-avar))))
	     (new-proof (make-proof-in-imp-elim-form
			 (make-proof-in-imp-intro-form new-avar new-goal)
			 proof-of-simphyp))
	     (new-num-goal (make-num-goal
			    (+ 1 maxgoal) new-goal drop-info hypname-info
			    ignore-deco-flag)))
	(make-pproof-state
	 (append (list new-num-goal) new-num-goals (cdr num-goals))
	 (goal-subst proof goal new-proof)
	 new-maxgoal)))
     (else (myerror "simphyp-with-intern"
		    "hypothesis cannot be simplified with"
		    used-formula)))))

(define (simphyp-with-kernel-aux
	 num-goals proof maxgoal negatom-or-eq-proof new-num-goals new-maxgoal
	 used-kernel bvar leaf-formula-without-kernel leaf)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (goal-formula (goal-to-formula goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (ignore-deco-flag (num-goal-to-ignore-deco-flag num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (used-formula (proof-to-formula negatom-or-eq-proof))
	 (all-formula (mk-all bvar leaf-formula-without-kernel)))
    (if
     (atom-form? used-formula)
     (let* ((proof-of-simphyp ;of A(True)
	     (mk-proof-in-elim-form
	      (compat-at all-formula) ;allnc p^,q^(p^=q^ -> A(p^) -> A(q^))
	      used-kernel ;r
	      (make-term-in-const-form true-const)
	      (mk-proof-in-elim-form ;of r=True
	       (make-proof-in-aconst-form ;of all p(atom(p) -> p=True)
		atom-true-aconst)
	       used-kernel ;r
	       negatom-or-eq-proof) ;of atom(r)
	      leaf)) ;of A(r)
	    (simphyp-formula (proof-to-formula proof-of-simphyp))
	    (new-avar (formula-to-new-avar simphyp-formula DEFAULT-AVAR-NAME))
	    (new-goalformula
	     (context-and-ncvars-and-formula-to-formula
	      (append context (list new-avar)) ncvars goal-formula))
	    (new-goalvar (formula-to-new-avar new-goalformula
					      DEFAULT-AVAR-NAME))
	    (new-goal
	     (apply mk-goal-in-elim-form
		    (make-goal-in-avar-form new-goalvar)
		    (append context (list new-avar))))
	    (new-proof (make-proof-in-imp-elim-form
			(make-proof-in-imp-intro-form new-avar new-goal)
			proof-of-simphyp))
	    (new-num-goal (make-num-goal
			   (+ 1 maxgoal) new-goal drop-info hypname-info
			   ignore-deco-flag)))
       (make-pproof-state
	(append (list new-num-goal) new-num-goals (cdr num-goals))
	(goal-subst proof goal new-proof)
	new-maxgoal))
     (let* ((info (assoc "AtomFalse" THEOREMS))
	    (atom-false-aconst
	     (if info (cadr info)
		 (myerror "simphyp-with-intern" "AtomFalse missing"
			  "all boole.(boole -> F) -> boole=False")))
	    (proof-of-simphyp ;of A(False)
	     (mk-proof-in-elim-form
	      (compat-at all-formula) ;allnc p^,q^(p^=q^ -> A(p^) -> A(q^))
	      used-kernel ;r
	      (make-term-in-const-form false-const)
	      (mk-proof-in-elim-form ;of r=False
	       (make-proof-in-aconst-form ;of all p(~p -> p=False)
		atom-false-aconst)
	       used-kernel ;r
	       negatom-or-eq-proof) ;of ~r
	      leaf)) ;of A(r)
	    (simphyp-formula (proof-to-formula proof-of-simphyp))
	    (new-avar (formula-to-new-avar simphyp-formula DEFAULT-AVAR-NAME))
	    (new-goalformula
	     (context-and-ncvars-and-formula-to-formula
	      (append context (list new-avar)) ncvars goal-formula))
	    (new-goalvar (formula-to-new-avar new-goalformula
					      DEFAULT-AVAR-NAME))
	    (new-goal
	     (apply mk-goal-in-elim-form
		    (make-goal-in-avar-form new-goalvar)
		    (append context (list new-avar))))
	    (new-proof (make-proof-in-imp-elim-form
			(make-proof-in-imp-intro-form new-avar new-goal)
			proof-of-simphyp))
	    (new-num-goal (make-num-goal
			   (+ 1 maxgoal) new-goal drop-info hypname-info
			   ignore-deco-flag)))
       (make-pproof-state
	(append (list new-num-goal) new-num-goals (cdr num-goals))
	(goal-subst proof goal new-proof)
	new-maxgoal)))))

;; simphyp-with-to expects a string as its last argument, which is used (via
;; name-hyp) to name the newly introduced simplified hypothesis.

(define (simphyp-with-to hyp . opt-dir-and-xs-and-name)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE
	  (apply simphyp-with-to-intern
		 num-goals proof maxgoal hyp opt-dir-and-xs-and-name))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (simphyp-with-to-intern num-goals proof maxgoal
				hyp . opt-dir-and-xs-and-name)
  (if (null? (cdr opt-dir-and-xs-and-name))
      (myerror "simphyp-with-to-intern" "more arguments expected"))
  (if (member DEFAULT-GOAL-NAME opt-dir-and-xs-and-name)
      (myerror "? illegal for simphyp-with-to; use simphyp-with instead"))
  (let* ((name (car (last-pair opt-dir-and-xs-and-name)))
	 (opt-dir-and-xs (list-head opt-dir-and-xs-and-name
				    (- (length opt-dir-and-xs-and-name) 1))))
    (if (not (string? name))
	(myerror "simphyp-with-to-intern" "string expected" name))
    (let* ((pproof-state1
	    (apply simphyp-with-intern
		   num-goals proof maxgoal hyp opt-dir-and-xs))
	   (num-goals (pproof-state-to-num-goals pproof-state1))
	   (num-goal
	    (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	   (goal (num-goal-to-goal num-goal))
	   (context (goal-to-context goal))
	   (avars (context-to-avars context))
	   (maxhyp (length avars)))
      (apply name-hyp-intern
	     (append pproof-state1 (list maxhyp name))))))

(define (simphyp hyp opt-dir . rest)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing"))))
	 (simphyp-result
	  (apply simphyp-intern num-goals proof maxgoal hyp opt-dir rest)))
    (if (not simphyp-result)
	(begin (display-comment "no simplification possible")
	       (if COMMENT-FLAG (newline)))
	(begin
	  (set! PPROOF-STATE simphyp-result)
	  (pproof-state-history-push PPROOF-STATE)
	  (display-new-goals num-goals number)))))

(define (simphyp-intern num-goals proof
			maxgoal hyp . opt-dir-and-x-and-elab-path-and-terms)
  (let* ((opt-dir (if (null? opt-dir-and-x-and-elab-path-and-terms)
		      (myerror "simphyp-intern" "more arguments expected")
		      (car opt-dir-and-x-and-elab-path-and-terms)))
	 (left-to-right (not (and (string? opt-dir) (string=? "<-" opt-dir))))
	 (x-and-elab-path-and-terms
	  (if left-to-right
	      opt-dir-and-x-and-elab-path-and-terms
	      (cdr opt-dir-and-x-and-elab-path-and-terms)))
	 (x (if (null? x-and-elab-path-and-terms)
		(myerror "simphyp-intern" "more arguments expected")
		(car x-and-elab-path-and-terms)))
	 (elab-path-and-terms (cdr x-and-elab-path-and-terms))
	 (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (avars (context-to-avars context))
	 (maxhyp (length avars))
	 (goal-formula (goal-to-formula goal))
	 (leaf (if (formula-form? hyp)
		   (context-and-ncvars-and-formula-to-new-goal
		    context ncvars hyp)
		   (hyp-info-to-leaf num-goal hyp)))
	 (used-leaf (if (formula-form? x)
			(context-and-ncvars-and-formula-to-new-goal
			 context ncvars x)
			(hyp-info-to-leaf num-goal x)))
	 (leaf-formula (proof-to-formula leaf))
	 (used-formula
	  (unfold-formula
	   (if (formula-form? x) x (proof-to-formula used-leaf))))
	 (sig-vars (context-to-vars context))
	 (sig-tvars-and-sig-vars
	  (if (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS))
	      sig-vars
	      (append (formula-to-tvars used-formula) sig-vars)))
	 (elab-path (do ((l elab-path-and-terms (cdr l))
			 (res '() (if (memq (car l) '(left right))
				      (cons (car l) res)
				      res)))
			((null? l) (reverse res))))
	 (xs-and-vars-and-toinst1
	  (apply fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
		 used-formula sig-tvars-and-sig-vars
		 leaf-formula left-to-right
		 elab-path))
	 (xs-and-vars-and-toinst
	  (if xs-and-vars-and-toinst1
	      xs-and-vars-and-toinst1
	      (apply
	       fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
	       (normalize-formula used-formula)
	       sig-tvars-and-sig-vars
	       (normalize-formula leaf-formula)
	       left-to-right
	       elab-path))))
    (if
     (not xs-and-vars-and-toinst)
     #f
     (let* ((xs (car xs-and-vars-and-toinst))
	    (vars (cadr xs-and-vars-and-toinst))
	    (toinst (caddr xs-and-vars-and-toinst))
	    (terms (do ((l elab-path-and-terms (cdr l))
			(res '() (if (memq (car l) '(left right))
				     res
				     (cons (car l) res))))
		       ((null? l) (reverse res))))
	    (subst (if (<= (length vars) (length terms))
		    (map list vars (list-head terms (length vars)))
		    empty-subst))
	    (subst-xs (map (lambda (x) (if (term-form? x)
					   (term-substitute x subst)
					   x))
			   xs))
	    (types (let ((info1 (assoc x THEOREMS))
			 (info2 (assoc x GLOBAL-ASSUMPTIONS))
			 (tsubst (list-transform-positive toinst
				   (lambda (x) (tvar-form? (car x))))))
		     (if
		      (and (or info1 info2) (pair? tsubst)) ;else '()
		      (let* ((aconst (if info1
					 (theorem-name-to-aconst x)
					 (global-assumption-name-to-aconst x)))
			     (fla (aconst-to-formula aconst))
			     (tvars (formula-to-tvars fla)))
			(map (lambda (tvar) (type-substitute tvar tsubst))
			     tvars))
		      '()))))
       (if (> (length vars) (length terms))
	   (apply myerror
		  "simphyp" "more terms expected, to be substituted for"
		  (list-tail vars (length terms))))
       (if (and COMMENT-FLAG (< (length vars) (length terms)))
	(begin
	  (comment "warning: superfluous terms")
	  (for-each comment
		    (map term-to-string (list-tail terms (length vars))))))
       (apply simphyp-with-intern
	      (if left-to-right
		  (append (list num-goals proof maxgoal hyp x)
			  (append types subst-xs))
		  (append (list num-goals proof maxgoal hyp "<-" x)
			  (append types subst-xs))))))))

;; simphyp-to and simphyp-to-intern simplify a given hypothesis and
;; add it with the given name to the context.

(define (simphyp-to hyp opt-dir-or-x . xs-and-name)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing"))))
	 (simphyp-result
	  (apply simphyp-to-intern
		 num-goals proof maxgoal hyp opt-dir-or-x
		 xs-and-name)))
    (if (not simphyp-result)
	(begin (display-comment "no simplification possible")
	       (if COMMENT-FLAG (newline)))
	(begin
	  (set! PPROOF-STATE simphyp-result)
	  (pproof-state-history-push PPROOF-STATE)
	  (display-new-goals num-goals number)))))

(define (simphyp-to-intern num-goals proof maxgoal
			   hyp . opt-dir-and-xs-and-name)
  (if (null? (cdr opt-dir-and-xs-and-name))
      (myerror "simphyp-to-intern" "more arguments expected"))
  (if (member DEFAULT-GOAL-NAME opt-dir-and-xs-and-name)
      (myerror "? illegal for simphyp-to; use simphyp instead"))
  (let* ((name (car (last-pair opt-dir-and-xs-and-name)))
	 (opt-dir-and-xs (list-head opt-dir-and-xs-and-name
				    (- (length opt-dir-and-xs-and-name) 1))))
    (if (not (string? name))
	(myerror "simphyp-to-intern" "string expected" name))
    (let* ((pproof-state1
	    (apply simphyp-intern
		   num-goals proof maxgoal hyp opt-dir-and-xs))
	   (num-goals (pproof-state-to-num-goals pproof-state1))
	   (num-goal
	    (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	   (goal (num-goal-to-goal num-goal))
	   (context (goal-to-context goal))
	   (avars (context-to-avars context))
	   (maxhyp (length avars)))
      (apply name-hyp-intern
	     (append pproof-state1 (list maxhyp name))))))

;; (efq) constructs a proof of the present goal from falsity, which should
;; be inferable from the context.

(define (efq)
  (let* ((fla (goal-to-formula (current-goal)))
	 (eq-pf (formula-to-ef-proof fla)))
    (use eq-pf)))

;; (invar term) expects a goal A of the same type as term.  It applies
;; InvarAll to solve the goal, resulting in the new goal term mr A.

(define (invar term)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (invar-intern num-goals proof maxgoal term))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (invar-intern num-goals proof maxgoal term)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (formula (goal-to-formula goal))
	 (type (formula-to-et-type formula))
	 (newvar (type-to-new-partial-var type))
	 (mr-formula (if (equal? type (term-to-type term))
			 (real-and-formula-to-mr-formula
			  (make-term-in-var-form newvar) formula)
			 (myerror "invar" "Type" type "of formula" formula
				  "differs from type" (term-to-type term)
				  "of realizer"	term)))
	 (vars (formula-to-free mr-formula))
	 (uninst-fla (aconst-to-uninst-formula invarall-aconst))
	 (var (all-form-to-var uninst-fla))
	 (tvar (var-to-type var))
	 (kernel (all-allnc-form-to-kernel uninst-fla))
	 (ext-predicate (imp-form-to-premise kernel))
	 (mr-predicate (imp-form-to-premise (imp-form-to-conclusion kernel)))
	 (predicate (imp-form-to-final-conclusion kernel))
	 (mr-pvar (predicate-form-to-predicate mr-predicate))
	 (pvar (predicate-form-to-predicate predicate))
	 (tsubst (make-subst tvar type))
	 (subst (make-subst-wrt var-term-equal? var term))
	 (psubst (make-substitution-wrt
		  pvar-cterm-equal?
		  (list pvar mr-pvar)
		  (list (make-cterm formula) (make-cterm newvar mr-formula))))
	 (topsubst (append tsubst subst psubst))
	 (subst-aconst (aconst-substitute invarall-aconst topsubst)))
    (apply use-with-intern
     num-goals proof maxgoal
     (make-proof-in-aconst-form subst-aconst)
     (append (map make-term-in-var-form (remove newvar vars))
	     (list term DEFAULT-GOAL-NAME DEFAULT-GOAL-NAME)))))

;; To introduce an abbreviation for a complex term by a variable one
;; can use def defnc

(define (def var-string term-string)
  (let* ((var (pv var-string))
	 (term (pt term-string))
	 (context (goal-to-context (current-goal)))
	 (vars (context-to-vars context))
	 (free (term-to-free term))
	 (hypname (string-append var-string "Ex")))
    (if (member var vars)
	(myerror "def" "Already in context" var))
    (if (member var free)
	(myerror "def" "Variable free in term" var term))
    (if (not (equal? (var-to-type var) (term-to-type term)))
	(myerror "def" "Equal types expected for var and term"
		 (var-to-type var) (term-to-type term)))
    (assert (make-exl var (make-eqd (make-term-in-var-form var) term)))
    (intro 0 term)
    (use "InitEqD")
    (assume hypname)
    (by-assume hypname
	       (var-to-string var)
	       (string-append (var-to-string var) "Def"))))

(define (defnc var-string term-string)
  (let* ((var (pv var-string))
	 (term (pt term-string))
	 (context (goal-to-context (current-goal)))
	 (vars (context-to-vars context))
	 (free (term-to-free term))
	 (hypname (string-append var-string "Exnc")))
    (if (member var vars)
	(myerror "defnc" "Already in context" var))
    (if (member var free)
	(myerror "defnc" "Variable free in term" var term))
    (if (not (equal? (var-to-type var) (term-to-type term)))
	(myerror "defnc" "Equal types expected for var and term"
		 (var-to-type var) (term-to-type term)))
    (assert (make-exnc var (make-eqd (make-term-in-var-form var) term)))
    (intro 0 term)
    (use "InitEqD")
    (assume hypname)
    (by-assume hypname
	       (var-to-string var)
	       (string-append (var-to-string var) "Def"))))

;; fold-alltotal expects a goal allnc z^(Total z^ -> A(z^)).  Using
;; AllTotalElim internally it produces a new goal all z A(z).

(define (fold-alltotal)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (fold-alltotal-intern num-goals proof maxgoal))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (fold-alltotal-intern num-goals proof maxgoal)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (goal-fla (goal-to-formula goal))
	 (free (formula-to-free goal-fla))
	 (var (if (all-allnc-form? goal-fla)
		  (all-allnc-form-to-var goal-fla)
		  (myerror "fold-alltotal-intern" "all-allnc form expected"
			   goal-fla)))
	 (kernel (all-allnc-form-to-kernel goal-fla))
	 (prem (if (imp-impnc-form? kernel)
		   (imp-impnc-form-to-premise kernel)
		   (myerror "fold-alltotal-intern" "all-allnc form expected"
			    kernel)))
	 (type (var-to-type var))
	 (concl
	  (let ((T-fla (term-to-totality-formula (make-term-in-var-form var))))
	    (if (or (formula=? prem T-fla)
		    (let ((val-type (arrow-form-to-final-val-type type)))
		      (and (formula-of-nulltype? goal-fla)
			   (alg-form? val-type)
			   (assoc (alg-name-to-totalnc-idpredconst-name
				   (alg-form-to-name val-type)) IDS)
			   (formula=? prem (term-to-totalnc-formula
					    (make-term-in-var-form var))))))
		(imp-impnc-form-to-conclusion kernel)
		(myerror "fold-alltotal-intern"
			 "totality formula expected" prem))))
	 (t-deg (if (< 1 (type-to-level type))
		    (myerror "fold-alltotal-intern"
			     "variable of type level <=1 expected"
			     (var-to-string var))
		    (var-to-t-deg var)))
	 (varterm (if (t-deg-one? t-deg)
		      (myerror "fold-alltotal-intern"
			       "partial variable expected"
			       (var-to-string var))
		      (make-term-in-var-form
		       (var-and-t-deg-to-new-var var t-deg-one))))
	 (alltotal-elim-fla (aconst-to-formula alltotal-elim-aconst))
	 (tvar (car (formula-to-tvars alltotal-elim-fla))) ;alpha
	 (pvar (car (formula-to-pvars alltotal-elim-fla))) ;(Pvar alpha)
	 (tsubst (make-subst tvar type))
	 (psubst (make-subst pvar (make-cterm var concl)))
	 (subst-aconst (aconst-substitute
			alltotal-elim-aconst (append tsubst psubst))))
    (apply
     use-with-intern
     num-goals proof maxgoal
     (make-proof-in-aconst-form subst-aconst)
     (append (map make-term-in-var-form free)
	     (list DEFAULT-GOAL-NAME)))))

;; Now we provide some tactics to generate classical proofs.

;; In the following definition of min-pr x is
;; - a number or string identifying a classical existential hypothesis
;;   from the context,
;; - the name of a classical existential global assumption or theorem
;; - a closed proof on a classical existential formula (closed ones suffice),
;; - a classical existential formula with free variables from the context,
;;   generating a new goal.
;; The result is a new implicational goal, whose premise provides the
;; (classical) existence of instances with least measure.

(define (min-pr x measure)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (min-pr-intern num-goals proof maxgoal x measure))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (min-pr-intern num-goals proof maxgoal x measure)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (l (length avars))
	 (goal-formula (goal-to-formula goal))
	 (exc-formula-and-x1
	  (cond
	   ((and (integer? x) (positive? x))
	    (if (<= x l)
		(let* ((avar (list-ref avars (- x 1)))
		       (formula (avar-to-formula avar)))
		  (list formula (make-proof-in-avar-form avar)))
		(myerror "min-pr" "assumption number expected" x)))
	   ((and (string? x)
		 (member x (hypname-info-to-names hypname-info)))
	    (let ((i (name-and-hypname-info-to-index x hypname-info)))
	      (if (<= i l)
		  (let* ((avar (list-ref avars (- i 1)))
			 (formula (avar-to-formula avar)))
		    (list formula (make-proof-in-avar-form avar)))
		  (myerror "min-pr" "assumption number expected" i))))
	   ((and (string? x) (assoc x THEOREMS))
	    (let* ((aconst (theorem-name-to-aconst x))
		   (formula (aconst-to-formula aconst)))
	      (list formula (make-proof-in-aconst-form aconst))))
	   ((and (string? x) (assoc x GLOBAL-ASSUMPTIONS))
	    (let* ((aconst (global-assumption-name-to-aconst x))
		   (formula (aconst-to-formula aconst)))
	      (list formula (make-proof-in-aconst-form aconst))))
	   ((proof-form? x) (list (proof-to-formula x) x))
	   ((formula-form? x) ;then a new goal is created
	    (list x DEFAULT-GOAL-NAME))
	   (else (myerror "min-pr" "illegal argument" x))))
	 (formula (car exc-formula-and-x1))
         (exc-formula (if (exc-form? formula)
                          formula
                          (if (or (foldable-excl-form? formula)
                                  (foldable-exca-form? formula))
                              (fold-formula formula)
                              (myerror "min-pr-intern"
                                       "exc-formula expected"
                                       formula))))
         (x1 (cadr exc-formula-and-x1))
	 (free (formula-to-free exc-formula))
	 (min-pr-proof (exc-formula-to-min-pr-proof exc-formula)))
    (apply inst-with-intern
	   num-goals proof maxgoal min-pr-proof
	   (append (map make-term-in-var-form free)
		   (list measure x1)))))

;; exc-formula-to-min-pr-proof computes first a gind-aconst (an axiom or
;; a theorem) and from this a proof of the minimum principle.

;;  Recall gind: all h,x(all x(all y(hy<hx -> Ry) -> Rx) -> all p(p -> Rx))

;;                      gind  h  x  prog:all x(all y(hy<hx -> Ry) -> Rx) True T
;;                      -------------------------------------------------------
;;                                                Rx
;;                                             --------
;;      exc-avar:all x Rx -> bot               all x Rx
;;      -----------------------------------------------
;;                           bot
;; ------------------------------------------------------------------
;; all h((all x Rx -> bot) -> all x(all y(hy<hx -> Ry) -> Rx) -> bot)

(define (exc-formula-to-min-pr-proof exc-formula . opt-gindthmname)
  (let* ((vars (quant-form-to-vars exc-formula))
         (n (length vars))
         (unfolded-formula (unfold-formula exc-formula))
         (all-formula (imp-form-to-premise unfolded-formula))
         (kernel-formula (all-form-to-final-kernel all-formula n))
         (gind-aconst (apply all-formula-and-number-to-gind-aconst
			     all-formula n opt-gindthmname))
	 (inst-gind-formula (aconst-to-inst-formula gind-aconst))
         (measure-var (all-form-to-var inst-gind-formula))
         (free (formula-to-free all-formula))
         (prog-formula (imp-form-to-premise
			(all-form-to-final-kernel inst-gind-formula)))
         (prog-avar (formula-to-new-avar prog-formula))
         (exc-avar (formula-to-new-avar unfolded-formula))
         (bot-proof
          (make-proof-in-imp-elim-form
           (make-proof-in-avar-form exc-avar)
           (apply mk-proof-in-intro-form
                  (append
                   vars
                   (list (apply
			  mk-proof-in-elim-form
			  (make-proof-in-aconst-form gind-aconst)
			  (append
			   (map make-term-in-var-form
				(append free (list measure-var) vars))
			   (list (make-proof-in-avar-form prog-avar)
				 (pt "True")
				 (make-proof-in-aconst-form
				  truth-aconst))))))))))
    (apply mk-proof-in-nc-intro-form
           (append
            free
            (list (mk-proof-in-intro-form
		   measure-var exc-avar prog-avar bot-proof))))))

;; Suppose we are proving a goal G from a classical existential
;; hypothesis ExcHyp: exc x1..xn(A1 !..! Am).  Then by the minimum
;; principle we can assume that we have x1..xn which are minimal
;; w.r.t. a measure h such that A1..Am are satified.  Correspondingly
;; we provide

(define (by-assume-minimal-wrt
	 exc-hyp . varnames-and-measure-and-minhyp-and-hyps)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (apply by-assume-minimal-wrt-intern
			      num-goals proof maxgoal exc-hyp
			      varnames-and-measure-and-minhyp-and-hyps))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (by-assume-minimal-wrt-intern
	 num-goals proof maxgoal exc-hyp .
	 varnames-and-measure-and-minhyp-and-hyps-and-opt-gindthmname)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (l (length avars))
	 (exc-formula-and-x1
	  (cond
	   ((and (integer? exc-hyp) (positive? exc-hyp))
	    (if (<= exc-hyp l)
		(let* ((avar (list-ref avars (- exc-hyp 1)))
		       (formula (avar-to-formula avar)))
		  (list formula (make-proof-in-avar-form avar)))
		(myerror "by-assume-minimal-wrt-intern"
			 "assumption number expected" exc-hyp)))
	   ((and (string? exc-hyp)
		 (member exc-hyp (hypname-info-to-names hypname-info)))
	    (let ((i (name-and-hypname-info-to-index exc-hyp hypname-info)))
	      (if (<= i l)
		  (let* ((avar (list-ref avars (- i 1)))
			 (formula (avar-to-formula avar)))
		    (list formula (make-proof-in-avar-form avar)))
		  (myerror "by-assume-minimal-wrt-intern"
			   "assumption number expected" i))))
	   ((and (string? exc-hyp) (assoc exc-hyp THEOREMS))
	    (let* ((aconst (theorem-name-to-aconst exc-hyp))
		   (formula (aconst-to-formula aconst)))
	      (list formula (make-proof-in-aconst-form aconst))))
	   ((and (string? exc-hyp) (assoc exc-hyp GLOBAL-ASSUMPTIONS))
	    (let* ((aconst (global-assumption-name-to-aconst exc-hyp))
		   (formula (aconst-to-formula aconst)))
	      (list formula (make-proof-in-aconst-form aconst))))
	   ((proof-form? exc-hyp) (list (proof-to-formula exc-hyp) exc-hyp))
	   ((formula-form? exc-hyp) ;then a new goal is created
	    (list exc-hyp DEFAULT-GOAL-NAME))
	   (else (myerror "by-assume-minimal-wrt-intern"
			  "illegal argument" exc-hyp))))
	 (exc-formula (fold-formula (car exc-formula-and-x1)))
	 (x1 (cadr exc-formula-and-x1))
	 (n (cond ((excl-form? exc-formula)
		   (length (excl-form-to-vars exc-formula)))
		  ((exca-form? exc-formula)
		   (length (exca-form-to-vars exc-formula)))
		  (else (myerror "exc-form expected" exc-formula))))
	 (l-test (excl-form? exc-formula))
	 (m (length (tensor-form-to-parts
		     (if l-test
			 (excl-form-to-kernel exc-formula)
			 (exca-form-to-kernel exc-formula)))))
	 (lh (length
	      varnames-and-measure-and-minhyp-and-hyps-and-opt-gindthmname))
	 (varnames
	  (if (<= (+ n 2 m) lh)
	      (list-head
	       varnames-and-measure-and-minhyp-and-hyps-and-opt-gindthmname n)
	      (myerror (+ n 2 m) "arguments expected in addition to exc-hyp")))
	 (vars (map pv varnames))
	 (tail
	  (list-tail
	   varnames-and-measure-and-minhyp-and-hyps-and-opt-gindthmname n))
	 (measure (car tail))
	 (minhyp (cadr tail))
	 (hyps (list-head (cddr tail) m))
	 (opt-gindthmname (list-tail (cddr tail) m)))
    (if (not (apply and-op (map (lambda (x) (and (string? x) (var? (pv x))))
				varnames)))
	(myerror "variable names expected" varnames))
    (if (not (term-form? measure)) (myerror "measure term expected" measure))
    (if (not (equal? (term-to-type measure)
		     (apply mk-arrow (append (map var-to-type vars)
					     (list (py "nat"))))))
	(myerror (apply mk-arrow (append (map var-to-type vars)
					 (list (py "nat"))))
		 "is the expected type of the measure term, not"
		 (term-to-type measure)))
    (if (not (string? minhyp))
	(myerror "name for the minimality hypothesis expected" minhyp))
    (if (not (apply and-op (map string? hyps)))
	(myerror "names for hypotheses expected" hyps))
    (let* ((free (formula-to-free exc-formula))
           (min-pr-proof (apply exc-formula-to-min-pr-proof
				exc-formula opt-gindthmname))
	   (all-h-formula (allnc-form-to-final-kernel
			   (proof-to-formula min-pr-proof)
			   (length free)))
	   (h (all-form-to-var all-h-formula))
	   (exc-min-formula
	    (formula-subst (imp-form-to-conclusion
			    (all-form-to-kernel all-h-formula))
			   h measure))
	   (pproof-state1
	    (exc-elim-intern num-goals proof maxgoal exc-min-formula)))
      (cond
       ((or ;hypothesis
	 (and (integer? exc-hyp) (positive? exc-hyp))
	 (and (string? exc-hyp)
	      (member exc-hyp (hypname-info-to-names hypname-info))))
	(let* ((pproof-state2
		(apply use-with-intern
		       (append pproof-state1
			       (list min-pr-proof)
			       (map make-term-in-var-form free)
			       (list measure exc-hyp))))
	       (pproof-state3
		(apply assume-intern
		       (append pproof-state2
			       (append varnames (list minhyp) hyps)))))
	  (apply drop-intern (append pproof-state3 (list exc-hyp)))))
       ((or ;theorem/global assumption/proof
	 (and (string? exc-hyp) (assoc exc-hyp THEOREMS))
	 (and (string? exc-hyp) (assoc exc-hyp GLOBAL-ASSUMPTIONS))
	 (proof-form? exc-hyp))
	(let* ((pproof-state2
		(apply use-with-intern
		       (append pproof-state1
			       (list min-pr-proof)
			       (map make-term-in-var-form free)
			       (list measure exc-hyp)))))
	  (apply assume-intern (append pproof-state2
				       (append varnames (list minhyp) hyps)))))
       ((formula-form? exc-hyp) ;then a new goal is created
	(let* ((pproof-state2
		(apply use-with-intern
		       (append pproof-state1
                               (list min-pr-proof)
			       (map make-term-in-var-form free)
			       (list measure DEFAULT-GOAL-NAME))))
	       (pproof-state3
		(apply get-intern
		       (append pproof-state2
			       (list (- (pproof-state-to-maxgoal pproof-state2)
					1)))))
	       (pproof-state4
		(apply assume-intern
		       (append pproof-state3
			       (append varnames (list minhyp) hyps)))))
	  (apply get-intern
		 (append pproof-state4
			 (list (- (pproof-state-to-maxgoal pproof-state4)
				  1))))))
       (else (myerror "by-assume-minimal-wrt-intern"
		      "unexpected exc-hyp" exc-hyp))))))

;; We need procedures to generate aconsts - depending on a number n of
;; variables and a number m of formulas - for GInd, ExclElim,
;; ExclIntro, MinPr.  This will involve certain fixed variables, terms
;; and formulas, which are provided first.  k works as a counter

(define (make-fixed-tvars n)
  (do ((i (- n 1) (- i 1))
       (res (list (make-tvar n DEFAULT-TVAR-NAME))
	    (cons (make-tvar i DEFAULT-TVAR-NAME) res)))
      ((zero? i) res)))

;; make-fixed-pvar is a function generating a predicate variable taking
;; n arguments of type alpha1 to alphan.  Its index is 0, and it has
;; computational content.

(define (make-fixed-pvar n)
  (let* ((fixed-tvars (make-fixed-tvars n))
	 (fixed-arity (apply make-arity fixed-tvars)))
    (make-pvar fixed-arity 0 0 0 "")))

;; make-fixed-pvars is a function generating m predicate variables.
;; Each predicate takes n arguments of type alpha1 to alphan.  Their
;; indices rum from 1 to m, and all have computational content.

(define (make-fixed-pvars m n)
  (let* ((fixed-tvars (make-fixed-tvars n))
	 (fixed-arity (apply make-arity fixed-tvars)))
    (do ((j (- m 1) (- j 1))
	 (res (list (make-pvar fixed-arity m 0 0 ""))
	      (cons (make-pvar fixed-arity j 0 0 "") res)))
	((zero? j) res))))

;; make-fixed-measure-var returns a variable of the type of the measure
;; function, i.e., alpha1 => ... => alphan => nat.

(define (make-fixed-measure-var n)
  (let* ((fixed-tvars (make-fixed-tvars n))
	 (measure-function-type
	  (apply mk-arrow (append fixed-tvars (list (py "nat"))))))
    (make-var measure-function-type -1 1 "")))

;; make-fixed-vars is a function generating (alpha1)_((k-1)*n+1)
;; ... (alphan)_((k-1)*n+n), i.e., the kth set of n fresh variables of
;; types alpha1 to alphan.

(define (make-fixed-vars k n)
  (do ((i (- n 1) (- i 1))
       (res (list (make-var (make-tvar n DEFAULT-TVAR-NAME)
			    (+ (* (- k 1) n) n) 1 ""))
	    (cons (make-var (make-tvar i DEFAULT-TVAR-NAME)
			    (+ (* (- k 1) n) i) 1 "")
		  res)))
      ((zero? i) res)))

;; make-gind-aconst takes a positive integer n and returns an assumption
;; constant for general induction w.r.t. a measure function of type
;; alpha1 => ... => alphan => nat.

;;                                    NatLtLtSuccTrans hy hx k v:hy<hx w:hx<Sk
;;                                    ----------------------------------------
;;                           IH  y                            hy<k
;;                           -------------------------------------
;;                                                   Ry
;;                                      ---------------------------
;;          Efq:bot->Rx u:hx<0          Prog^h  x  all y(hy<hx->Ry)
;;          ------------------          ---------------------------
;;                    Rx                           Rx
;;             ---------------    ----------------------------------------
;; Ind h S(hx) all x(hx<0->Rx)    all k(all x(hx<k->Rx)->all x(hx<Sk->Rx))
;; -----------------------------------------------------------------------
;;                          all x(hx<S(hx)->Rx)                             x T
;;                          ---------------------------------------------------
;;                                                     Rx
;;                                            ---------------------
;;                                            all h,x(Prog^h -> Rx)

(define (make-gind-aconst n)
  (let* ((gind-name (string-append "GInd" (number-to-alphabetic-string n)))
	 (info (assoc gind-name THEOREMS)))
    (if
     info
     (theorem-name-to-aconst gind-name)
     (let* ((h (make-fixed-measure-var n))
	    (x (make-fixed-vars 1 n))
	    (y (make-fixed-vars 2 n))
	    (R (make-fixed-pvar n))
	    (Rx (apply make-predicate-formula R (map make-term-in-var-form x)))
	    (Ry (apply make-predicate-formula R (map make-term-in-var-form y)))
	    (hx (apply mk-term-in-app-form
		       (make-term-in-var-form h)
		       (map make-term-in-var-form x)))
	    (hy (apply mk-term-in-app-form
		       (make-term-in-var-form h)
		       (map make-term-in-var-form y)))
	    (k (make-var (py "nat") -1 1 ""))
	    (hx<0 (make-atomic-formula
		   (mk-term-in-app-form (make-term-in-const-form
					 (pconst-name-to-pconst "NatLt"))
					hx (pt "Zero"))))
	    (hx<k (make-atomic-formula
		   (mk-term-in-app-form (make-term-in-const-form
					 (pconst-name-to-pconst "NatLt"))
					hx (make-term-in-var-form k))))
	    (hy<hx (make-atomic-formula
		    (mk-term-in-app-form (make-term-in-const-form
					  (pconst-name-to-pconst "NatLt"))
					 hy hx)))
	    (hx<Sk (make-atomic-formula
		    (mk-term-in-app-form (make-term-in-const-form
					  (pconst-name-to-pconst "NatLt"))
					 hx (make-term-in-app-form
					     (pt "Succ")
					     (make-term-in-var-form k)))))
	    (IH-fla ;all x(hx<k->Rx)
	     (apply mk-all (append x (list (make-imp hx<k Rx)))))
	    (prog-fla ;all x((all y(hy<hx) -> Ry) -> Rx)
	     (apply
	      mk-all
	      (append
	       x (list (make-imp
			(apply mk-all (append y (list (make-imp hy<hx Ry))))
			Rx)))))
	    (ind-fla (make-all k IH-fla))
	    (u (formula-to-new-avar hx<0))
	    (v (formula-to-new-avar hy<hx))
	    (w (formula-to-new-avar hx<Sk))
	    (IH (formula-to-new-avar IH-fla))
	    (prog (formula-to-new-avar prog-fla))
	    (efq (proof-of-efq-at Rx))
	    (proof
	     (apply
	      mk-proof-in-intro-form
	      (append
	       (list h)
	       x
	       (list
		prog
		(apply
		 mk-proof-in-elim-form
		 (append
		  (list
		   (make-proof-in-aconst-form
		    (all-formulas-to-ind-aconst ind-fla))
		   (make-term-in-var-form h)
		   (make-term-in-app-form (pt "Succ") hx)
		   (apply ;base
		    mk-proof-in-intro-form
		    (append
		     x (list u (mk-proof-in-elim-form
				efq (make-proof-in-avar-form u)))))
		   (apply ;step
		    mk-proof-in-intro-form
		    (append
		     (list k IH)
		     x (list
			w (apply
			   mk-proof-in-elim-form
			   (append
			    (list (make-proof-in-avar-form prog))
			    (map make-term-in-var-form x)
			    (list
			     (apply
			      mk-proof-in-intro-form
			      (append
			       y (list
				  v (apply
				     mk-proof-in-elim-form
				     (append
				      (list (make-proof-in-avar-form IH))
				      (map make-term-in-var-form y)
				      (list
				       (mk-proof-in-elim-form
					(make-proof-in-aconst-form
					 (theorem-name-to-aconst
					  "NatLtLtSuccTrans"))
					hy hx
					(make-term-in-var-form k)
					(make-proof-in-avar-form v)
					(make-proof-in-avar-form
					 w)))))))))))))))
		  (map make-term-in-var-form x)
		  (list (make-proof-in-aconst-form truth-aconst)))))))))
       (set! OLD-COMMENT-FLAG COMMENT-FLAG)
       (set! COMMENT-FLAG #f)
       (add-theorem gind-name proof)
       (set! COMMENT-FLAG OLD-COMMENT-FLAG)
       (theorem-name-to-aconst gind-name)))))

;; make-min-pr-aconst takes positive integers m,n and returns an
;; assumption constant for the minimum principle w.r.t. a measure
;; function h of type alpha1 => ... => alphan => nat.  Let x=x1...xn.

;; all h(exc x(Q1x ! ... ! Qmx) ->
;;       exc x(all y(hy<hx -> Q1y -> ... -> Qmy -> bot) ! Q1x ! ... ! Qmx))

;; In unfolded form, with Rx := Q1x -> ... -> Qmx -> bot

;; all h((all x Rx -> bot) -> all x(all y(hy<hx -> Ry) -> Rx) -> bot)

;; Recall gind: all h,x(all x(all y(hy<hx -> Ry) -> Rx) -> Rx)

;;                           gind  h  x  prog:all x(all y(hy<hx -> Ry) -> Rx)
;;                           ----------------------------------------------
;;                                                Rx
;;                                             --------
;;      u:all x Rx -> bot                      all x Rx
;;      ------------------------------------------------
;;                           bot
;; -------------------------------------------------------------------
;; all h((all x Rx -> bot) -> all x(all y(hy<hx -> Ry) -> Rx) -> bot)

(define (make-min-pr-aconst l-test m n)
  (let* ((min-pr-name (string-append "MinPr" (if l-test "l" "a")
				     (number-to-alphabetic-string m)
				     (number-to-alphabetic-string n)))
	 (info (assoc min-pr-name THEOREMS)))
    (if
     info
     (theorem-name-to-aconst min-pr-name)
     (let* ((gind-aconst (make-gind-aconst n))
	    (gind-uninst-fla (aconst-to-uninst-formula gind-aconst))
	    (h (all-form-to-var gind-uninst-fla))
	    (Rx (imp-all-allnc-form-to-final-conclusion gind-uninst-fla))
	    (pvar (predicate-form-to-predicate Rx))
	    (x (map term-in-var-form-to-var (predicate-form-to-args Rx)))
	    (arity (apply make-arity (map var-to-type x)))
	    (Qs ;pvars indexed 1..m of the same arity as R
	     (do ((j (- m 1) (- j 1))
		  (res (list (make-pvar arity m 0 0 ""))
		       (cons (make-pvar arity j 0 0 "") res)))
		 ((zero? j) res)))
	    (bot (if l-test falsity-log falsity))
	    (parts (map (lambda (Q)
			  (apply make-predicate-formula
				 Q (map make-term-in-var-form x)))
			Qs))
	    (cterm (apply
		    make-cterm
		    (append
		     x (list (apply mk-imp (append parts (list bot)))))))
	    (inst-gind-aconst
	     (make-aconst (aconst-to-name gind-aconst)
			  (aconst-to-kind gind-aconst)
			  (aconst-to-uninst-formula gind-aconst)
			  (list (list pvar cterm))))
	    (gind-fla (aconst-to-formula inst-gind-aconst))
	    (prog-fla
	     (imp-form-to-premise (all-form-to-final-kernel gind-fla)))
	    (all-fla ;all x Rx
	     (apply
	      mk-all
	      (append
	       x (list (imp-form-to-conclusion
			(all-form-to-final-kernel gind-fla))))))
	    (u (formula-to-new-avar (make-imp all-fla bot)))
	    (prog (formula-to-new-avar prog-fla))
	    (proof
	     (mk-proof-in-intro-form
	      h u prog
	      (make-proof-in-imp-elim-form
	       (make-proof-in-avar-form u)
	       (apply
		mk-proof-in-intro-form
		(append
		 x (list (apply
			  mk-proof-in-elim-form
			  (append
			   (list (make-proof-in-aconst-form inst-gind-aconst)
				 (make-term-in-var-form h))
			   (predicate-form-to-args Rx)
			   (list (make-proof-in-avar-form prog)))))))))))
       (set! OLD-COMMENT-FLAG COMMENT-FLAG)
       (set! COMMENT-FLAG #f)
       (add-theorem min-pr-name proof)
       (set! COMMENT-FLAG OLD-COMMENT-FLAG)
       (theorem-name-to-aconst min-pr-name)))))

;; exc-intro and exc-elim can be used in interactive proofs.

(define (exc-intro . terms)
  (for-each
   (lambda (x)
     (if
      (string? x)
      (myerror "exc-intro" "use pt (parse-term) to produce a term from string"
	       x)))
   terms)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (apply exc-intro-intern num-goals proof maxgoal terms))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (exc-intro-intern num-goals proof maxgoal . terms)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (goal-formula (fold-formula (goal-to-formula goal)))
	 (l-test (excl-form? goal-formula))
	 (quant (cond (l-test 'excl)
		      ((exca-form? goal-formula) 'exca)
		      (else (myerror "exc-intro" "exc goal expected"))))
	 (vars (quant-form-to-vars goal-formula))
	 (kernel (quant-form-to-kernel goal-formula))
	 (free (formula-to-free goal-formula))
	 (parts (tensor-form-to-parts kernel)))
    (if (not (= (length vars) (length terms)))
	(myerror "exc-intro" "vars and terms of equal length expected"
		 (map var-to-string vars)
		 (map term-to-string terms)))
    (apply
     use-with-intern
     num-goals proof maxgoal
     (make-proof-in-aconst-form
      (if l-test
	  (excl-formula-to-excl-intro-aconst goal-formula)
	  (exca-formula-to-exca-intro-aconst goal-formula)))
     (append (map make-term-in-var-form free)
	     terms
	     (vector->list (make-vector (length parts) DEFAULT-GOAL-NAME))))))

(define (exca-formula-to-exca-intro-aconst exca-formula)
  (let* ((vars (quant-form-to-vars exca-formula))
	 (kernel (quant-form-to-kernel exca-formula))
	 (parts (tensor-form-to-parts kernel))
	 (n (length vars))
	 (m (length parts))
	 (exca-intro-aconst (make-exca-intro-aconst m n))
	 (types (map var-to-type vars))
	 (cterms (map (lambda (part)
			(apply make-cterm (append vars (list part))))
		      parts))
	 (exca-intro-uninst-fla (aconst-to-uninst-formula exca-intro-aconst))
	 (pvars (list-head (formula-to-pvars exca-intro-uninst-fla)
			   (length parts)))
	 (tvars (formula-to-tvars exca-intro-uninst-fla))
	 (tsubst (make-substitution tvars types))
	 (psubst (map list pvars cterms)))
    (make-aconst (aconst-to-name exca-intro-aconst)
		 (aconst-to-kind exca-intro-aconst)
		 (aconst-to-uninst-formula exca-intro-aconst)
		 (append tsubst psubst))))

(define (excl-formula-to-excl-intro-aconst excl-formula)
  (let* ((vars (quant-form-to-vars excl-formula))
	 (kernel (quant-form-to-kernel excl-formula))
	 (parts (tensor-form-to-parts kernel))
	 (n (length vars))
	 (nc-indicator (map formula-of-nulltype? parts))
	 (excl-intro-aconst (make-excl-intro-aconst nc-indicator n))
	 (types (map var-to-type vars))
	 (cterms (map (lambda (part)
			(apply make-cterm (append vars (list part))))
		      parts))
	 (excl-intro-uninst-fla (aconst-to-uninst-formula excl-intro-aconst))
	 (pvars (list-head (formula-to-pvars excl-intro-uninst-fla)
			   (length parts)))
	 (tvars (formula-to-tvars excl-intro-uninst-fla))
	 (tsubst (make-substitution tvars types))
	 (psubst (map list pvars cterms)))
    (make-aconst (aconst-to-name excl-intro-aconst)
		 (aconst-to-kind excl-intro-aconst)
		 (aconst-to-uninst-formula excl-intro-aconst)
		 (append tsubst psubst))))

;; make-exca-intro-aconst takes positive integers m,n and returns an
;; assumption constant for exca-introduction w.r.t. n variables of type
;; alpha1 to alphan.  Let xs = x1...xn

;; all xs(Q1 xs -> ... -> Qm xs -> exca xs(Q1 xs ! ... ! Qm xs))

;; In unfolded form

;; all xs(Q1 xs -> ... -> Qm xs -> all xs(Q1 xs -> ... -> Qm xs -> F) -> F)

;;      v: all xs(Q1 xs -> ... -> Qm xs -> F)  xs  u1:Q1 xs ... um:Qm xs
;;      ----------------------------------------------------------------
;;                                     F

(define (make-exca-intro-aconst m n)
  (let* ((exca-intro-name (string-append "ExcaIntro"
					 (number-to-alphabetic-string m)
					 (number-to-alphabetic-string n)))
	 (info (assoc exca-intro-name THEOREMS)))
    (if
     info
     (theorem-name-to-aconst exca-intro-name)
     (let* ((x (make-fixed-vars 1 n))
	    (Qs (make-fixed-pvars m n))
	    (parts (map (lambda (Q)
			  (apply make-predicate-formula
				 Q (map make-term-in-var-form x)))
			Qs))
	    (all-fla ;all x(Q1x -> ... -> Qmx -> F)
	     (apply
	      mk-all
	      (append x (list (apply mk-imp (append parts (list falsity)))))))
	    (us (map formula-to-new-avar parts))
	    (v (formula-to-new-avar all-fla))
	    (proof (apply
		    mk-proof-in-intro-form
		    (append
		     x us (list v)
		     (list (apply mk-proof-in-elim-form
				  (append
				   (list (make-proof-in-avar-form v))
				   (map make-term-in-var-form x)
				   (map make-proof-in-avar-form us))))))))
       (set! OLD-COMMENT-FLAG COMMENT-FLAG)
       (set! COMMENT-FLAG #f)
       (add-theorem exca-intro-name proof)
       (set! COMMENT-FLAG OLD-COMMENT-FLAG)
       (theorem-name-to-aconst exca-intro-name)))))

;; (pp (rename-variables (aconst-to-formula (make-exca-intro-aconst 2 1))))
;; all alpha1(
;; (Pvar alpha1)_1 alpha1 ->
;; (Pvar alpha1)_2 alpha1 ->
;; all alpha1_0((Pvar alpha1)_1 alpha1_0 -> (Pvar alpha1)_2 alpha1_0 -> F) ->
;; F)

;; make-excl-intro-aconst takes a list nc-indicator of booleans and a
;; positive integer n.  The n.c. or c.r. status of each Q is determined
;; by nc-indicator.  It returns an assumption constant for
;; excl-introduction w.r.t. n variables of type alpha1 to alphan.  Let
;; xs = x1...xn

;; all xs(Q1 xs -> ... -> Qm xs -> excl xs(Q1 xs ! ... ! Qm xs))

;; In unfolded form

;; all xs(Q1 xs -> ... -> Qm xs -> all xs(Q1 xs -> ... -> Qm xs -> bot) -> bot)

;;                      v: all x(Qs x -> bot)  x  ws:Qs x
;;                      ---------------------------------
;;                                     bot
;;                   ---------------------------------------
;;                   all x(Qs x -> all x(Qs x -> bot) -> bot)

(define (make-excl-intro-aconst nc-indicator n)
    (let* ((all-cr? (apply and-op (map not nc-indicator)))
	   (nc-indicator-string
	    (if  all-cr? ""
		 (apply string-append
			(map (lambda (p) (if p "Nc" "Cr")) nc-indicator))))
	   (excl-intro-name
	    (string-append "ExclIntro"
			   (number-to-alphabetic-string n)
			   nc-indicator-string))
	   (info (assoc excl-intro-name THEOREMS)))
      (if
       info
       (theorem-name-to-aconst excl-intro-name)
       (let* ((pvar-flas (make-fixed-pvar-formulas nc-indicator n))
	      (imp-fla ;Q1x -> ... -> Qmx -> bot
	       (apply mk-imp (append pvar-flas (list falsity-log))))
	      (xs (make-fixed-vars 1 n))
	      (excl-prem ;all x(Q1x -> ... -> Qmx -> bot)
	       (apply mk-all (append xs (list imp-fla))))
	      (ws (map formula-to-new-avar pvar-flas))
	      (v (formula-to-new-avar excl-prem))
	      (proof (apply
		      mk-proof-in-intro-form
		      (append
		       xs ws (list v (apply mk-proof-in-elim-form
					    (make-proof-in-avar-form v)
					    (append
					     (map make-term-in-var-form xs)
					     (map make-proof-in-avar-form
						  ws))))))))
	 (set! OLD-COMMENT-FLAG COMMENT-FLAG)
	 (set! COMMENT-FLAG #f)
	 (add-theorem excl-intro-name proof)
	 (set! COMMENT-FLAG OLD-COMMENT-FLAG)
	 (theorem-name-to-aconst excl-intro-name)))))

(define (make-fixed-pvar-formulas nc-indicator n)
  (let* ((xs (make-fixed-vars 1 n))
	 (fixed-tvars (map var-to-type xs))
	 (fixed-arity (apply make-arity fixed-tvars))
	 (m (length nc-indicator))
	 (one-to-m (do ((i 1 (+ i 1))
			(res '() (cons i res)))
		       ((< m i) (reverse res))))
	 (fixed-pvars
	  (map (lambda (i is-nc)
		 (make-pvar fixed-arity i
			    (if is-nc h-deg-one h-deg-zero)
			    n-deg-zero ""))
	       one-to-m nc-indicator)))
    (map (lambda (pvar)
	   (apply make-predicate-formula pvar (map make-term-in-var-form xs)))
	 fixed-pvars)))

;; (for-each pp (make-fixed-pvar-formulas (list #f #t) 3))

;; (Pvar alpha1 alpha2 alpha3)_1 alpha1_1 alpha2_2 alpha3_3
;; (Pvar alpha1 alpha2 alpha3)^2 alpha1_1 alpha2_2 alpha3_3

;; (define aconst (make-excl-intro-aconst (list #f #t) 3))

;; (pp "ExclIntroThreeCrNc")

;; all alpha1,alpha2_0,alpha3_1(
;;  (Pvar alpha1 alpha2 alpha3)_1 alpha1 alpha2_0 alpha3_1 -> 
;;  (Pvar alpha1 alpha2 alpha3)^2 alpha1 alpha2_0 alpha3_1 -> 
;;  excl alpha1_2,alpha2_3,alpha3_4(
;;   (Pvar alpha1 alpha2 alpha3)_1 alpha1_2 alpha2_3 alpha3_4 ! 
;;   (Pvar alpha1 alpha2 alpha3)^2 alpha1_2 alpha2_3 alpha3_4))

;; (pp (unfold-formula (aconst-to-formula aconst)))

;; all alpha1_1,alpha2_2,alpha3_3(
;;  (Pvar alpha1 alpha2 alpha3)_1 alpha1_1 alpha2_2 alpha3_3 -> 
;;  (Pvar alpha1 alpha2 alpha3)^2 alpha1_1 alpha2_2 alpha3_3 -> 
;;  all alpha1_1,alpha2_2,alpha3_3(
;;   (Pvar alpha1 alpha2 alpha3)_1 alpha1_1 alpha2_2 alpha3_3 -> 
;;   (Pvar alpha1 alpha2 alpha3)^2 alpha1_1 alpha2_2 alpha3_3 -> bot) -> 
;;  bot)

;; In the following definition of exc-elim x is
;; - a number or string identifying an existential hypothesis form the context,
;; - the name of an existential global assumption or theorem
;; - a closed proof on an existential formula (closed ones suffice),
;; - an existential formula with free variables from the context,
;;   generating a new goal.

(define (exc-elim x)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (exc-elim-intern num-goals proof maxgoal x))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (exc-elim-intern num-goals proof maxgoal x)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
         (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (l (length avars))
	 (goal-formula (goal-to-formula goal))
         (exc-formula-and-x1
	  (cond
	   ((and (integer? x) (positive? x))
	    (if (<= x l)
		(let* ((avar (list-ref avars (- x 1)))
		       (formula (avar-to-formula avar)))
		  (list formula (make-proof-in-avar-form avar)))
		(myerror "exc-elim" "assumption number expected" x)))
	   ((and (string? x)
		 (member x (hypname-info-to-names hypname-info)))
	    (let ((i (name-and-hypname-info-to-index x hypname-info)))
	      (if (<= i l)
		  (let* ((avar (list-ref avars (- i 1)))
			 (formula (avar-to-formula avar)))
		    (list formula (make-proof-in-avar-form avar)))
		  (myerror "exc-elim" "assumption number expected" i))))
	   ((and (string? x) (assoc x THEOREMS))
	    (let* ((aconst (theorem-name-to-aconst x))
		   (formula (aconst-to-formula aconst)))
	      (list formula (make-proof-in-aconst-form aconst))))
	   ((and (string? x) (assoc x GLOBAL-ASSUMPTIONS))
	    (let* ((aconst (global-assumption-name-to-aconst x))
		   (formula (aconst-to-formula aconst)))
	      (list formula (make-proof-in-aconst-form aconst))))
	   ((proof-form? x) (list (proof-to-formula x) x))
	   ((formula-form? x) ;then a new goal is created
	    (list x DEFAULT-GOAL-NAME))
	   (else (myerror "exc-elim" "illegal argument" x))))
         (exc-formula (fold-formula (car exc-formula-and-x1)))
	 (exc-elim-aconst
	  (cond
	   ((and (exca-form? exc-formula) (negation-form? goal-formula))
	    (exca-formula-and-nega-concl-to-exca-elim-neg-aconst
	     exc-formula goal-formula))
	   ((and (excl-form? exc-formula) (negation-log-form? goal-formula))
	    (excl-formula-and-negl-concl-to-excl-elim-neg-aconst
	     exc-formula goal-formula))
	   (else (exc-formula-and-concl-to-exc-elim-aconst
		  exc-formula goal-formula))))
         (x1 (cadr exc-formula-and-x1))
	 (free1 (formula-to-free exc-formula))
	 (free2 (formula-to-free goal-formula))
         (free (union free1 free2)))
    (apply use-with-intern
	   num-goals proof maxgoal
	   (make-proof-in-aconst-form exc-elim-aconst)
	   (append (map make-term-in-var-form free)
		   (list x1 DEFAULT-GOAL-NAME)))))

(define (exca-formula-and-nega-concl-to-exca-elim-neg-aconst
	 exca-formula nega-concl)
  (let* ((vars (quant-form-to-vars exca-formula))
	 (kernel (quant-form-to-kernel exca-formula))
	 (parts (tensor-form-to-parts kernel))
	 (m (length parts))
	 (n (length vars))
	 (part (negation-form-to-kernel nega-concl))
	 (exca-elim-neg-aconst (make-exca-elim-neg-aconst m n))
	 (types (map var-to-type vars))
	 (cterms (map (lambda (part)
			(apply make-cterm (append vars (list part))))
		      parts))
	 (cterm (make-cterm part))
	 (exca-elim-neg-uninst-fla
	  (aconst-to-uninst-formula exca-elim-neg-aconst))
	 (tvars (formula-to-tvars exca-elim-neg-uninst-fla))
	 (tsubst (make-substitution tvars types))
	 (pvars (formula-to-pvars exca-elim-neg-uninst-fla))
	 (psubst (make-substitution-wrt
		  pvar-cterm-equal? pvars (append cterms (list cterm)))))
    (make-aconst (aconst-to-name exca-elim-neg-aconst)
		 (aconst-to-kind exca-elim-neg-aconst)
		 exca-elim-neg-uninst-fla
		 (append tsubst psubst))))

(define (excl-formula-and-negl-concl-to-excl-elim-neg-aconst
	 excl-formula negl-concl)
  (let* ((vars (quant-form-to-vars excl-formula))
	 (kernel (quant-form-to-kernel excl-formula))
	 (parts (tensor-form-to-parts kernel))
	 (n (length vars))
	 (part (negation-log-form-to-kernel negl-concl))
	 (nc-indicator (map formula-of-nulltype? (append parts (list part))))
	 (excl-elim-neg-aconst (make-excl-elim-neg-aconst nc-indicator n))
	 (types (map var-to-type vars))
	 (cterms (map (lambda (part)
			(apply make-cterm (append vars (list part))))
		      parts))
	 (cterm (make-cterm part))
	 (excl-elim-neg-uninst-fla
	  (aconst-to-uninst-formula excl-elim-neg-aconst))
	 (tvars (formula-to-tvars excl-elim-neg-uninst-fla))
	 (tsubst (make-substitution tvars types))
	 (pvars-with-bot (formula-to-pvars excl-elim-neg-uninst-fla))
	 (pvars (remove (predicate-form-to-predicate falsity-log)
			pvars-with-bot))
	 (psubst (make-substitution-wrt
		  pvar-cterm-equal? pvars (append cterms (list cterm)))))
    (make-aconst (aconst-to-name excl-elim-neg-aconst)
		 (aconst-to-kind excl-elim-neg-aconst)
		 excl-elim-neg-uninst-fla
		 (append tsubst psubst))))

;; The default case uses stability, via make-exc-elim-aconst.  We
;; define a procedure that takes a classical existential formula and a
;; conclusion, and returns the corresponding existence elimination
;; theorem all ys(exc xs As -> all xs(As -> B) -> B).

(define (exc-formula-and-concl-to-exc-elim-aconst exc-formula concl)
  (let* ((l-test (excl-form? exc-formula))
	 (vars (quant-form-to-vars exc-formula))
	 (kernel (quant-form-to-kernel exc-formula))
	 (parts (tensor-form-to-parts kernel))
	 (n (length vars))
	 (m (length parts))
	 (exc-elim-aconst (make-exc-elim-aconst l-test m n))
	 (types (map var-to-type vars))
	 (cterms (map (lambda (part)
			(apply make-cterm (append vars (list part))))
		      parts))
	 (cterm (make-cterm concl))
	 (exc-elim-uninst-fla (aconst-to-uninst-formula exc-elim-aconst))
	 (pvars-with-bot (formula-to-pvars exc-elim-uninst-fla))
	 (pvars (list-head pvars-with-bot (length parts)))
	 (pvar (car (last-pair pvars-with-bot)))
	 (tvars (formula-to-tvars exc-elim-uninst-fla))
	 (tsubst (make-substitution tvars types))
	 (psubst (map (lambda (pv ct) (list pv ct))
		      (cons pvar pvars) (cons cterm cterms))))
    (make-aconst (aconst-to-name exc-elim-aconst)
		 (aconst-to-kind exc-elim-aconst)
		 (aconst-to-uninst-formula exc-elim-aconst)
		 (append tsubst psubst))))

;; make-exca-elim-neg-aconst takes positive integers m,n.  It returns an
;; assumption constant for exca-elimination w.r.t. n variables of type
;; alpha1 to alphan.  Let xs=x1...xn.

;; exc xs(Q1 xs ! ... ! Qm xs) -> all xs(Q1 xs -> ... -> Qm xs -> ~P) -> ~P

;; In unfolded form

;; (all xs(Q1 xs -> ... -> Qm xs -> F) -> F) ->
;;  all xs(Q1 xs -> ... -> Qm xs -> ~P) -> ~P

;; For simplicity take n=1

;;                    v: all x(Qs x -> P -> F)  x  ws:Qs x  w:P
;;                    --------------------------------------
;;                                            F
;;                                         -------
;;                                         Qs x -> F
;;                                         -------
;;      u:all x ~Qs x -> F                 all x ~Qs x
;;      ------------------------------------------
;;                            F
;;                          ------
;;                          P -> F
;;                -----------------------------
;;                all x(Qs x -> P -> F) -> P -> F
;;     ----------------------------------------
;;     exca Qs x -> all x(Qs x -> P -> F) -> P -> F

(define (make-exca-elim-neg-aconst m n)
  (let* ((exca-elim-neg-name
	  (string-append "ExcaElimNeg"
			 (number-to-alphabetic-string m)
			 (number-to-alphabetic-string n)))
	 (info (assoc exca-elim-neg-name THEOREMS)))
    (if
     info
     (theorem-name-to-aconst exca-elim-neg-name)
     (let* ((pvar-formulas (make-fixed-pvar-formulas m n))
	    (pvar (make-pvar (make-arity) -1 h-deg-zero n-deg-zero ""))
	    (pvar-formula (make-predicate-formula pvar))
	    (imp-fla (apply mk-imp (append pvar-formulas (list falsity))))
	    (xs (make-fixed-vars 1 n))
	    (exca-prem ;all x(Q1x -> ... -> Qmx -> F)
	     (apply mk-all (append xs (list imp-fla))))
	    (all-imp-fla ;all x(Q1x -> ... -> Qmx -> P -> bot)
	     (apply mk-all
		    (append
		     xs (list (apply mk-imp
				     (append pvar-formulas
					     (list pvar-formula falsity)))))))
	    (v (formula-to-new-avar all-imp-fla))
	    (ws (map formula-to-new-avar pvar-formulas))
	    (w (formula-to-new-avar pvar-formula))
	    (intro-proof
	     (apply
	      mk-proof-in-intro-form
	      (append
	       xs ws (list (apply
			    mk-proof-in-elim-form
			    (make-proof-in-avar-form v)
			    (append (map make-term-in-var-form xs)
				    (map make-proof-in-avar-form ws)
				    (list (make-proof-in-avar-form w))))))))
	    (u (formula-to-new-avar (make-negation exca-prem)))
	    (elim-proof (make-proof-in-imp-elim-form
			 (make-proof-in-avar-form u) intro-proof))
	    (proof (mk-proof-in-intro-form u v w elim-proof)))
       (set! OLD-COMMENT-FLAG COMMENT-FLAG)
       (set! COMMENT-FLAG #f)
       (add-theorem exca-elim-neg-name proof)
       (set! COMMENT-FLAG OLD-COMMENT-FLAG)
       (theorem-name-to-aconst exca-elim-neg-name)))))

;; make-excl-elim-neg-aconst takes nc-indicator, a positive integer n
;; and a negation ~A.  The n.c. or c.r. status of each Q and of P is
;; determined by nc-indicator.  It returns an assumption constant for
;; excl-elimination w.r.t. n variables of type alpha1 to alphan.  Let
;; xs=x1...xn.

;; excl xs(Q1 xs ! ... ! Qm xs) -> all xs(Q1 xs -> ... -> Qm xs -> ~P) -> ~P

;; In unfolded form

;; (all xs(Q1 xs -> ... -> Qm xs -> bot) -> bot) ->
;;  all xs(Q1 xs -> ... -> Qm xs -> ~P) -> ~P

;; For simplicity take n=1

;;                    v: all x(Qs x -> P -> bot)  x  ws:Qs x  w:P
;;                    ----------------------------------------
;;                                            bot
;;                                         ---------
;;                                         Qs x -> bot
;;                                         ---------
;;      u:all x ~Qs x -> bot                 all x ~Qs x
;;      --------------------------------------------
;;                            bot
;;                          --------
;;                          P -> bot
;;                ---------------------------------
;;                all x(Qs x -> P -> bot) -> P -> bot
;;     --------------------------------------------
;;     excl Qs x -> all x(Qs x -> P -> bot) -> P -> bot

(define (make-excl-elim-neg-aconst nc-indicator n)
  (let* ((all-cr? (apply and-op (map not nc-indicator)))
	 (nc-indicator-string
	  (if  all-cr? ""
	       (apply string-append
		      (map (lambda (p) (if p "Nc" "Cr")) nc-indicator))))
	 (excl-elim-neg-name
	  (string-append "ExclElimNeg"
			 (number-to-alphabetic-string n)
			 nc-indicator-string))
	 (info (assoc excl-elim-neg-name THEOREMS)))
    (if
     info
     (theorem-name-to-aconst excl-elim-neg-name)
     (let* ((m (- (length nc-indicator) 1))
	    (nc-indicator-for-Qs (list-head nc-indicator m))
	    (nc-indicator-for-P (car (last-pair nc-indicator)))
	    (pvar-flas (make-fixed-pvar-formulas nc-indicator-for-Qs n))
	    (pvar (make-pvar (make-arity) -1
			     (if nc-indicator-for-P h-deg-one h-deg-zero)
			     n-deg-zero ""))
	    (pvar-fla (make-predicate-formula pvar))
	    (imp-fla ;Q1x -> ... -> Qmx -> bot
	     (apply mk-imp (append pvar-flas (list falsity-log))))
	    (xs (make-fixed-vars 1 n))
	    (excl-prem ;all x(Q1x -> ... -> Qmx -> bot)
	     (apply mk-all (append xs (list imp-fla))))
	    (all-imp-fla ;all x(Q1x -> ... -> Qmx -> P -> bot)
	     (apply mk-all
		    (append
		     xs (list (apply mk-imp
				     (append pvar-flas (list pvar-fla
							     falsity-log)))))))
	    (v (formula-to-new-avar all-imp-fla))
	    (ws (map formula-to-new-avar pvar-flas))
	    (w (formula-to-new-avar pvar-fla))
	    (intro-proof
	     (apply
	      mk-proof-in-intro-form
	      (append
	       xs ws (list (apply mk-proof-in-elim-form
				  (make-proof-in-avar-form v)
				  (append
				   (map make-term-in-var-form xs)
				   (map make-proof-in-avar-form
					(append ws (list w)))))))))
	    (u (formula-to-new-avar (make-negation-log excl-prem)))
	    (elim-proof (make-proof-in-imp-elim-form
			 (make-proof-in-avar-form u) intro-proof))
	    (proof (mk-proof-in-intro-form u v w elim-proof)))
       (set! OLD-COMMENT-FLAG COMMENT-FLAG)
       (set! COMMENT-FLAG #f)
       (add-theorem excl-elim-neg-name proof)
       (set! COMMENT-FLAG OLD-COMMENT-FLAG)
       (theorem-name-to-aconst excl-elim-neg-name)))))

;; (define aconst (make-excl-elim-neg-aconst '(#f #t #f) 1))
;; (pp (aconst-to-formula aconst))

;; (all alpha1_1((Pvar alpha1)_1 alpha1_1 -> (Pvar alpha1)^2 alpha1_1 -> bot) ->
;;  bot) -> 
;; all alpha1_1(
;;  (Pvar alpha1)_1 alpha1_1 -> (Pvar alpha1)^2 alpha1_1 -> Pvar -> bot) -> 
;; Pvar -> bot

;; The default case is make-exc-elim-aconst and uses stability.  It
;; takes positive integers m,n and returns an assumption constant for
;; exc-elimination w.r.t. n variables of types alpha1 to alphan.  Let
;; xs=x1...xn

;; exc xs(Q1 xs ! ... ! Qm xs) -> all xs(Q1 xs -> ... -> Qm xs -> P) -> P

;; In unfolded form

;; (all xs(Q1 xs -> ... -> Qm xs -> bot) -> bot) ->
;;  all xs(Q1 xs -> ... -> Qm xs -> P) -> P

;; For simplicity take n=m=1

;;                   v: all x(Qx -> P)  x  w2:Qx
;;                   ---------------------------
;;           w1: ~P                P
;;           -----------------------
;;                            bot
;;                            --- ->+ w2
;;                            ~Qx
;;                         ---------
;;   u:all x ~Qx -> bot    all x ~Qx
;;   -------------------------------
;;                            bot
;;                            --- ->+ w1
;;   Stab:~~P->P              ~~P
;;   ----------------------------
;;                    P

(define (make-exc-elim-aconst l-test m n)
  (let* ((exc-elim-name (string-append "Exc" (if l-test "l" "a") "Elim"
					(number-to-alphabetic-string m)
					(number-to-alphabetic-string n)))
	 (info (assoc exc-elim-name THEOREMS)))
    (if
     info
     (theorem-name-to-aconst exc-elim-name)
     (let* ((x (make-fixed-vars 1 n))
	    (Qs (make-fixed-pvars m n))
	    (parts (map (lambda (Q)
			  (apply make-predicate-formula
				 Q (map make-term-in-var-form x)))
			Qs))
	    (P (make-predicate-formula (make-pvar (make-arity)1 0 0 "")))
	    (stab (if l-test (proof-of-stab-log-at P) (proof-of-stab-at P)))
	    (bot (if l-test falsity-log falsity))
	    (w1 (formula-to-new-avar (make-imp P bot)))
	    (w2s (map formula-to-new-avar parts))
	    (u (formula-to-new-avar
		(make-imp
		 (apply mk-all
			(append x (list (apply mk-imp
					       (append parts (list bot))))))
		 bot)))
	    (v (formula-to-new-avar
		(apply mk-all
		       (append
			x (list (apply mk-imp (append parts (list P))))))))
	    (proof
	     (mk-proof-in-intro-form
	      u v (make-proof-in-imp-elim-form
		   stab
		   (make-proof-in-imp-intro-form
		    w1 (make-proof-in-imp-elim-form
			(make-proof-in-avar-form u)
			(apply
			 mk-proof-in-intro-form
			 (append
			  x w2s
			  (list
			   (make-proof-in-imp-elim-form
			    (make-proof-in-avar-form w1)
			    (apply mk-proof-in-elim-form
				   (append
				    (list (make-proof-in-avar-form v))
				    (map make-term-in-var-form x)
				    (map make-proof-in-avar-form
					 w2s)))))))))))))
       (set! OLD-COMMENT-FLAG COMMENT-FLAG)
       (set! COMMENT-FLAG #f)
       (add-theorem exc-elim-name proof)
       (set! COMMENT-FLAG OLD-COMMENT-FLAG)
       (theorem-name-to-aconst exc-elim-name)))))

;; We want to use (pair-elim) in interactive proofs, which replaces a
;; goal  all i Q i  by  all n,m Q(n@m)

(define (pair-elim)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (pair-intern num-goals proof maxgoal))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (pair-elim-intern num-goals proof maxgoal)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
         (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (goal-formula (goal-to-formula goal))
	 (free (formula-to-free goal-formula)))
    (if (not (and (all-form? goal-formula)
		  (star-form? (var-to-type (all-form-to-var goal-formula)))))
	(myerror "all form with a variable of pair type expected"
		 goal-formula))
    (apply use-with-intern
	   num-goals proof maxgoal
	   (make-proof-in-aconst-form
	    (all-pair-formula-to-pair-elim-aconst goal-formula))
	   (append (map make-term-in-var-form free)
		   (list DEFAULT-GOAL-NAME)))))

;; (admit) temporarily accepts the present goal, by turning it into a
;; global assumption.

(define (admit)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing")))))
    (set! PPROOF-STATE (admit-intern num-goals proof maxgoal))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (admit-intern num-goals proof maxgoal)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (ncvars (goal-to-ncvars goal))
	 (goal-formula (goal-to-formula goal))
	 (new-goal-formula (context-and-ncvars-and-formula-to-formula
			    context ncvars goal-formula))
	 (name (new-global-assumption-name "AdmitGA")))
    (add-global-assumption name new-goal-formula)
    (apply use-with-intern
	   num-goals proof maxgoal name (context-to-proofargs context))))

;; search
;; ======

;; Following Miller (J. Logic Computat. Vol 1, 1991) and Berger, work with
;; lists of sequents instead of single sequents; they all are Q-sequents
;; for the same prefix Q.  One then searches for a Q-substitution phi and
;; proofs of the phi-substituted sequents.  Intro-search takes the first
;; sequent and extends Q by all x1... .  It then calls select, which
;; selects (using or) a fitting clause.  If one is found, a new prefix Q'
;; (from raised-new-flex-vars) is formed, and the n (>= 0) new goals with
;; their clauses (and also all remaining sequents) are substituted with
;; raise o rho, where rho is the mgu.  For this constellation
;; intro-search is called again.  In case of success, one obtains a
;; Q'-substitution phi' and proofs on the phi' o raise o rho -substituted
;; new sequents.  Let phi := (raise o rho o phi') restricted Q_exists, and
;; take the first n proofs of these to build a proof of the phi-substituted
;; (first) sequent originally considered by intro-search.

;; Change to Miller and Berger: work with all ex all -prefixes instead of
;; using arbitrary prefixes.

;; Terminology:
;; elab-path   list of symbols 'left or 'right
;; elab-list   list of formulas, variables and symbols 'left or 'right
;; elim-list   list of formulas, terms and symbols 'left or 'right
;; elim-items  list of proofs, terms and symbols 'left or 'right
;; elims       either elim-list or elim-items

;; elab-paths are needed for search in case conjunctions are present.

(define (formula-to-elab-paths formula)
  (case (tag formula)
    ((atom predicate ex) '(()))
    ((imp) (formula-to-elab-paths (imp-form-to-conclusion formula)))
    ((impnc) (formula-to-elab-paths (impnc-form-to-conclusion formula)))
    ((and) (append (map (lambda (l) (cons 'left l))
			(formula-to-elab-paths (and-form-to-left formula)))
		   (map (lambda (l) (cons 'right l))
			(formula-to-elab-paths (and-form-to-right formula)))))
    ((all) (formula-to-elab-paths (all-form-to-kernel formula)))
    ((allnc) (formula-to-elab-paths (allnc-form-to-kernel formula)))
    (else (myerror "formula-to-elab-paths" "formula expected" formula))))

(define (elab-list-to-free elab-list)
  (if (null? elab-list)
      '()
      (let ((x (car elab-list)))
	(cond
	 ((formula-form? x)
	  (union (formula-to-free x) (elab-list-to-free (cdr elab-list))))
	 ((var-form? x) (remove x (elab-list-to-free (cdr elab-list))))
	 ((eq? 'left x) (elab-list-to-free (cdr elab-list)))
	 ((eq? 'right x) (elab-list-to-free (cdr elab-list)))
	 (else (myerror "elab-list-to-free" "elab-list item expected" x))))))

;; elim-list is used to construct a proof; it is obtained by substituting
;; in all variables and formulas, and leaving out the last (goal-)
;; formula

(define (elab-list-to-elim-list elab-list subst)
  (do ((l elab-list (cdr l))
       (res
	'()
	(let ((x (car l)))
	  (cond
	   ((formula-form? x)
	    (cons (formula-substitute-and-beta0-nf x subst) res))
	   ((var-form? x)
	    (cons (term-substitute (make-term-in-var-form x) subst) res))
	   ((eq? 'left x) (cons 'left res))
	   ((eq? 'right x) (cons 'right res))
	   (else (myerror
		  "elab-list-to-elim-list" "elab-list item expected" x))))))
      ((null? (cdr l)) (reverse res))))

(define (elim-list-to-formulas elim-list)
  (do ((l elim-list (cdr l))
       (res '() (if (formula-form? (car l)) (cons (car l) res) res)))
      ((null? l) (reverse res))))

(define (formula-and-elims-to-t-deg-ok? formula . elims)
  (or
   (null? elims)
   (let ((first (car elims))
	 (rest (cdr elims)))
     (case (tag formula)
       ((atom predicate ex) #t)
       ((imp)
	(if (or (formula-form? first) (proof-form? first))
	    (apply formula-and-elims-to-t-deg-ok?
		   (imp-form-to-conclusion formula) rest)
	    (myerror
	     "formula-and-elims-to-t-deg-ok?" "formula or proof expected"
	     first)))
       ((impnc)
	(if (or (formula-form? first) (proof-form? first))
	    (apply formula-and-elims-to-t-deg-ok?
		   (impnc-form-to-conclusion formula) rest)
	    (myerror
	     "formula-and-elims-to-t-deg-ok?" "formula or proof expected"
	     first)))
       ((and)
	(cond ((eq? 'left first)
	       (apply formula-and-elims-to-t-deg-ok?
		      (and-form-to-left formula) rest))
	      ((eq? 'right first)
	       (apply formula-and-elims-to-t-deg-ok?
		      (and-form-to-right formula) rest))
	      (else
	       (myerror
		"formula-and-elims-to-t-deg-ok?" "left or right expected"
		first))))
       ((all)
	(let ((var (all-form-to-var formula))
	      (kernel (all-form-to-kernel formula)))
	  (if (term-form? first)
	      (and
	       (not (and (t-deg-one? (var-to-t-deg var))
			 (not (synt-total? first))))
	       (apply formula-and-elims-to-t-deg-ok? kernel rest))
	      (myerror "formula-and-elims-to-t-deg-ok?" "term expected"
		       first))))
       ((allnc)
	(let ((var (allnc-form-to-var formula))
	      (kernel (allnc-form-to-kernel formula)))
	  (if (term-form? first)
	      (and
	       (not (and (t-deg-one? (var-to-t-deg var))
			 (not (synt-total? first))))
	       (apply formula-and-elims-to-t-deg-ok? kernel rest))
	      (myerror "formula-and-elims-to-t-deg-ok?" "term expected"
		       first))))
       (else (myerror "formula-and-elims-to-t-deg-ok?" "formula expected"
		      formula))))))

(define (formula-and-elab-path-to-renamed-elab-list
	 formula elab-path used-vars)
  (case (tag formula)
    ((atom predicate ex) (list formula))
    ((imp)
     (cons (imp-form-to-premise formula)
	   (formula-and-elab-path-to-renamed-elab-list
	    (imp-form-to-conclusion formula)
	    elab-path used-vars)))
    ((impnc)
     (cons (impnc-form-to-premise formula)
	   (formula-and-elab-path-to-renamed-elab-list
	    (impnc-form-to-conclusion formula)
	    elab-path used-vars)))
    ((and)
     (if
      (pair? elab-path)
      (cond
       ((eq? 'left (car elab-path))
	(cons 'left (formula-and-elab-path-to-renamed-elab-list
		     (and-form-to-left formula)
		     (cdr elab-path) used-vars)))
       ((eq? 'right (car elab-path))
	(cons 'right (formula-and-elab-path-to-renamed-elab-list
		      (and-form-to-right formula)
		      (cdr elab-path) used-vars)))
       (else
	(myerror
	 "formula-and-elab-path-to-renamed-elab-list" "elab-path item expected"
	 (car elab-path))))
      (myerror
       "formula-and-elab-path-to-renamed-elab-list" "elab-path empty for"
       formula)))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (info (member var used-vars))
	    (new-var (if info (var-to-new-var var) var))
	    (new-kernel
	     (if info
		 (formula-subst kernel var (make-term-in-var-form new-var))
		 kernel)))
       (cons new-var (formula-and-elab-path-to-renamed-elab-list
		      new-kernel elab-path (cons new-var used-vars)))))
    ((allnc)
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (info (member var used-vars))
	    (new-var (if info (var-to-new-var var) var))
	    (new-kernel
	     (if info
		 (formula-subst kernel var (make-term-in-var-form new-var))
		 kernel)))
       (cons new-var (formula-and-elab-path-to-renamed-elab-list
		      new-kernel elab-path (cons new-var used-vars)))))
    (else (myerror
	   "formula-and-elab-path-to-renamed-elab-list" "formula expected"
	   formula))))

(define (elab-list-to-vars elab-list)
  (do ((l elab-list (cdr l))
       (res '() (if (var-form? (car l)) (cons (car l) res) res)))
      ((null? l) (reverse res))))

(define (elab-list-item-to-string x)
  (cond
   ((var-form? x) (var-to-string x))
   ((formula-form? x) (formula-to-string x))
   ((eq? 'left x) "left")
   ((eq? 'right x) "right")
   (else (myerror "elab-list-to-string" "elab-list item expected" x))))

(define (elab-list-to-string elab-list)
  (do ((l (cdr elab-list) (cdr l))
       (res (elab-list-item-to-string (car elab-list))
	    (string-append res ", " (elab-list-item-to-string (car l)))))
      ((null? l) (string-append "(" res ")"))))

(define (elim-list-item-to-string x)
  (cond
   ((term-form? x) (term-to-string x))
   ((formula-form? x) (formula-to-string x))
   ((eq? 'left x) "left")
   ((eq? 'right x) "right")
   (else
    (myerror "elim-list-to-string" "elim-list item expected" x))))

(define (elim-list-to-string elim-list)
  (do ((l (cdr elim-list) (cdr l))
       (res (elim-list-item-to-string (car elim-list))
	    (string-append res ", " (elim-list-item-to-string
				     (car l)))))
      ((null? l) (string-append "(" res ")"))))

;; A clause has the form (leaf elab-path m), where elab-path is a list
;; of symbols left or right, giving the direction in case the formula
;; of leaf is a conjunction.  m is the multiplicity for using this clause.

(define (make-clause leaf elab-path m)
  (list leaf elab-path m))

(define clause-to-leaf car)
(define clause-to-elab-path cadr)
(define clause-to-mult caddr)

(define (display-clause clause n i)
  (display-comment (make-string n #\.)) (display "Clause ")
  (display i) (display ": ") (df (proof-to-formula (clause-to-leaf clause)))
  (display " (") (display (clause-to-mult clause)) (display " times)")
  (newline))

(define (display-clauses clauses n)
  (do ((l clauses (cdr l))
       (i 1 (+ 1 i)))
      ((null? l))
    (display-clause (car l) n i)))

(define (clause-substitute clause subst)
  (make-clause (proof-substitute (clause-to-leaf clause) subst)
	       (clause-to-elab-path clause)
	       (clause-to-mult clause)))

(define (clauses-substitute clauses subst)
  (map (lambda (clause) (clause-substitute clause subst)) clauses))

(define (clause-substitute-and-beta0-nf clause subst)
  (make-clause (proof-substitute-and-beta0-nf (clause-to-leaf clause) subst)
	       (clause-to-elab-path clause)
	       (clause-to-mult clause)))

(define (clauses-substitute-and-beta0-nf clauses subst)
  (map (lambda (clause) (clause-substitute-and-beta0-nf clause subst))
       clauses))

(define (leaf-with-mult-to-clauses leaf-with-mult)
  (let* ((leaf (car leaf-with-mult))
	 (mult (cadr leaf-with-mult))
	 (formula (unfold-formula (normalize-formula (proof-to-formula leaf))))
	 (elab-paths (formula-to-elab-paths formula)))
    (map (lambda (elab-path) (make-clause leaf elab-path mult)) elab-paths)))

;; A sequent has the form (goal clause1 ...).

(define (make-sequent goal . clauses)
  (cons goal clauses))

(define sequent-to-goal car)
(define sequent-to-clauses cdr)

(define (display-sequent sequent n i)
  (display-comment (make-string n #\.)) (display "Sequent ")
  (display i) (display ": ") (df (sequent-to-goal sequent))
  (display " from ") (newline)
  (display-clauses (sequent-to-clauses sequent) (+ n 11)))

(define (display-sequents sequents n)
  (do ((l sequents (cdr l))
       (i 1 (+ 1 i)))
      ((null? l))
    (display-sequent (car l) n i)))

(define (sequent-substitute sequent subst)
  (apply make-sequent
	 (formula-substitute (sequent-to-goal sequent) subst)
	 (clauses-substitute (sequent-to-clauses sequent) subst)))

(define (sequents-substitute sequents subst)
  (map (lambda (sequent) (sequent-substitute sequent subst)) sequents))

(define (sequent-substitute-and-beta0-nf sequent subst)
  (apply make-sequent
	 (formula-substitute-and-beta0-nf
	  (sequent-to-goal sequent) subst)
	 (clauses-substitute-and-beta0-nf
	  (sequent-to-clauses sequent) subst)))

(define (sequents-substitute-and-beta0-nf sequents subst)
  (map (lambda (sequent) (sequent-substitute-and-beta0-nf sequent subst))
       sequents))

;; (search m '(name1 m1) '(name2 m2) ...) expects for m a default value
;; for multiplicity (i.e. how often assumptions are to be used), for
;; name1 ...
;; - numbers of hypotheses from the present context or
;; - names for theorems or global assumptions,
;; and for m1 m2 ... a multiplicity (positive integer for global
;; assumptions or theorems).  A search is started for a proof of the goal
;; formula from the given hypotheses with the given multiplicities and in
;; addition from the other hypotheses (but not any other global
;; assumptions or theorems) with m or mult-default.  To exclude a
;; hypothesis from being tried, list it with multiplicity 0.

;; In case existential quantifiers are present, we add appropriate
;; existence introduction and elimination axioms as additional clauses.
;; Then non-termination may occur; we therefore in this case bound the
;; number of applications of elim-search.  We use a flag ex? to indicate
;; whether the counter needs to be used.

(define ELIM-SEARCH-BOUND 100)
(define ELIM-SEARCH-COUNTER 0)

;; auto does iterated search automatically.  Its arguments (possibly
;; empty) consist of a multiplicity and theorem or global assumption
;; names, each with its individual multiplicity (a positive integer).
;; From these and the local context clauses are determined, and with
;; these intro-search is called.  If it returns #f, the automated
;; search terminates and the unsolved goal is displayed.  If it returns
;; a true value, a new search is started, with the same multiplicity
;; and given leaves.

(define (mult-and-given-leaves-with-mult-to-ex-flag-and-search-result
	 num-goals proof maxgoal . x)
  (set! ELIM-SEARCH-COUNTER ELIM-SEARCH-BOUND)
  (let* ((m (if (null? x) mult-default
		(let ((first (car x)))
		  (if (and (integer? first) (positive? first)) first
		      (myerror "search" "positive integer expected" first)))))
	 (rest (if (null? x)
		   '()
		   (cdr x)))
	 (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (sig-vars (context-to-vars context)) ;signature variables
	 (given-leaves-with-mult
	  (do ((l rest (cdr l))
	       (res
		'()
		(let ((z (car l)))
		  (if
		   (and (list? z) (= 2 (length z)))
		   (let ((entry (car z))
			 (mult (cadr z)))
		     (if
		      (and (integer? mult) (not (negative? mult)))
		      (cons
		       (list (cond
			      ((and (integer? entry) (positive? entry))
			       (make-proof-in-avar-form
				(list-ref avars (- entry 1))))
			      ((and (string? entry)
				    (assoc entry (append GLOBAL-ASSUMPTIONS
							 THEOREMS)))
			       (if
				(zero? mult)
				(myerror "search"
					 "positive multiplicity expected for"
					 entry)
				(make-proof-in-aconst-form
				 (cadr (assoc entry (append GLOBAL-ASSUMPTIONS
							    THEOREMS))))))
			      (else
			       (myerror
				"search" "hyp-number or aconst-name expected"
				entry)))
			     mult)
		       res)
		      (myerror "search" "non-negative integer expected" mult)))
		   (myerror "search" "list (name mult) expected" z)))))
	      ((null? l) (reverse res))))
	 (leaves-with-mult
	  (do ((l avars (cdr l))
	       (i 1 (+ i 1))
	       (res
		(reverse given-leaves-with-mult)
		(let* ((avar (car l))
		       (info (assoc i rest)))
		  (if info
		      res
		      (cons (list (make-proof-in-avar-form avar) m) res)))))
	      ((null? l) (reverse res))))
	 (goal-formula (goal-to-formula goal))
	 (clause-formulas (map proof-to-formula
			       (map car leaves-with-mult)))
	 (pos-ex-list
	  (remove-duplicates-wrt
	   classical-formula=?
	   (apply append
		  (formula-to-positive-existential-subformulas
		   goal-formula)
		  (map formula-to-negative-existential-subformulas
		       clause-formulas))))
	 (neg-ex-list
	  (remove-duplicates-wrt
	   classical-formula=?
	   (apply append
		  (formula-to-negative-existential-subformulas
		   goal-formula)
		  (map formula-to-positive-existential-subformulas
		       clause-formulas))))
	 (ex-list (remove-duplicates-wrt classical-formula=?
					 (append pos-ex-list neg-ex-list)))
	 (ex? (pair? ex-list))
	 (ex-intro-leaves-with-mult
	  (map
	   (lambda (f)
	     (cond
	      ((ex-form? f) (list (make-proof-in-aconst-form
				   (ex-formula-to-ex-intro-aconst f))
				  m))
	      ((and (quant-form? f)
		    (memq (quant-form-to-quant f)
			  '(exd exl exr exnc exdt exlt exrt exnct)))
	       (list (make-proof-in-aconst-form
		      (number-and-idpredconst-to-intro-aconst
		       0 (predicate-form-to-predicate f)))
		     m))
	      (else
	       (myerror
		"mult-and-given-leaves-with-mult-to-ex-flag-and-search-result"
		"existential formula expected" f))))
	   pos-ex-list))
	 (ex-elim-leaves-with-mult
	  (do ((l (reverse neg-ex-list) (cdr l))
	       (res
		'()
		(append
		 (map
		  (lambda (f)
		    (cond
		     ((ex-form? (car l))
		      (list (make-proof-in-aconst-form
			     (ex-formula-and-concl-to-ex-elim-aconst
			      (car l) f))
			    m))
		     ((and (quant-form? (car l))
			   (memq (quant-form-to-quant (car l))
				 '(exd exl exr exnc exdt exlt exrt exnct)))
		      (list (make-proof-in-aconst-form
			     (imp-formulas-to-elim-aconst
			      (make-imp (car l) f)))
			    m))
		     (else
		      (myerror
		       "mult-and-given-leaves-with-mult-to-ex-flag-and-search-result"
		       "existential formula expected" (car l)))))
		  (remove-wrt classical-formula=? (car l) ex-list))
		 res)))
	      ((null? l) res)))
	 (clauses
	  (apply append
		 (map (lambda (lwm) (leaf-with-mult-to-clauses lwm))
		      (append leaves-with-mult
			      ex-intro-leaves-with-mult
			      ex-elim-leaves-with-mult)))))
    (list ex? (intro-search m
			    (normalize-formula goal-formula)
			    clauses
			    '() ;no sequents initially
			    sig-vars
			    '() ;no flex-vars initially
			    '() ;no forb-vars initially
			    ex?
			    0))))

(define (search . mult-and-aconst-names-with-mult)
  (check-mult-and-aconst-names-with-mult mult-and-aconst-names-with-mult)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing"))))
	 (search-result (apply search-intern
			       num-goals proof maxgoal
			       mult-and-aconst-names-with-mult)))
    (if (not search-result)
	(begin (display-comment "no proof found")
	       (if COMMENT-FLAG (newline)))
	(begin
	  (set! PPROOF-STATE search-result)
	  (pproof-state-history-push PPROOF-STATE)
	  (if
	   COMMENT-FLAG
	   (begin
	     (display-comment "ok, " DEFAULT-GOAL-NAME "_"
			      (number-to-string number)
			      " is proved by minimal quantifier logic.")
	     (if (null? (pproof-state-to-num-goals))
		 (begin (display "  Proof finished.") (newline))
		 (begin (display "  The active goal now is") (newline)
			(display-num-goal
			 (car (pproof-state-to-num-goals)))))))))))

(define (search-intern
	 num-goals proof maxgoal . mult-and-aconst-names-with-mult)
  (let* ((num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (goal (num-goal-to-goal num-goal))
 	 (ex-flag-and-search-result
	  (apply mult-and-given-leaves-with-mult-to-ex-flag-and-search-result
		 num-goals proof maxgoal mult-and-aconst-names-with-mult))
	 (ex? (car ex-flag-and-search-result))
	 (prev (cadr ex-flag-and-search-result)))
    (if (not prev)
	#f
	(let* ((subst (car prev))
	       (proofs (cdr prev))
	       (proof1 (car proofs)))
	  (make-pproof-state (cdr num-goals)
			     (goal-subst proof goal proof1)
			     maxgoal)))))

(define (check-mult-and-aconst-names-with-mult mult-and-aconst-names-with-mult)
  (or
   (null? mult-and-aconst-names-with-mult)
   (let ((first (car mult-and-aconst-names-with-mult))
	 (rest (cdr mult-and-aconst-names-with-mult)))
     (if (not (and (integer? first) (positive? first)))
	 (myerror "positive integer (multiplicity) expected" first))
     (for-each (lambda (z)
		 (if (not (and (list? z) (= 2 (length z))))
		     (myerror "list of length 2 expected" z))
		 (let ((entry (car z))
		       (mult (cadr z)))
		   (if (not (and (string? entry)
				 (assoc entry (append GLOBAL-ASSUMPTIONS
						      THEOREMS))))
		       (myerror "aconst-name expected" entry))
		   (if (not (and (integer? mult) (positive? mult)))
		       (myerror "positive multiplicity expected" mult))))
	       rest))))

;; It can be convenient to automate (the easy cases of an) interactive
;; proof development by iterating \texttt{search} as long as it is
;; successful in finding a proof.  Then the first goal where it failed
;; is presented as the new goal.

(define (auto . mult-and-aconst-names-with-mult)
  (check-mult-and-aconst-names-with-mult mult-and-aconst-names-with-mult)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (auto-result (apply auto-intern
			     num-goals proof maxgoal
			     mult-and-aconst-names-with-mult)))
    (set! PPROOF-STATE auto-result)
    (pproof-state-history-push PPROOF-STATE)
    (if
     COMMENT-FLAG
     (if (null? (pproof-state-to-num-goals))
	 (begin (display-comment "Proof finished.") (newline))
	 (begin (display-comment "  The active goal now is") (newline)
		(display-num-goal (car (pproof-state-to-num-goals))))))))

(define (auto-intern num-goals proof maxgoal . mult-and-aconst-names-with-mult)
  (do ((prev-res (list num-goals proof maxgoal) res)
       (res (apply search-intern
		   num-goals proof maxgoal mult-and-aconst-names-with-mult)
	    (apply search-intern (append res
					 mult-and-aconst-names-with-mult))))
      ((or (not res) (null? (pproof-state-to-num-goals res)))
       (display-comment)
       (if (not res)
	   prev-res
	   res))))

;; Goal: preprocess formulas to remove existential quantifiers as far
;; as possible, before employing proof search.  This is done by
;; searchex, involving the procedures formula-to-ex-red-formula
;; and formula-to-proof-of-ex-red-formula-imp-formula.

;; Experience with toy examples: searchex is no better than search.
;; Moreover, the proofs found by search are much shorter and clearer
;; than those found by searchex.  This remains true after normalization,
;; which does not work well when ex-elim axioms are used.
;; But more experience is needed.

(define (searchex . mult-and-aconst-names-with-mult)
  (check-mult-and-aconst-names-with-mult mult-and-aconst-names-with-mult)
  (set! ELIM-SEARCH-COUNTER ELIM-SEARCH-BOUND)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number
	  (num-goal-to-number
	   (if (pair? num-goals) (car num-goals) (myerror "goal missing"))))
	 (search-result (apply searchex-intern
			       num-goals proof maxgoal
			       mult-and-aconst-names-with-mult)))
    (if (not search-result)
	(begin (display-comment "no proof found")
	       (if COMMENT-FLAG (newline)))
	(begin
	  (set! PPROOF-STATE search-result)
	  (pproof-state-history-push PPROOF-STATE)
	  (if
	   COMMENT-FLAG
	   (begin
	     (display-comment "ok, " DEFAULT-GOAL-NAME "_"
			      (number-to-string number)
			      " is proved by minimal quantifier logic.")
	     (if (null? (pproof-state-to-num-goals))
		 (begin (display "  Proof finished.") (newline))
		 (begin (display "  The active goal now is") (newline)
			(display-num-goal
			 (car (pproof-state-to-num-goals)))))))))))

(define (searchex-intern
	 num-goals proof maxgoal . mult-and-aconst-names-with-mult)
  (set! ELIM-SEARCH-COUNTER ELIM-SEARCH-BOUND)
  (let* ((m (if (null? mult-and-aconst-names-with-mult) mult-default
		(let ((first (car mult-and-aconst-names-with-mult)))
		  (if (and (integer? first) (positive? first)) first
		      (myerror
		       "searchex" "positive integer expected" first)))))
	 (rest (if (null? mult-and-aconst-names-with-mult) '()
		   (cdr mult-and-aconst-names-with-mult)))
	 (num-goal
	  (if (pair? num-goals) (car num-goals) (myerror "goal missing")))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (sig-vars (context-to-vars context)) ;signature variables
	 (given-leaves-with-mult ;given as arguments to searchex
	  (do ((l rest (cdr l))
	       (res
		'()
		(let ((z (car l)))
		  (if
		   (and (list? z) (= 2 (length z)))
		   (let ((entry (car z))
			 (mult (cadr z)))
		     (if
		      (and (integer? mult) (not (negative? mult)))
		      (cons
		       (list (cond
			      ((and (integer? entry) (positive? entry))
			       (make-proof-in-avar-form
				(list-ref avars (- entry 1))))
			      ((and (string? entry)
				    (assoc entry (append GLOBAL-ASSUMPTIONS
							 THEOREMS)))
			       (if
				(zero? mult)
				(myerror "search"
					 "positive multiplicity expected for"
					 entry)
				(make-proof-in-aconst-form
				 (cadr (assoc entry (append GLOBAL-ASSUMPTIONS
							    THEOREMS))))))
			      (else
			       (myerror
				"searchex" "hyp-number or aconst-name expected"
				entry)))
			     mult)
		       res)
		      (myerror
		       "searchex" "non-negative integer expected" mult)))
		   (myerror "searchex" "list (name mult) expected" z)))))
	      ((null? l) (reverse res))))
	 (leaves-with-mult ;add avars not explicitly given
	  (do ((l avars (cdr l))
	       (i 1 (+ i 1))
	       (res
		(reverse given-leaves-with-mult)
		(let* ((avar (car l))
		       (info (assoc i rest)))
		  (if info
		      res
		      (cons (list (make-proof-in-avar-form avar) m) res)))))
	      ((null? l) (reverse res))))
	 (goal-formula (goal-to-formula goal))
	 (clause-formulas (map proof-to-formula (map car leaves-with-mult)))
	 (ex-red-goal-formula (formula-to-ex-red-formula goal-formula))
	 (ex-red-clause-formulas
	  (map formula-to-ex-red-formula clause-formulas))
	 (vars-and-kernel-list
	  (map ex-form-to-vars-and-final-kernel ex-red-clause-formulas))
	 (varss (map car vars-and-kernel-list))
	 (kernels (map cadr vars-and-kernel-list))
	 (test (and (pair? ex-red-clause-formulas)
		    (or (pair? (apply intersection varss))
			(pair? (intersection
				(apply append varss)
				(formula-to-free goal-formula))))))
	 (new-varss
	  (if test
	      (map (lambda (vars) (map var-to-new-var vars)) varss)
	      varss))
	 (new-kernels
	  (if test
	      (do ((l1 varss (cdr l1))
		   (l2 kernels (cdr l2))
		   (l3 new-varss (cdr l3))
		   (res '() (let* ((vars (car l1))
				   (kernel (car l2))
				   (new-vars (car l3))
				   (subst (map list
					       vars
					       (map make-term-in-var-form
						    new-vars))))
			      (cons (formula-substitute kernel subst) res))))
		  ((null? l1) (reverse res)))
	      kernels))
	 (ex-red-leaves-with-mult
	  (map (lambda (kernel lwm)
		 (list (make-proof-in-avar-form
			(formula-to-new-avar kernel DEFAULT-AVAR-NAME))
		       (cadr lwm)))
	       new-kernels leaves-with-mult))
	 (pos-ex-list
	  (remove-duplicates-wrt
	   classical-formula=?
	   (apply append
		  (formula-to-positive-existential-subformulas
		   ex-red-goal-formula)
		  (map formula-to-negative-existential-subformulas
		       new-kernels))))
	 (neg-ex-list
	  (remove-duplicates-wrt
	   classical-formula=?
	   (apply append
		  (formula-to-negative-existential-subformulas
		   ex-red-goal-formula)
		  (map formula-to-positive-existential-subformulas
		       new-kernels))))
	 (ex-list (remove-duplicates-wrt classical-formula=?
					 (append pos-ex-list neg-ex-list)))
	 (ex? (pair? ex-list))
	 (ex-intro-leaves-with-mult
	  (map (lambda (f) (list (make-proof-in-aconst-form
				  (ex-formula-to-ex-intro-aconst f))
				 m))
	       pos-ex-list))
	 (ex-elim-leaves-with-mult
	  (do ((l (reverse neg-ex-list) (cdr l))
	       (res
		'()
		(append
		 (map
		  (lambda (f)
		    (list (make-proof-in-aconst-form
			   (ex-formula-and-concl-to-ex-elim-aconst (car l) f))
			  m))
		  (remove-wrt classical-formula=? (car l) ex-list))
		 res)))
	      ((null? l) res)))
	 (clauses
	  (apply append
		 (map (lambda (lwm) (leaf-with-mult-to-clauses lwm))
		      (append ex-red-leaves-with-mult
			      ex-intro-leaves-with-mult
			      ex-elim-leaves-with-mult))))
	 (prev (intro-search
		m
		(normalize-formula ex-red-goal-formula)
		clauses
		'() ;no sequents initially
		sig-vars
		'() ;no flex-vars initially
		'() ;no forb-vars initially
		ex?
		0)))
    (if
     (not prev) #f
     (let* ((found-proof1 (cadr prev))
	    (proof1 ;of G
	     (make-proof-in-imp-elim-form
	      (formula-to-proof-of-ex-red-formula-imp-formula goal-formula)
	      (apply
	       mk-proof-in-elim-form
	       (apply
		ex-formulas-and-concl-to-ex-elim-proof
		(append
		 ex-red-clause-formulas (list ex-red-goal-formula)))
	       (append
		(map (lambda (fla lwm)
		       (make-proof-in-imp-elim-form
			(formula-to-proof-of-formula-imp-ex-red-formula fla)
			(car lwm)))
		     clause-formulas leaves-with-mult)
		(list
		 (apply
		  mk-proof-in-intro-form
		  (append
		   (apply append new-varss)
		   (map (lambda (lwm) (proof-in-avar-form-to-avar (car lwm)))
			ex-red-leaves-with-mult)
		   (list found-proof1)))))))))
       (make-pproof-state (cdr num-goals)
			  (goal-subst proof goal proof1)
			  maxgoal)))))

(define mult-default 2)

(define VERBOSE-SEARCH #f)

(define (display-prefix sig-vars flex-vars forb-vars)
  (if (pair? (append sig-vars flex-vars forb-vars))
      (begin (display " under")
	     (if (pair? sig-vars)
		 (begin (display " all ")
			(display (vars-to-comma-string sig-vars))))
	     (if (pair? flex-vars)
		 (begin (display " ex ")
			(display (vars-to-comma-string flex-vars))))
	     (if (pair? forb-vars)
		 (begin (display " all ")
			(display (vars-to-comma-string forb-vars)))))))

;; intro-search yields either #f, indicating that not all of (clauses ->
;; goal, sequents) can be proved, or else a substitution phi and proofs
;; of all of (clauses -> goal, sequents) under phi.

;; Note that sig-vars is needed, for renaming of universal quantifiers in goals.

(define (intro-search
	 m goal clauses sequents sig-vars flex-vars forb-vars ex? n)
  (case (tag goal)
    ((atom)
     (if VERBOSE-SEARCH
	 (begin (display-comment (make-string n #\.))
		(display "Goal ") (df goal)
		(display-prefix sig-vars flex-vars forb-vars)
		(newline)))
     (if
      (classical-formula=? truth (normalize-formula goal)) ;04-01-08 norm added
      (if (null? sequents)
	  (cons empty-subst
		(list (make-proof-in-aconst-form truth-aconst)))
	  (let* ((first-sequent (car sequents))
		 (new-goal (sequent-to-goal first-sequent))
		 (new-clauses (sequent-to-clauses first-sequent))
		 (prev (intro-search
			m new-goal new-clauses (cdr sequents)
			sig-vars flex-vars forb-vars ex? (+ n 1))))
	    (if
	     (not prev)
	     (begin (if VERBOSE-SEARCH
			(begin (display-comment (make-string n #\.))
			       (display "Failed") (newline)))
		    #f)
	     (cons (car prev)
		   (cons (make-proof-in-aconst-form truth-aconst)
			 (cdr prev))))))
      (select clauses '() (normalize-formula goal) ;normalize-formula added
	      sequents sig-vars flex-vars forb-vars ex? n)))
    ((predicate ex)
     (if VERBOSE-SEARCH
	 (begin (display-comment (make-string n #\.))
		(display "Goal ") (df goal)
		(display-prefix sig-vars flex-vars forb-vars)
		(newline)))
     (select clauses '() (normalize-formula goal) ;normalize-formula added
	     sequents sig-vars flex-vars forb-vars ex? n))
    ((imp)
     (let* ((formula (imp-form-to-premise goal))
	    (avar (formula-to-new-avar formula DEFAULT-AVAR-NAME))
	    (leaf (make-proof-in-avar-form avar))
	    (elab-paths (formula-to-elab-paths formula))
	    (new-clauses
	     (map (lambda (path) (list leaf path m)) elab-paths))
	    (prev
	     (intro-search m (imp-form-to-conclusion goal)
			   (append new-clauses clauses)
			   sequents sig-vars flex-vars forb-vars ex? n)))
       (if
	(not prev)
	#f
	(let* ((subst (car prev))
	       (proofs (cdr prev))
	       (proof (car proofs))
	       (new-proof (make-proof-in-imp-intro-form
			   (proof-in-avar-form-to-avar
			    (proof-substitute-and-beta0-nf
			     (make-proof-in-avar-form avar) subst))
			   proof)))
	  (cons subst (cons new-proof (cdr proofs)))))))
    ((impnc)
     (let* ((formula (impnc-form-to-premise goal))
	    (avar (formula-to-new-avar formula DEFAULT-AVAR-NAME))
	    (leaf (make-proof-in-avar-form avar))
	    (elab-paths (formula-to-elab-paths formula))
	    (new-clauses
	     (map (lambda (path) (list leaf path m)) elab-paths))
	    (prev
	     (intro-search m (impnc-form-to-conclusion goal)
			   (append new-clauses clauses)
			   sequents sig-vars flex-vars forb-vars ex? n)))
       (if
	(not prev)
	#f
	(let* ((subst (car prev))
	       (proofs (cdr prev))
	       (proof (car proofs))
	       (new-proof (make-proof-in-impnc-intro-form
			   (proof-in-avar-form-to-avar
			    (proof-substitute-and-beta0-nf
			     (make-proof-in-avar-form avar) subst))
			   proof)))
	  (cons subst (cons new-proof (cdr proofs)))))))
    ((and)
     (let* ((right-sequent
	     (apply make-sequent (and-form-to-right goal) clauses))
	    (prev (intro-search m (and-form-to-left goal)
				clauses (cons right-sequent sequents)
				sig-vars flex-vars forb-vars ex? n)))
       (if
	(not prev)
	#f
	(let* ((subst (car prev))
	       (proofs (cdr prev))
	       (left-proof (car proofs))
	       (right-proof (cadr proofs))
	       (new-proof (make-proof-in-and-intro-form
			   left-proof right-proof)))
	  (cons subst (cons new-proof (cddr proofs)))))))
    ((all)
     (let* ((var (all-form-to-var goal))
	    (kernel (all-form-to-kernel goal))
	    (info (member var (append sig-vars flex-vars forb-vars)))
	    (new-var (if info (var-to-new-var var) var))
	    (new-kernel
	     (if info
		 (formula-subst kernel var (make-term-in-var-form new-var))
		 kernel))
	    (prev
	     (if (null? flex-vars)
		 (intro-search
		  m new-kernel clauses sequents
		  (append sig-vars (list new-var)) '() forb-vars ex? n)
		 (intro-search
		  m new-kernel clauses sequents
		  sig-vars flex-vars (append forb-vars (list new-var))
		  ex? n))))
       (if
	(not prev)
	#f
	(let* ((subst (car prev))
	       (proofs (cdr prev))
	       (proof (car proofs))
	       (new-proof (make-proof-in-all-intro-form new-var proof)))
	  (cons subst (cons new-proof (cdr proofs)))))))
    ((allnc)
     (let* ((var (allnc-form-to-var goal))
	    (kernel (allnc-form-to-kernel goal))
	    (info (member var (append sig-vars flex-vars forb-vars)))
	    (new-var (if info (var-to-new-var var) var))
	    (new-kernel
	     (if info
		 (formula-subst kernel var (make-term-in-var-form new-var))
		 kernel))
	    (prev
	     (if (null? flex-vars)
		 (intro-search
		  m new-kernel clauses sequents
		  (append sig-vars (list new-var)) '() forb-vars ex? n)
		 (intro-search
		  m new-kernel clauses sequents
		  sig-vars flex-vars (append forb-vars (list new-var))
		  ex? n))))
       (if
	(not prev)
	#f
	(let* ((subst (car prev))
	       (proofs (cdr prev))
	       (proof (car proofs))
	       (new-proof (make-proof-in-allnc-intro-form new-var proof)))
	  (cons subst (cons new-proof (cdr proofs)))))))
    (else (myerror "intro-search" "formula expected" goal))))

(define (select clauses done prime-or-ex-goal sequents
		sig-vars flex-vars forb-vars ex? n)
  (if
   (null? clauses)
   #f
   (let* ((clause (car clauses))
	  (rest (cdr clauses))
	  (leaf (clause-to-leaf clause))
	  (elab-path (clause-to-elab-path clause))
	  (renamed-elab-list (formula-and-elab-path-to-renamed-elab-list
			      (unfold-formula
			       (normalize-formula (proof-to-formula leaf)))
			      elab-path (append sig-vars flex-vars forb-vars)))
	  (m (clause-to-mult clause))
	  (head (car (last-pair renamed-elab-list))))
     (or ;elim-search, provided mgu rho exists
      (if
       (not (or (and (atom-form? head) (atom-form? prime-or-ex-goal))
		(and (ex-form? head) (ex-form? prime-or-ex-goal))
		(and (predicate-form? head) (predicate-form? prime-or-ex-goal)
		     (predicate-equal?
		      (predicate-form-to-predicate head)
		      (predicate-form-to-predicate prime-or-ex-goal)))))
       #f
       (let* ((new-flex-vars (elab-list-to-vars renamed-elab-list))
	      (raised-new-flex-vars
	       (map (lambda (x)
		      (if (pair? forb-vars) ;then the type must be raised
			  (let* ((type (var-to-type x))
				 (t-deg (var-to-t-deg x))
				 (types (map var-to-type forb-vars))
				 (t-degs (map var-to-t-deg forb-vars))
				 (new-type
				  (apply mk-arrow
					 (append types (list type)))))
			    (if (zero? t-deg)
				(type-to-new-partial-var new-type)
				(if (< 0 (apply min t-degs))
				    (type-to-new-var new-type)
				    (myerror
				     "select" "partial variable expected"
				     x))))
			  x))
		    new-flex-vars))
	      (new-app-terms
	       (map (lambda (x) (apply mk-term-in-app-form
				       (make-term-in-var-form x)
				       (map make-term-in-var-form
					    forb-vars)))
		    raised-new-flex-vars))
	      (star (if (pair? forb-vars)
			(map list new-flex-vars new-app-terms)
			empty-subst))
	      (raised-head
	       (if (pair? forb-vars)
		   (formula-substitute-and-beta0-nf head star)
		   head))
	      (unif-results ;minimal commitment such that selected clause fits
	       (if (and (pattern? raised-head
				  (append flex-vars raised-new-flex-vars)
				  forb-vars)
			(pattern? prime-or-ex-goal
				  (append flex-vars raised-new-flex-vars)
				  forb-vars))
		   (let ((pattern-unify-result
			  (pattern-unify
			   sig-vars
			   (append flex-vars raised-new-flex-vars)
			   forb-vars
			   (list raised-head prime-or-ex-goal))))
		     (if pattern-unify-result
			 (list pattern-unify-result)
			 '()))
		   (begin
		     (if VERBOSE-SEARCH
			 (begin
			   (display-comment (make-string n #\.))
			   (display "Non-pattern encountered: ")
			   (if
			    (pattern? raised-head
				      (append flex-vars raised-new-flex-vars)
				      forb-vars)
			    (display (formula-to-string prime-or-ex-goal))
			    (display (formula-to-string raised-head)))
			   (newline)
			   (display-comment (make-string n #\.))
			   (display "under flex-vars ")
			   (display (vars-to-comma-string
				     (append flex-vars raised-new-flex-vars)))
			   (display " and forb-vars ")
			   (display (vars-to-comma-string forb-vars))
			   (newline)))
		     (huet-unifiers sig-vars
				    (append flex-vars raised-new-flex-vars)
				    forb-vars
				    (list raised-head prime-or-ex-goal))))))
	 (if VERBOSE-SEARCH
	     (begin (display-comment (make-string n #\.))
		    (display "Select ")
		    (df (proof-to-formula leaf))
		    (display " with elab-list ")
		    (display (elab-list-to-string renamed-elab-list))
		    (newline)))
	 (if VERBOSE-SEARCH
	     (if (pair? new-flex-vars)
		 (begin
		   (display-comment (make-string n #\.))
		   (if (pair? forb-vars)
		       (display "Raised new flex-vars ")
		       (display "New flex-vars "))
		   (display (vars-to-comma-string raised-new-flex-vars))
		   (newline))))
	 (select-unif unif-results done m leaf clause rest star
		      renamed-elab-list flex-vars sequents ex? n)))
      (select rest (append done (list clause)) prime-or-ex-goal
	      sequents sig-vars flex-vars forb-vars ex? n)))))

(define (select-unif unif-results done m leaf clause rest star
		     renamed-elab-list flex-vars sequents ex? n)
  (if
   (null? unif-results)
   (begin (if VERBOSE-SEARCH
	      (begin (display-comment (make-string n #\.))
		     (display "Unification fails") (newline)))
	  #f)
   (let* ((unif-res (car unif-results))
	  (rho (car unif-res))
	  (new-prefix (cdr unif-res))
	  (new-sig-vars (car new-prefix))
	  (new-flex-vars (cadr new-prefix))
	  (new-forb-vars (caddr new-prefix)))
     (if (and VERBOSE-SEARCH (not (equal? empty-subst rho)))
	 (begin (display-comment (make-string n #\.))
		(display "Unifier: ")
		(display (pp-subst rho))
		(apply display-prefix new-prefix)
		(newline)))
     (let* ((new-clauses (append
			  done
			  (if (< 1 m)
			      (cons (make-clause leaf
						 (clause-to-elab-path clause)
						 (- m 1))
				    rest)
			      rest)))
	    (star_o_rho (compose-substitutions-and-beta0-nf star rho))
	    (elim-list (elab-list-to-elim-list renamed-elab-list star_o_rho)))
       (if VERBOSE-SEARCH
	   (begin (if (pair? star_o_rho)
		      (begin
			(display-comment (make-string n #\.))
			(display "Star_o_rho: ")
			(display (pp-subst star_o_rho))
			(newline)))))
       (if
	(not (apply formula-and-elims-to-t-deg-ok?
		    (unfold-formula
		     (proof-to-formula leaf)) elim-list))
	(begin (if VERBOSE-SEARCH
		   (begin (display-comment (make-string n #\.))
			  (display "Failed: t-degs do not fit")
			  (newline)))
	       (select-unif
		(cdr unif-results) done m leaf clause rest star
		renamed-elab-list flex-vars sequents ex? n))
	(let ((prev
	       (elim-search
		rho flex-vars m
		(proof-substitute-and-beta0-nf leaf rho) elim-list
		(clauses-substitute-and-beta0-nf new-clauses star_o_rho)
		(sequents-substitute-and-beta0-nf sequents rho)
		star_o_rho new-sig-vars new-flex-vars new-forb-vars ex? n)))
	  (if (not prev)
	      (select-unif
	       (cdr unif-results) done m leaf clause rest star
	       renamed-elab-list flex-vars sequents ex? n)
	      (cons (restrict-substitution-to-args (car prev) flex-vars)
		    (cdr prev)))))))))

(define (elim-search rho flex-vars m leaf elim-list clauses sequents
		     star_o_rho sig-vars new-flex-vars forb-vars ex? n)
  (if
   (zero? ELIM-SEARCH-COUNTER)
   #f
   (let* ((formulas (elim-list-to-formulas elim-list))
	  (new-sequents
	   (append (map (lambda (g) (apply make-sequent g clauses))
			formulas)
		   sequents)))
     (if ex? (set! ELIM-SEARCH-COUNTER (- ELIM-SEARCH-COUNTER 1)))
     (if
      (null? new-sequents)
      (cons star_o_rho
	    (list (apply mk-proof-in-elim-form leaf elim-list)))
      (let* ((first-new-sequent (car new-sequents))
	     (goal (sequent-to-goal first-new-sequent))
	     (new-clauses (sequent-to-clauses first-new-sequent))
	     (prev (intro-search
		    m goal new-clauses (cdr new-sequents)
		    sig-vars new-flex-vars forb-vars ex? (+ n 1))))
	(if
	 (not prev)
	 (begin (if VERBOSE-SEARCH
		    (begin (display-comment (make-string n #\.))
			   (display "Failed") (newline)))
		#f)
	 (let* ((phiprime (car prev))
		(rho_o_phiprime
		 (compose-substitutions-and-beta0-nf rho phiprime))
		(phi (restrict-substitution-to-args rho_o_phiprime flex-vars))
		(new-leaf (proof-substitute-and-beta0-nf leaf phi))
		(proofs (cdr prev))
		(star_o_rho_o_phiprime
		 (compose-substitutions-and-beta0-nf star_o_rho phiprime))
		(elim-items-and-sequent-proofs
		 (do ((l elim-list (cdr l))
		      (l1 proofs (if (formula-form? (car l)) (cdr l1) l1))
		      (res '() (cond
				((formula? (car l)) (cons (car l1) res))
				((term-form? (car l))
				 (cons (term-substitute-and-beta0-nf
					(car l) star_o_rho_o_phiprime)
				       res))
				((or (eq? 'left (car l)) (eq? 'right (car l)))
				 (cons (car l) res))
				(else (myerror
				       "elim-search" "elim list item expected"
				       (car l))))))
		     ((null? l) (list (reverse res) l1))))
		(elim-items (car elim-items-and-sequent-proofs)))
	   (if (not (apply formula-and-elims-to-t-deg-ok?
			   (unfold-formula
			    (proof-to-formula new-leaf)) elim-items))
	       (begin (if VERBOSE-SEARCH
			  (begin (display-comment (make-string n #\.))
				 (display "Failed: t-degs do not fit")
				 (newline)))
		      #f)
	       (let* ((new-proof (apply mk-proof-in-elim-form
					new-leaf elim-items))
		      (sequent-proofs (cadr elim-items-and-sequent-proofs)))
		 (cons star_o_rho_o_phiprime
		       (cons new-proof sequent-proofs)))))))))))

