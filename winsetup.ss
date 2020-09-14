;; petite chez scheme "Add to path for shell use" should be checked
;; when you install petite chez scheme.

(load "src/list.scm")

(define (rdc xs)
  (if (= 2 (length xs))
      (list (car xs))
      (cons (car xs) (rdc (cdr xs)))))

(define (rac xs)
  (if (= 1 (length xs))
      (car xs)
      (rac (cdr xs))))

(define (chomp-tail str chars)
  (define (chomp-tail-aux char-list chars)
    (if (member (rac char-list) chars)
	(chomp-tail-aux (rdc char-list) chars)
	char-list))
  (apply string (chomp-tail-aux (string->list str) chars)))

(define (read-file filepath)
  (apply string
	 (let ((p (open-input-file filepath)))
	   (let f ((x (read-char p)))
	     (if (eof-object? x)
		 (begin (close-port p) '())
		 (cons x (f (read-char p))))))))

(define (write-file filepath str)
  (if (file-exists? filepath) (delete-file filepath))
  (let ((char-list (string->list str))
	(p (open-output-file filepath)))
    (let f ((ls char-list))
      (if (not (null? ls))
	  (begin (write-char (car ls) p)
		 (f (cdr ls)))))
    (close-port p)))

(define (replace-path-sep path)
  (string-replace-substring path "\\" "/"))

;(define (escape-win-chars str)
;   (string-replace-substring str "\\" "\\\\"))

;; get the path to petite.exe
(define petite-pass-tmpfilename "petitepass.txt")

(system (string-append "for %i in (petite.exe) do @echo %~$PATH:i >"
		       petite-pass-tmpfilename))

(define petite-exe-path
  (replace-path-sep (chomp-tail (read-file petite-pass-tmpfilename)
				(list #\space #\newline))))

(delete-file petite-pass-tmpfilename)

(define minlog-path (replace-path-sep (current-directory)))
;(define minlog-path (escape-win-chars (current-directory)))

;; (define (quote-path-for-elisp path)
;;   (string-append (string #\\ #\") path (string #\\ #\")))

(define src-init-scm (read-file "src/init.scm"))
(write-file
 "init.scm"
 (string-replace-substring src-init-scm "---MINLOGPATH---" minlog-path))

(define src-minlog-el (read-file "util/minlog.template.el"))
;; (define minlog-path-for-el (quote-path-for-elisp minlog-path))
;; (define petite-exe-path-for-el (quote-path-for-elisp petite-exe-path))

(write-file
 "util/minlog.el"
 (string-replace-substring
  (string-replace-substring
   (string-replace-substring src-minlog-el
			     "---MINLOGPATH---" minlog-path)
   "---MINLOGELPATH---" minlog-path)
  "---PETITEEXEPATH---" petite-exe-path))

(cd "src")
(if (file-exists? "minitab.scm") (delete-file "minitab.scm"))
(system "petite grammar.scm > grammar.log")
(cd "..")

(exit)
