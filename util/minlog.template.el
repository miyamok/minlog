(defun run-minlog (&optional filename)
  ;; Enable utf-8
  (setq default-enable-multibyte-characters t)
  (condition-case nil
      (set-language-environment "Greek")
    (error nil))
  (condition-case nil
      (set-language-environment "utf-8")
    (error nil))
  (set-input-method "TeX")

  ;; Start MINLOG
  (interactive)

  ;; MINLOG directory
  (if (getenv "MINLOGPATH")
      (setq minlogpath (getenv "MINLOGPATH"))
    (setq minlogpath "---MINLOGPATH---"))

  ;; which scheme to use ?
  (cond ((eq system-type 'windows-nt)
	 (setq scheme "---PETITEEXEPATH---"))
	((getenv "SCHEME") (setq scheme (getenv "SCHEME")))
	((eq 0 (shell-command "which scheme"))
	 (setq scheme "scheme"))
	((eq 0 (shell-command "which petite"))
	 (setq scheme "petite"))
	((eq 0 (shell-command "which racket"))
	 (setq scheme "racket -l mzscheme -l r5rs -i --load"))
	((eq 0 (shell-command "which mzscheme"))
	 (let ((version-info (shell-command-to-string "mzscheme --version")))
	   (if (or (string-match "Racket" version-info) ;; >= version 5
		   (string-match "v4." version-info))
	       (setq scheme "mzscheme -l mzscheme -l r5rs -i --load")
	     (setq scheme "mzscheme --load"))))
	((eq 0 (shell-command "which guile"))
	 (setq scheme "guile -l"))
	(t (error "Neither scheme nor petite nor racket nor mzscheme nor guile installed ")))

  ;; is there a heap file ?
  (if (and (file-readable-p (concat minlogpath "/minlog.heap"))
	   (or (string= scheme "petite")
	       (string= scheme "/usr/bin/petite")))
      (setq heapload
	    (concat "-h " minlogpath "/minlog.heap "
		    minlogpath "/welcome.scm"))
    (setq heapload (concat minlogpath "/init.scm")))

  (setq inhibit-startup-message t)
  (delete-other-frames)
  (delete-other-windows)
  ;; setup the frames
  (if (eq window-system nil)
      (setup-minlog-frame-nox filename)
    (setup-minlog-frames filename))

  ;; start scheme
  (if (eq system-type 'windows-nt)
      (run-scheme (concat (quote-string scheme) " " (quote-string heapload)))
    (run-scheme (concat scheme " " heapload))))

(defun setup-minlog-frames (&optional filename)
  (let* ((orig-frame (selected-frame))
	 (left-frame (make-frame))
	 (right-frame (make-frame))
	 (wh (frame-pixel-width left-frame))
	 (left-frame-lt (frame-parameter left-frame 'left))
	 (lt (if (< (+ left-frame-lt (* wh 2)) (x-display-pixel-width))
		 left-frame-lt 0))
	 (ht (/ (x-display-pixel-height) (frame-char-height)))
	 (border (frame-parameter left-frame 'border-width))
	 (tp  (cdr (assoc 'top (frame-parameters (selected-frame))))))
    (delete-frame orig-frame)
    (set-frame-position left-frame lt tp)
    (set-frame-position right-frame (+ lt wh (* 2 border)) tp)
    (if filename
	(progn (select-frame-set-input-focus left-frame)
	       (find-file filename)))
    (select-frame-set-input-focus right-frame)))

(defun setup-minlog-frame-nox (&optional filename)
  (split-window)
  (if filename (find-file filename))
  (other-window 1))

(defun quote-string (s) (concat "\"" s "\""))

(load "---MINLOGPATH---/util/minlog-unicode.el")

