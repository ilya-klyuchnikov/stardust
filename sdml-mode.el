;;; sdml-mode.el --- Major mode for editing StardustML

;; Derived from sml-mode.el, and associated files, by Stefan Monnier et al.;
;; see copyright notices below.
;; Changes are Copyright 2012 Joshua Dunfield; the GNU General Public License applies.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; sml-mode.el --- Major mode for editing (Standard) ML

;; Copyright (C) 1989       Lars Bo Nielsen
;; Copyright (C) 1994-1997  Matthew J. Morley
;; Copyright (C) 1999-2000  Stefan Monnier

;; Author: Lars Bo Nielsen
;;      Olin Shivers
;;	Fritz Knabe (?)
;;	Steven Gilmore (?)
;;	Matthew Morley <mjm@scs.leeds.ac.uk> (aka <matthew@verisity.com>)
;;	Matthias Blume <blume@cs.princeton.edu> (aka <blume@kurims.kyoto-u.ac.jp>)
;;      (Stefan Monnier) monnier@cs.yale.edu
;; Maintainer: (Stefan Monnier) monnier+lists/emacs/sml@flint.cs.yale.edu
;; Keywords: SML
;; $Revision: 1.27 $
;; $Date: 2001/09/18 19:09:26 $

;; This file is not part of GNU Emacs, but it is distributed under the
;; same conditions.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING. If not, write to the
;; Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;;; HISTORY

;; Still under construction: History obscure, needs a biographer as
;; well as a M-x doctor. Change Log on request.

;; Hacked by Olin Shivers for comint from Lars Bo Nielsen's sml.el.

;; Hacked by Matthew Morley to incorporate Fritz Knabe's hilite and
;; font-lock patterns, some of Steven Gilmore's (reduced) easy-menus,
;; and numerous bugs and bug-fixes.

;;; DESCRIPTION

;; See accompanying info file: sml-mode.info

;;; FOR YOUR .EMACS FILE

;; If sml-mode.el lives in some non-standard directory, you must tell
;; emacs where to get it. This may or may not be necessary:

;; (add-to-list 'load-path "~jones/lib/emacs/")

;; Then to access the commands autoload sml-mode with that command:

;; (load "sml-mode-startup")

;; sml-mode-hook is run whenever a new sml-mode buffer is created.

;; Finally, there are inferior-sml-{mode,load}-hooks -- see comments
;; in sml-proc.el. For much more information consult the mode's *info*
;; tree.

;;; Code:

(eval-when-compile (require 'cl))
(condition-case nil (require 'skeleton) (error nil))


;;; VARIABLES CONTROLLING INDENTATION

(defcustom sdml-indent-level 4
  "*Indentation of blocks in ML (see also `sdml-structure-indent')."
  :group 'sdml
  :type '(integer))

(defcustom sdml-indent-args sdml-indent-level
  "*Indentation of args placed on a separate line."
  :group 'sdml
  :type '(integer))

;; (defvar sdml-indent-align-args t
;;   "*Whether the arguments should be aligned.")

(defcustom sdml-electric-semi-mode nil
  "*If non-nil, `\;' will self insert, reindent the line, and do a newline.
If nil, just insert a `\;'.  (To insert while t, do: \\[quoted-insert] \;)."
  :group 'sdml
  :type 'boolean)

(defcustom sdml-rightalign-and t
  "If non-nil, right-align `and' with its leader.
If nil:					If t:
	datatype a = A				datatype a = A
	and b = B				     and b = B"
  :group 'sdml
  :type 'boolean)

;;; OTHER GENERIC MODE VARIABLES

(defvar sdml-mode-info "sdml-mode"
  "*Where to find Info file for `sdml-mode'.
The default assumes the info file \"sdml-mode.info\" is on Emacs' info
directory path.  If it is not, either put the file on the standard path
or set the variable `sdml-mode-info' to the exact location of this file

  (setq sdml-mode-info \"/usr/me/lib/info/sdml-mode\")

in your .emacs file. You can always set it interactively with the
set-variable command.")

(defvar sdml-mode-hook nil
  "*Run upon entering `sdml-mode'.
This is a good place to put your preferred key bindings.")

;;; CODE FOR SDML-MODE

(defun sdml-mode-info ()
  "Command to access the TeXinfo documentation for `sdml-mode'.
See doc for the variable `sdml-mode-info'."
  (interactive)
  (require 'info)
  (condition-case nil
      (info sdml-mode-info)
    (error (progn
             (describe-variable 'sdml-mode-info)
             (message "Can't find it... set this variable first!")))))


;;; Autoload functions -- no-doc is another idea cribbed from AucTeX!

(let ((sdml-no-doc
       "This function is part of sdml-proc, and has not yet been loaded.
Full documentation will be available after autoloading the function."))

  (autoload 'sdml-compile	"sdml-proc"   sdml-no-doc t)
  (autoload 'sdml-load-file	"sdml-proc"   sdml-no-doc t)
  (autoload 'switch-to-sdml	"sdml-proc"   sdml-no-doc t)
  (autoload 'sdml-send-region	"sdml-proc"   sdml-no-doc t)
  (autoload 'sdml-send-buffer	"sdml-proc"   sdml-no-doc t))


(defun flatten (ls &optional acc)
  (if (null ls) acc
    (let ((rest (flatten (cdr ls) acc))
	  (head (car ls)))
      (if (listp head)
	  (flatten head rest)
	(cons head rest)))))

(defun sdml-preproc-alist (al)
  "Expand an alist AL where keys can be lists of keys into a normal one."
  (reduce (lambda (x al)
	    (let ((k (car x))
		  (v (cdr x)))
	      (if (consp k)
		  (append (mapcar (lambda (y) (cons y v)) k) al)
		(cons x al))))
	  al
	  :initial-value nil
	  :from-end t))

;;; 
;;; defmap
;;; 

(defun custom-create-map (m bs args)
  (let (inherit dense suppress)
    (while args
      (let ((key (first args))
	    (val (second args)))
	(cond
	 ((eq key :dense) (setq dense val))
	 ((eq key :inherit) (setq inherit val))
	 ((eq key :group) )
	 ;;((eq key :suppress) (setq suppress val))
	 (t (message "Uknown argument %s in defmap" key))))
      (setq args (cddr args)))
    (unless (keymapp m)
      (setq bs (append m bs))
      (setq m (if dense (make-keymap) (make-sparse-keymap))))
    (dolist (b bs)
      (let ((keys (car b))
	    (binding (cdr b)))
	(dolist (key (if (consp keys) keys (list keys)))
	  (cond
	   ((symbolp key)
	    (substitute-key-definition key binding m global-map))
	   ((null binding)
	    (unless (keymapp (lookup-key m key)) (define-key m key binding)))
	   ((let ((o (lookup-key m key)))
	      (or (null o) (numberp o) (eq o 'undefined)))
	    (define-key m key binding))))))
    (cond
     ((keymapp inherit) (set-keymap-parent m inherit))
     ((consp inherit) (set-keymap-parents m inherit)))
    m))

(defmacro defmap (m bs doc &rest args)
  `(defconst ,m
     (custom-create-map (if (boundp ',m) ,m) ,bs ,(cons 'list args))
     ,doc))

;; defsyntax ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun custom-create-syntax (css args)
  (let ((st (make-syntax-table (cadr (memq :copy args)))))
    (dolist (cs css)
      (let ((char (car cs))
	    (syntax (cdr cs)))
	(if (sequencep char)
	    (mapcar* (lambda (c) (modify-syntax-entry c syntax st)) char)
	  (modify-syntax-entry char syntax st))))
    st))

(defmacro defsyntax (st css doc &rest args)
  `(defconst ,st (custom-create-syntax ,css ,(cons 'list args)) ,doc))

;;;; 
;;;; Compatibility info
;;;; 

(defvar sdml-builtin-nested-comments-flag
  (ignore-errors
    (not (equal (let ((st (make-syntax-table)))
		  (modify-syntax-entry ?\* ". 23n" st) st)
		(let ((st (make-syntax-table)))
		  (modify-syntax-entry ?\* ". 23" st) st))))
  "Non-nil means this Emacs understands the `n' in syntax entries.")


(defgroup sdml ()
  "Editing SDML code."
  :group 'languages)

(defvar sdml-outline-regexp
  ;; `st' and `si' are to match structure and signature.
  "\\|s[ti]\\|[ \t]*\\(let[ \t]+\\)?\\(fun\\|and\\)\\>"
  "Regexp matching a major heading.
This actually can't work without extending `outline-minor-mode' with the
notion of \"the end of an outline\".")

;;; 
;;; Internal defines
;;; 

(defmap sdml-mode-map
  ;; smarter cursor movement
  '((forward-sexp	. sdml-user-forward-sexp)
    (backward-sexp	. sdml-user-backward-sexp)
    ;; Text-formatting commands:
    ("\C-c\C-m"	. sdml-insert-form)
    ("\C-c\C-i"	. sdml-mode-info)
    ("\M-|"	. sdml-electric-pipe)
    ("\M-\ "	. sdml-electric-space)
    ("\;"	. sdml-electric-semi)
    ("\M-\t"	. sdml-back-to-outer-indent)
    ;; Process commands added to sdml-mode-map -- these should autoload
    ("\C-c\C-l"	. sdml-load-file)
    ("\C-c\C-c" . sdml-compile)
    ("\C-c\C-s" . switch-to-sdml)
    ("\C-c\C-r" . sdml-send-region)
    ("\C-c\C-b" . sdml-send-buffer)
    ([(meta shift down-mouse-1)] . sdml-drag-region))
  "The keymap used in `sdml-mode'."
  ;; :inherit sdml-bindings
  :group 'sdml)

(defsyntax sdml-mode-syntax-table
  `((?\*   . ,(if sdml-builtin-nested-comments-flag ". 23n" ". 23"))
    (?\(   . "()1")
    (?\)   . ")(4")
    ("._'" . "_")
    (",;"  . ".")
    ;; `!' is not really a prefix-char, oh well!
    ("~#!" . "'")
    ("%&$+-/:<=>?@`^|"	 . "."))
  "The syntax table used in `sdml-mode'.")


(easy-menu-define sdml-mode-menu sdml-mode-map "Menu used in `sdml-mode'."
  '("SDML"
    ("Process"
     ["Help for Inferior ML"	(describe-function 'inferior-sdml-mode) :active (featurep 'sdml-proc)])
    ["electric pipe"     sdml-electric-pipe t]
    ["insert SDML form"   sdml-insert-form t]
    ("Forms" :filter sdml-forms-menu)
    ("Format/Mode Variables"
     ["indent region"             indent-region t]
     ["outdent"                   sdml-back-to-outer-indent t]
     ["-" nil nil]
     ["set indent-level"          sdml-indent-level t]
     ["set pipe-indent"           sdml-pipe-indent t]
     ["--" nil nil]
     ["toggle type-of-indent"     (sdml-type-of-indent) t]
     ["toggle nested-if-indent"   (sdml-nested-if-indent) t]
     ["toggle case-indent"        (sdml-case-indent) t]
     ["toggle electric-semi-mode" (sdml-electric-semi-mode) t])
    ["-----" nil nil]
    ["SDML mode help (brief)"       describe-mode t]
    ["SDML mode *info*"             sdml-mode-info t]
    ["-----" nil nil]
    ["Remove overlay"    (sdml-error-overlay 'undo) t ;:active (sdml-overlay-active-p)
     ]))

;; Make's sure they appear in the menu bar when sdml-mode-map is active.
;; On the hook for XEmacs only -- see easy-menu-add in auc-menu.el.
;; (defun sdml-mode-menu-bar ()
;;   "Make sure menus appear in the menu bar as well as under mouse 3."
;;   (and (eq major-mode 'sdml-mode)
;;        (easy-menu-add sdml-mode-menu sdml-mode-map)))
;; (add-hook 'sdml-mode-hook 'sdml-mode-menu-bar)

;;
;; regexps
;;

(defun sdml-syms-re (&rest syms)
  (concat "\\<" (regexp-opt (flatten syms) t) "\\>"))

;;

(defconst sdml-module-head-syms nil)


(defconst sdml-begin-syms
  '("let" "local" "struct" "sig")
  "Symbols matching the `end' symbol.")

(defconst sdml-begin-syms-re
  (sdml-syms-re "let" "local" "struct" "sig")
  "Symbols matching the `end' symbol.")

;; (defconst sdml-user-begin-symbols-re
;;   (sdml-syms-re "let" "local" "struct" "sig" "in" "with")
;;   "Symbols matching (loosely) the `end' symbol.")

(defconst sdml-sexp-head-symbols-re
  (sdml-syms-re "let" "local" "struct" "sig" "in" "with"
	       "where"
                         "if" "then" "else" "case" "of" "fn" "fun" "val" "and"
	       "datatype" "type"
	       sdml-module-head-syms
	       "handle" "raise")
  "Symbols starting an sexp.")

;; (defconst sdml-not-arg-start-re
;;   (sdml-syms-re "in" "of" "end" "andalso")
;;   "Symbols that can't be found at the head of an arg.")

;; (defconst sdml-not-arg-re
;;   (sdml-syms-re "in" "of" "end" "andalso")
;;   "Symbols that should not be confused with an arg.")

(defconst sdml-=-starter-syms
  (list* "|" "val" "fun" "and" "datatype" "type" "eqtype"
	 sdml-module-head-syms)
  "Symbols that can be followed by a `='.")
(defconst sdml-=-starter-re
  (concat "\\S.|\\S.\\|" (sdml-syms-re (cdr sdml-=-starter-syms)))
  "Symbols that can be followed by a `='.")

(defconst sdml-indent-rule
  (sdml-preproc-alist
   `(("struct" . 0)
     (,sdml-module-head-syms "d=" 0)
     ("local" "in" 0)
     ;;("of" . (3 nil))
     ;;("else" . (sdml-indent-level 0))
     ;;(("in" "fun" "and" "of") . (sdml-indent-level nil))
     ("if" "else" 0)
     (,sdml-=-starter-syms nil)
     (("case" "datatype" "if" "then" "else"
       "let" "local" "raise" "type" "val" "while"
       "with" "withtype")))))

(defconst sdml-starters-indent-after
  (sdml-syms-re "let" "local" "in")
  "Indent after these.")

(defconst sdml-delegate
  (sdml-preproc-alist
   `((("of" "else" "then" "d=") . (not (sdml-bolp)))
     ("in" . t)))
  "Words which might delegate indentation to their parent.")

(defcustom sdml-symbol-indent
  '(("fn" . -3)
    ("of" . 1)
    ("|" . -2)
    ("," . -2)
    (";" . -2)
    ;;("in" . 1)
    ("d=" . 2))
  "Special indentation alist for some symbols.
An entry like (\"in\" . 1) indicates that a line starting with the
symbol `in' should be indented one char further to the right.
This is only used in a few specific cases, so it does not work
for all symbols and in all lines starting with the given symbol."
  :group 'sdml
  :type '(repeat (cons string integer)))

(defconst sdml-open-paren
  (sdml-preproc-alist
   `((,(list* "with" "in" sdml-begin-syms) ,sdml-begin-syms-re "\\<end\\>")))
  "Symbols that should behave somewhat like opening parens.")

(defconst sdml-close-paren
  `(("in" "\\<l\\(ocal\\|et\\)\\>")
    ("withtype" "\\<\\(data\\)type\\>")
    ("end" ,sdml-begin-syms-re)
    ("then" "\\<if\\>")
    ("else" "\\<if\\>" (sdml-bolp))
    ("of" "\\<case\\>")
    ("d=" nil))
  "Symbols that should behave somewhat like close parens.")

(defconst sdml-agglomerate-re "\\<else[ \t]+if\\>"
  "Regexp of compound symbols (pairs of symbols to be considered as one).")

(defconst sdml-non-nested-of-starter-re
  (sdml-syms-re "datatype")
  "Symbols that can introduce an `of' that shouldn't behave like a paren.")

(defconst sdml-starters-syms
  (append sdml-module-head-syms
	  '("datatype" "fun"
	    "local"
	    "type" "val" "and"
	    "withtype" "with"))
  "The starters of new expressions.")

(defconst sdml-exptrail-syms
  '("if" "then" "else" "withtype" "case" "of" "raise" "fn"))

(defconst sdml-pipeheads
   '("|" "of" "fun" "fn" "and" "handle" "datatype")
   "A `|' corresponds to one of these.")


;;;;
;;;; Imenu support
;;;;

(defvar sdml-imenu-regexp
  (concat "^[ \t]*\\(let[ \t]+\\)?"
	  (regexp-opt (append sdml-module-head-syms
			      '("and" "fun" "datatype" "type")) t)
	  "\\>"))

(defun sdml-imenu-create-index ()
  (let (alist)
    (goto-char (point-max))
    (while (re-search-backward sdml-imenu-regexp nil t)
      (save-excursion
	(let ((kind (match-string 2))
	      (column (progn (goto-char (match-beginning 2)) (current-column)))
	      (location
	       (progn (goto-char (match-end 0))
		      (sdml-forward-spaces)
		      (when (looking-at sdml-tyvarseq-re)
			(goto-char (match-end 0)))
		      (point)))
	      (name (sdml-forward-sym)))
	  ;; Eliminate trivial renamings.
	  (when (or (not (member kind '("structure" "signature")))
		    (progn (search-forward "=")
			   (sdml-forward-spaces)
			   (looking-at "sig\\|struct")))
	    (push (cons (concat (make-string (/ column 2) ?\ ) name) location)
		  alist)))))
    alist))

;;; MORE CODE FOR SDML-MODE

;; XEmacs hack, autoload a dummy autoload instead of a derived mode.
;;;###autoload(autoload 'sdml-mode "sdml-mode" nil t)
(define-derived-mode sdml-mode fundamental-mode "SDML"
  "\\<sdml-mode-map>Major mode for editing StardustML code (based on sml-mode)
This mode runs `sdml-mode-hook' just before exiting.
\\{sdml-mode-map}"
  (set (make-local-variable 'font-lock-defaults) sdml-font-lock-defaults)
  (set (make-local-variable 'outline-regexp) sdml-outline-regexp)
  (set (make-local-variable 'imenu-create-index-function)
       'sdml-imenu-create-index)
  (set (make-local-variable 'add-log-current-defun-function)
       'sdml-current-fun-name)
  ;; forward-sexp-function is an experimental variable in my hacked Emacs.
  (set (make-local-variable 'forward-sexp-function) 'sdml-user-forward-sexp)
  ;; For XEmacs
  (easy-menu-add sdml-mode-menu)
  ;; Compatibility
  (unless (boundp 'skeleton-positions) (set (make-local-variable '@) nil))
  (sdml-mode-variables))

(defun sdml-mode-variables ()
  (set-syntax-table sdml-mode-syntax-table)
  (setq local-abbrev-table sdml-mode-abbrev-table)
  ;; A paragraph is separated by blank lines or ^L only.
  
  (set (make-local-variable 'paragraph-start)
       (concat "^[\t ]*$\\|" page-delimiter))
  (set (make-local-variable 'paragraph-separate) paragraph-start)
  (set (make-local-variable 'indent-line-function) 'sdml-indent-line) ; XXX
  (set (make-local-variable 'comment-start) "(* ")
  (set (make-local-variable 'comment-end) " *)")
  (set (make-local-variable 'comment-nested) t)
  ;;(set (make-local-variable 'block-comment-start) "* ")
  ;;(set (make-local-variable 'block-comment-end) "")
  ;; (set (make-local-variable 'comment-column) 40)
  (set (make-local-variable 'comment-start-skip) "(\\*+\\s-*"))

(defun sdml-funname-of-and ()
  "Name of the function this `and' defines, or nil if not a function.
Point has to be right after the `and' symbol and is not preserved."
  (sdml-forward-spaces)
  (if (looking-at sdml-tyvarseq-re) (goto-char (match-end 0)))
  (let ((sym (sdml-forward-sym)))
    (sdml-forward-spaces)
    (unless (or (member sym '(nil "d="))
		(member (sdml-forward-sym) '("d=")))
      sym)))

(defun sdml-electric-pipe ()
  "Insert a \"|\".
Depending on the context insert the name of function, a \"=>\" etc."
  (interactive)
  (sdml-with-ist
   (unless (save-excursion (skip-chars-backward "\t ") (bolp)) (insert "\n"))
   (insert "| ")
   (let ((text
	  (save-excursion
	    (backward-char 2)		;back over the just inserted "| "
	    (let ((sym (sdml-find-matching-starter sdml-pipeheads
						  (sdml-op-prec "|" 'back))))
	      (sdml-forward-sym)
	      (sdml-forward-spaces)
	      (cond
	       ((string= sym "|")
		(let ((f (sdml-forward-sym)))
		  (sdml-find-forward "\\(=>\\|=\\||\\)\\S.")
		  (cond
		   ((looking-at "|") "") ;probably a datatype
		   ((looking-at "=>") " => ") ;`case', or `fn' or `handle'
		   ((looking-at "=") (concat f "  = "))))) ;a function
	       ((string= sym "and")
		;; could be a datatype or a function
		(setq sym (sdml-funname-of-and))
		(if sym (concat sym "  = ") ""))
	       ;; trivial cases
	       ((string= sym "fun")
		(while (and (setq sym (sdml-forward-sym))
			    (string-match "^'" sym))
		  (sdml-forward-spaces))
		(concat sym "  = "))
	       ((member sym '("case" "handle" "fn" "of")) " => ")
	       ;;((member sym '("datatype")) "")
	       (t ""))))))

     (insert text)
     (indent-according-to-mode)
     (beginning-of-line)
     (skip-chars-forward "\t |")
     (skip-syntax-forward "w")
     (skip-chars-forward "\t ")
     (when (and (not (eobp)) (= ?= (char-after))) (backward-char)))))

(defun sdml-electric-semi ()
  "Insert a \;.
If variable `sdml-electric-semi-mode' is t, indent the current line, insert
a newline, and indent."
  (interactive)
  (insert "\;")
  (if sdml-electric-semi-mode
      (reindent-then-newline-and-indent)))

;;; INDENTATION !!!

(defun sdml-mark-function ()
  "Synonym for `mark-paragraph' -- sorry.
If anyone has a good algorithm for this..."
  (interactive)
  (mark-paragraph))

(defun sdml-indent-line ()
  "Indent current line of Stardust ML code."
  (interactive)
  (let ((savep (> (current-column) (current-indentation)))
	(indent (max (or (ignore-errors (sdml-calculate-indentation)) 0) 0)))
    (if savep
	(save-excursion (indent-line-to indent))
      (indent-line-to indent))))

(defun sdml-back-to-outer-indent ()
  "Unindents to the next outer level of indentation."
  (interactive)
  (save-excursion
    (beginning-of-line)
    (skip-chars-forward "\t ")
    (let ((start-column (current-column))
          (indent (current-column)))
      (if (> start-column 0)
          (progn
            (save-excursion
              (while (>= indent start-column)
                (if (re-search-backward "^[^\n]" nil t)
                    (setq indent (current-indentation))
                  (setq indent 0))))
            (backward-delete-char-untabify (- start-column indent)))))))

(defun sdml-find-comment-indent ()
  (save-excursion
    (let ((depth 1))
      (while (> depth 0)
	(if (re-search-backward "(\\*\\|\\*)" nil t)
	    (cond
	     ;; FIXME: That's just a stop-gap.
	     ((eq (get-text-property (point) 'face) 'font-lock-string-face))
	     ((looking-at "*)") (incf depth))
	     ((looking-at comment-start-skip) (decf depth)))
	  (setq depth -1)))
      (if (= depth 0)
	  (1+ (current-column))
	nil))))

;;; Code:

(eval-when-compile (require 'cl))


(defsyntax sdml-internal-syntax-table
  '((?_  . "w")
    (?'  . "w")
    (?.  . "w")
    ;; treating `~' as a word constituent is not quite right, but
    ;; close enough.  Think about 12.3E~2 for example.  Also `~' on its
    ;; own *is* a nonfix symbol.
    (?~  . "w"))
  "Syntax table used for internal sdml-mode operation."
  :copy sdml-mode-syntax-table)

;;; 
;;; various macros
;;; 

(defmacro sdml-with-ist (&rest r)
  (let ((ost-sym (make-symbol "oldtable")))
    `(let ((,ost-sym (syntax-table))
	   (case-fold-search nil)
	   (parse-sexp-lookup-properties t)
	   (parse-sexp-ignore-comments t))
       (unwind-protect
	   (progn (set-syntax-table sdml-internal-syntax-table) . ,r)
	 (set-syntax-table ,ost-sym)))))
(def-edebug-spec sdml-with-ist t)

(defmacro sdml-move-if (&rest body)
  (let ((pt-sym (make-symbol "point"))
	(res-sym (make-symbol "result")))
    `(let ((,pt-sym (point))
	   (,res-sym ,(cons 'progn body)))
       (unless ,res-sym (goto-char ,pt-sym))
       ,res-sym)))
(def-edebug-spec sdml-move-if t)

(defmacro sdml-point-after (&rest body)
  `(save-excursion
     ,@body
     (point)))
(def-edebug-spec sdml-point-after t)

;;

(defvar sdml-op-prec
  (sdml-preproc-alist
   '(("before" . 0)
     ((":=" "o") . 3)
     ((">" ">=" "<>" "<" "<=" "=") . 4)
     (("::" "@") . 5)
     (("+" "-" "^") . 6)
     (("/" "*" "quot" "rem" "div" "mod") . 7)))
  "Alist of SDML infix operators and their precedence.")

(defconst sdml-syntax-prec
  (sdml-preproc-alist
   `((("in" "with") . 10)
     ((";" ",") . 20)
     (("=>" "d=" "=of") . (65 . 40))
     ("|" . (47 . 30))
     (("case" "of" "fn") . 45)
     (("if" "then" "else" "while" "do" "raise") . 50)
     ("handle" . 60)
     ("orelse" . 70)
     ("andalso" . 80)
     ((":" ":>") . 90)
     ("->" . 95)
     (,(cons "end" sdml-begin-syms) . 10000)))
  "Alist of pseudo-precedence of syntactic elements.")

(defun sdml-op-prec (op dir)
  "Return the precedence of OP or nil if it's not an infix.
DIR should be set to BACK if you want to precedence w.r.t the left side
    and to FORW for the precedence w.r.t the right side.
This assumes that we are `looking-at' the OP."
  (when op
    (let ((sprec (cdr (assoc op sdml-syntax-prec))))
      (cond
       ((consp sprec) (if (eq dir 'back) (car sprec) (cdr sprec)))
       (sprec sprec)
       (t
	(let ((prec (cdr (assoc op sdml-op-prec))))
	  (when prec (+ prec 100))))))))

;;

(defun sdml-forward-spaces () (forward-comment 100000))
(defun sdml-backward-spaces () (forward-comment -100000))


;;
;; moving forward around matching symbols
;;

(defun sdml-looking-back-at (re)
  (save-excursion
    (when (= 0 (skip-syntax-backward "w_")) (backward-char))
    (looking-at re)))

(defun sdml-find-match-forward (this match)
  "Only works for word matches."
  (let ((level 1)
	(forward-sexp-function nil)
	(either (concat this "\\|" match)))
    (while (> level 0)
      (forward-sexp 1)
      (while (not (or (eobp) (sdml-looking-back-at either)))
	(condition-case () (forward-sexp 1) (error (forward-char 1))))
      (setq level
	    (cond
	     ((sdml-looking-back-at this) (1+ level))
	     ((sdml-looking-back-at match) (1- level))
	     (t (error "Unbalanced")))))
    t))

(defun sdml-find-match-backward (this match)
  (let ((level 1)
	(forward-sexp-function nil)
	(either (concat this "\\|" match)))
    (while (> level 0)
      (backward-sexp 1)
      (while (not (or (bobp) (looking-at either)))
	(condition-case () (backward-sexp 1) (error (backward-char 1))))
      (setq level
	    (cond
	     ((looking-at this) (1+ level))
	     ((looking-at match) (1- level))
	     (t (error "Unbalanced")))))
    t))

;;; 
;;; read a symbol, including the special "op <sym>" case
;;; 

(defmacro sdml-move-read (&rest body)
  (let ((pt-sym (make-symbol "point")))
    `(let ((,pt-sym (point)))
       ,@body
       (when (/= (point) ,pt-sym)
	 (buffer-substring-no-properties (point) ,pt-sym)))))
(def-edebug-spec sdml-move-read t)

(defun sdml-poly-equal-p ()
  (< (sdml-point-after (re-search-backward sdml-=-starter-re nil 'move))
     (sdml-point-after (re-search-backward "=" nil 'move))))

(defun sdml-nested-of-p ()
  (< (sdml-point-after
      (re-search-backward sdml-non-nested-of-starter-re nil 'move))
     (sdml-point-after (re-search-backward "\\<case\\>" nil 'move))))

(defun sdml-forward-sym-1 ()
  (or (/= 0 (skip-syntax-forward "'w_"))
      (/= 0 (skip-syntax-forward ".'"))))
(defun sdml-forward-sym ()
  (let ((sym (sdml-move-read (sdml-forward-sym-1))))
    (cond
     ((equal "op" sym)
      (sdml-forward-spaces)
      (concat "op " (or (sdml-move-read (sdml-forward-sym-1)) "")))
     ((equal sym "=")
      (save-excursion
	(sdml-backward-sym-1)
	(if (sdml-poly-equal-p) "=" "d=")))
     ((equal sym "of")
      (save-excursion
	(sdml-backward-sym-1)
	(if (sdml-nested-of-p) "of" "=of")))
     ;; ((equal sym "datatype")
     ;;  (save-excursion
     ;; 	(sdml-backward-sym-1)
     ;; 	(sdml-backward-spaces)
     ;; 	(if (eq (preceding-char) ?=) "=datatype" sym)))
     (t sym))))

(defun sdml-backward-sym-1 ()
  (or (/= 0 (skip-syntax-backward ".'"))
      (/= 0 (skip-syntax-backward "'w_"))))
(defun sdml-backward-sym ()
  (let ((sym (sdml-move-read (sdml-backward-sym-1))))
    (when sym
      ;; FIXME: what should we do if `sym' = "op" ?
      (let ((point (point)))
	(sdml-backward-spaces)
	(if (equal "op" (sdml-move-read (sdml-backward-sym-1)))
	    (concat "op " sym)
	  (goto-char point)
	  (cond
	   ((string= sym "=") (if (sdml-poly-equal-p) "=" "d="))
	   ((string= sym "of") (if (sdml-nested-of-p) "of" "=of"))
	   ;; ((string= sym "datatype")
	   ;;  (save-excursion (sdml-backward-spaces)
	   ;; 		    (if (eq (preceding-char) ?=) "=datatype" sym)))
	   (t sym)))))))
    

(defun sdml-backward-sexp (prec)
  "Move one sexp backward if possible, or one char else.
Returns t if the move indeed moved through one sexp and nil if not.
PREC is the precedence currently looked for."
  (let ((parse-sexp-lookup-properties t)
	(parse-sexp-ignore-comments t))
    (sdml-backward-spaces)
    (let* ((point (point))
	   (op (sdml-backward-sym))
	   (op-prec (sdml-op-prec op 'back))
	   match)
      (cond
       ((not op)
	(let ((point (point)))
	  (ignore-errors (let ((forward-sexp-function nil)) (backward-sexp 1)))
	  (if (/= point (point)) t (ignore-errors (backward-char 1)) nil)))
       ;; stop as soon as precedence is smaller than `prec'
       ((and prec op-prec (>= prec op-prec)) nil)
       ;; special rules for nested constructs like if..then..else
       ((and (or (not prec) (and prec op-prec))
	     (setq match (second (assoc op sdml-close-paren))))
	(sdml-find-match-backward (concat "\\<" op "\\>") match))
       ;; don't back over open-parens
       ((assoc op sdml-open-paren) nil)
       ;; infix ops precedence
       ((and prec op-prec) (< prec op-prec))
       ;; [ prec = nil ]  a new operator, let's skip the sexps until the next
       (op-prec (while (sdml-move-if (sdml-backward-sexp op-prec))) t)
       ;; special symbols indicating we're getting out of a nesting level
       ((string-match sdml-sexp-head-symbols-re op) nil)
       ;; if the op was not alphanum, then we still have to do the backward-sexp
       ;; this reproduces the usual backward-sexp, but it might be bogus
       ;; in this case since !@$% is a perfectly fine symbol
       (t t))))) ;(or (string-match "\\sw" op) (sdml-backward-sexp prec))

(defun sdml-forward-sexp (prec)
  "Moves one sexp forward if possible, or one char else.
Returns T if the move indeed moved through one sexp and NIL if not."
  (let ((parse-sexp-lookup-properties t)
	(parse-sexp-ignore-comments t))
    (sdml-forward-spaces)
    (let* ((point (point))
	   (op (sdml-forward-sym))
	   (op-prec (sdml-op-prec op 'forw))
	   match)
      (cond
       ((not op)
	(let ((point (point)))
	  (ignore-errors (let ((forward-sexp-function nil)) (forward-sexp 1)))
	  (if (/= point (point)) t (forward-char 1) nil)))
       ;; stop as soon as precedence is smaller than `prec'
       ((and prec op-prec (>= prec op-prec)) nil)
       ;; special rules for nested constructs like if..then..else
       ((and (or (not prec) (and prec op-prec))
	     (setq match (cdr (assoc op sdml-open-paren))))
	(sdml-find-match-forward (first match) (second match)))
       ;; don't forw over close-parens
       ((assoc op sdml-close-paren) nil)
       ;; infix ops precedence
       ((and prec op-prec) (< prec op-prec))
       ;; [ prec = nil ]  a new operator, let's skip the sexps until the next
       (op-prec (while (sdml-move-if (sdml-forward-sexp op-prec))) t)
       ;; special symbols indicating we're getting out of a nesting level
       ((string-match sdml-sexp-head-symbols-re op) nil)
       ;; if the op was not alphanum, then we still have to do the backward-sexp
       ;; this reproduces the usual backward-sexp, but it might be bogus
       ;; in this case since !@$% is a perfectly fine symbol
       (t t))))) ;(or (string-match "\\sw" op) (sdml-backward-sexp prec))

(defun sdml-in-word-p ()
  (and (eq ?w (char-syntax (or (char-before) ? )))
       (eq ?w (char-syntax (or (char-after) ? )))))

(defun sdml-user-backward-sexp (&optional count)
  "Like `backward-sexp' but tailored to the SDML syntax."
  (interactive "p")
  (unless count (setq count 1))
  (sdml-with-ist
   (let ((point (point)))
     (if (< count 0) (sdml-user-forward-sexp (- count))
       (when (sdml-in-word-p) (forward-word 1))
       (dotimes (i count)
	 (unless (sdml-backward-sexp nil)
	   (goto-char point)
	   (error "Containing expression ends prematurely")))))))

(defun sdml-user-forward-sexp (&optional count)
  "Like `forward-sexp' but tailored to the SDML syntax."
  (interactive "p")
  (unless count (setq count 1))
  (sdml-with-ist
   (let ((point (point)))
     (if (< count 0) (sdml-user-backward-sexp (- count))
       (when (sdml-in-word-p) (backward-word 1))
       (dotimes (i count)
	 (unless (sdml-forward-sexp nil)
	   (goto-char point)
	   (error "Containing expression ends prematurely")))))))

;;(defun sdml-forward-thing ()
;;  (if (= ?w (char-syntax (char-after))) (forward-word 1) (forward-char 1)))

(defun sdml-backward-arg () (sdml-backward-sexp 1000))
(defun sdml-forward-arg () (sdml-forward-sexp 1000))


(provide 'sdml-move)

;;; sdml-move.el ends here




(defun sdml-calculate-indentation ()
  (save-excursion
    (beginning-of-line) (skip-chars-forward "\t ")
    (sdml-with-ist
     ;; Indentation for comments alone on a line, matches the
     ;; proper indentation of the next line.
     (when (looking-at "(\\*") (sdml-forward-spaces))
     (let (data
	   (sdml-point (point))
	   (sym (save-excursion (sdml-forward-sym))))
       (or
	;; Allow the user to override the indentation.
	(when (looking-at (concat ".*" (regexp-quote comment-start)
				  "[ \t]*fixindent[ \t]*"
				  (regexp-quote comment-end)))
	  (current-indentation))

	;; Continued comment.
	(and (looking-at "\\*") (sdml-find-comment-indent))

	;; Continued string ? (Added 890113 lbn)
	(and (looking-at "\\\\")
	     (save-excursion
	       (if (save-excursion (previous-line 1)
				   (beginning-of-line)
				   (looking-at "[\t ]*\\\\"))
		   (progn (previous-line 1) (current-indentation))
		 (if (re-search-backward "[^\\\\]\"" nil t)
		     (1+ (current-column))
		   0))))

	;; Closing parens.  Could be handled below with `sdml-indent-relative'?
	(and (looking-at "\\s)")
	     (save-excursion
	       (skip-syntax-forward ")")
	       (backward-sexp 1)
	       (if (sdml-dangling-sym)
		   (sdml-indent-default 'noindent)
		 (current-column))))

	(and (setq data (assoc sym sdml-close-paren))
	     (sdml-indent-relative sym data))

	(and (member sym sdml-starters-syms)
	     (sdml-indent-starter sym))

	(and (string= sym "|") (sdml-indent-pipe))

	(sdml-indent-arg)
	(sdml-indent-default))))))

(defsubst sdml-bolp ()
  (save-excursion (skip-chars-backward " \t|") (bolp)))

(defun sdml-indent-starter (orig-sym)
  "Return the indentation to use for a symbol in `sdml-starters-syms'.
Point should be just before the symbol ORIG-SYM and is not preserved."
  (let ((sym (unless (save-excursion (sdml-backward-arg))
	       (sdml-backward-spaces)
	       (sdml-backward-sym))))
    (if (equal sym "d=") (setq sym nil))
    (if sym (sdml-get-sym-indent sym)
      ;; FIXME: this can take a *long* time !!
      (setq sym (sdml-find-matching-starter sdml-starters-syms))
      ;; Don't align with `and' because it might be specially indented.
      (if (and (or (equal orig-sym "and") (not (equal sym "and")))
	       (sdml-bolp))
	  (+ (current-column)
	     (if (and sdml-rightalign-and (equal orig-sym "and"))
		 (- (length sym) 3) 0))
	(sdml-indent-starter orig-sym)))))

(defun sdml-indent-relative (sym data)
  (save-excursion
    (sdml-forward-sym) (sdml-backward-sexp nil)
    (unless (second data) (sdml-backward-spaces) (sdml-backward-sym))
    (+ (or (cdr (assoc sym sdml-symbol-indent)) 0)
       (sdml-delegated-indent))))

(defun sdml-indent-pipe ()
  (let ((sym (sdml-find-matching-starter sdml-pipeheads
					(sdml-op-prec "|" 'back))))
    (when sym
      (if (string= sym "|")
	  (if (sdml-bolp) (current-column) (sdml-indent-pipe))
	(let ((pipe-indent (or (cdr (assoc "|" sdml-symbol-indent)) -2)))
	  (when (or (member sym '("datatype" "abstype"))
		    (and (equal sym "and")
			 (save-excursion
			   (forward-word 1)
			   (not (sdml-funname-of-and)))))
	    (re-search-forward "="))
	  (sdml-forward-sym)
	  (sdml-forward-spaces)
	  (+ pipe-indent (current-column)))))))

(defun sdml-find-forward (re)
  (sdml-forward-spaces)
  (while (and (not (looking-at re))
	      (progn
		(or (ignore-errors (forward-sexp 1) t) (forward-char 1))
		(sdml-forward-spaces)
		(not (looking-at re))))))

(defun sdml-indent-arg ()
  (and (save-excursion (ignore-errors (sdml-forward-arg)))
       ;;(not (looking-at sdml-not-arg-re))
       ;; looks like a function or an argument
       (sdml-move-if (sdml-backward-arg))
       ;; an argument
       (if (save-excursion (not (sdml-backward-arg)))
	   ;; a first argument
	   (+ (current-column) sdml-indent-args)
	 ;; not a first arg
	 (while (and (/= (current-column) (current-indentation))
		     (sdml-move-if (sdml-backward-arg))))
	 (unless (save-excursion (sdml-backward-arg))
	   ;; all earlier args are on the same line
	   (sdml-forward-arg) (sdml-forward-spaces))
	 (current-column))))

(defun sdml-get-indent (data sym)
  (let ((head-sym (pop data)) d)
    (cond
     ((not (listp data)) data)
     ((setq d (member sym data)) (second d))
     ((and (consp data) (not (stringp (car data)))) (car data))
     (t sdml-indent-level))))

(defun sdml-dangling-sym ()
  "Non-nil if the symbol after point is dangling.
The symbol can be an SDML symbol or an open-paren. \"Dangling\" means that
it is not on its own line but is the last element on that line."
  (save-excursion
    (and (not (sdml-bolp))
	 (< (sdml-point-after (end-of-line))
	    (sdml-point-after (or (sdml-forward-sym) (skip-syntax-forward "("))
			     (sdml-forward-spaces))))))

(defun sdml-delegated-indent ()
  (if (sdml-dangling-sym)
      (sdml-indent-default 'noindent)
    (sdml-move-if (backward-word 1)
		 (looking-at sdml-agglomerate-re))
    (current-column)))

(defun sdml-get-sym-indent (sym &optional style)
  "Find the indentation for the SYM we're `looking-at'.
If indentation is delegated, point will move to the start of the parent.
Optional argument STYLE is currently ignored."
  (assert (equal sym (save-excursion (sdml-forward-sym))))
  (save-excursion
    (let ((delegate (assoc sym sdml-close-paren))
	  (head-sym sym))
      (when (and delegate (not (eval (third delegate))))
	;;(sdml-find-match-backward sym delegate)
	(sdml-forward-sym) (sdml-backward-sexp nil)
	(setq head-sym
	      (if (second delegate)
		  (save-excursion (sdml-forward-sym))
		(sdml-backward-spaces) (sdml-backward-sym))))

      (let ((idata (assoc head-sym sdml-indent-rule)))
	(when idata
	  ;;(if (or style (not delegate))
	  ;; normal indentation
	  (let ((indent (sdml-get-indent idata sym)))
	    (when indent (+ (sdml-delegated-indent) indent)))
	  ;; delgate indentation to the parent
	  ;;(sdml-forward-sym) (sdml-backward-sexp nil)
	  ;;(let* ((parent-sym (save-excursion (sdml-forward-sym)))
	  ;;     (parent-indent (cdr (assoc parent-sym sdml-indent-starters))))
	  ;; check the special rules
	  ;;(+ (sdml-delegated-indent)
	  ;; (or (sdml-get-indent indent-data 1 'strict)
	  ;; (sdml-get-indent parent-indent 1 'strict)
	  ;; (sdml-get-indent indent-data 0)
	  ;; (sdml-get-indent parent-indent 0))))))))
	  )))))

(defun sdml-indent-default (&optional noindent)
  (let* ((sym-after (save-excursion (sdml-forward-sym)))
	 (_ (sdml-backward-spaces))
	 (sym-before (sdml-backward-sym))
	 (sym-indent (and sym-before (sdml-get-sym-indent sym-before)))
	 (indent-after (or (cdr (assoc sym-after sdml-symbol-indent)) 0)))
    (when (equal sym-before "end")
      ;; I don't understand what's really happening here, but when
      ;; it's `end' clearly, we need to do something special.
      (forward-word 1)
      (setq sym-before nil sym-indent nil))
    (cond
     (sym-indent
      ;; the previous sym is an indentation introducer: follow the rule
      (if noindent
	  ;;(current-column)
	  sym-indent
	(+ sym-indent indent-after)))
     ;; If we're just after a hanging open paren.
     ((and (eq (char-syntax (preceding-char)) ?\()
	   (save-excursion (backward-char) (sdml-dangling-sym)))
      (backward-char)
      (sdml-indent-default))
     (t
      ;; default-default
      (let* ((prec-after (sdml-op-prec sym-after 'back))
	     (prec (or (sdml-op-prec sym-before 'back) prec-after 100)))
	;; go back until you hit a symbol that has a lower prec than the
	;; "current one", or until you backed over a sym that has the same prec
	;; but is at the beginning of a line.
	(while (and (not (sdml-bolp))
		    (while (sdml-move-if (sdml-backward-sexp (1- prec))))
		    (not (sdml-bolp)))
	  (while (sdml-move-if (sdml-backward-sexp prec))))
	(if noindent
	    ;; the `noindent' case does back over an introductory symbol
	    ;; such as `fun', ...
	    (progn
	      (sdml-move-if
	       (sdml-backward-spaces)
	       (member (sdml-backward-sym) sdml-starters-syms))
	      (current-column))
	  ;; Use `indent-after' for cases such as when , or ; should be
	  ;; outdented so that their following terms are aligned.
	  (+ (if (progn
		   (if (equal sym-after ";")
		       (sdml-move-if
			(sdml-backward-spaces)
			(member (sdml-backward-sym) sdml-starters-syms)))
		   (and sym-after (not (looking-at sym-after))))
		 indent-after 0)
	     (current-column))))))))


;; maybe `|' should be set to word-syntax in our temp syntax table ?
(defun sdml-current-indentation ()
  (save-excursion
    (beginning-of-line)
    (skip-chars-forward " \t|")
    (current-column)))


(defun sdml-find-matching-starter (syms &optional prec)
  (let (sym)
    (ignore-errors
      (while
	  (progn (sdml-backward-sexp prec)
		 (setq sym (save-excursion (sdml-forward-sym)))
		 (not (or (member sym syms) (bobp)))))
      (if (member sym syms) sym))))

(defun sdml-skip-siblings ()
  (while (and (not (bobp)) (sdml-backward-arg))
    (sdml-find-matching-starter sdml-starters-syms))
  (when (looking-at "in\\>\\|local\\>")
    ;;skip over `local...in' and continue
    (forward-word 1)
    (sdml-backward-sexp nil)
    (sdml-skip-siblings)))

(defun sdml-beginning-of-defun ()
  (let ((sym (sdml-find-matching-starter sdml-starters-syms)))
    (if (member sym '("fun" "and" "functor" "signature" "structure"
		      "abstraction" "datatype" "abstype"))
	(save-excursion (sdml-forward-sym) (sdml-forward-spaces)
			(sdml-forward-sym))
      ;; We're inside a "non function declaration": let's skip all other
      ;; declarations that we find at the same level and try again.
      (sdml-skip-siblings)
      ;; Obviously, let's not try again if we're at bobp.
      (unless (bobp) (sdml-beginning-of-defun)))))

(defcustom sdml-max-name-components 3
  "Maximum number of components to use for the current function name."
  :group 'sdml
  :type 'integer)

(defun sdml-current-fun-name ()
  (save-excursion
    (let ((count sdml-max-name-components)
	  fullname name)
      (end-of-line)
      (while (and (> count 0)
		  (setq name (sdml-beginning-of-defun)))
	(decf count)
	(setq fullname (if fullname (concat name "." fullname) name))
	;; Skip all other declarations that we find at the same level.
	(sdml-skip-siblings))
      fullname)))



;;; INSERTING PROFORMAS (COMMON SDML-FORMS)

(defvar sdml-forms-alist nil
  "*Alist of code templates.
You can extend this alist to your heart's content.  For each additional
template NAME in the list, declare a keyboard macro or function (or
interactive command) called 'sdml-form-NAME'.
If 'sdml-form-NAME' is a function it takes no arguments and should
insert the template at point\; if this is a command it may accept any
sensible interactive call arguments\; keyboard macros can't take
arguments at all.  Apropos keyboard macros, see `name-last-kbd-macro'
and `sdml-addto-forms-alist'.
`sdml-forms-alist' understands let, local, case, datatype,
signature, structure, and functor by default.")

(defmacro sdml-def-skeleton (name interactor &rest elements)
  (when (fboundp 'define-skeleton)
    (let ((fsym (intern (concat "sdml-form-" name))))
      `(progn
	 (add-to-list 'sdml-forms-alist ',(cons name fsym))
	 (define-abbrev sdml-mode-abbrev-table ,name "" ',fsym)
	 (define-skeleton ,fsym
	   ,(format "SDML-mode skeleton for `%s..' expressions" name)
	   ,interactor
	   ,(concat name " ") >
	   ,@elements)))))
(put 'sdml-def-skeleton 'lisp-indent-function 2)

(sdml-def-skeleton "let" nil
  @ "\nin " > _ "\nend" >)

(sdml-def-skeleton "if" nil
  @ " then " > _ "\nelse " > _)

(sdml-def-skeleton "local" nil
  @ "\nin" > _ "\nend" >)

(sdml-def-skeleton "case" "Case expr: "
  str "\nof " > _ " => ")

(sdml-def-skeleton "signature" "Signature name: "
  str " =\nsig" > "\n" > _ "\nend" >)

(sdml-def-skeleton "structure" "Structure name: "
  str " =\nstruct" > "\n" > _ "\nend" >)

(sdml-def-skeleton "functor" "Functor name: "
  str " () : =\nstruct" > "\n" > _ "\nend" >)

(sdml-def-skeleton "datatype" "Datatype name and type params: "
  str " =" \n)

;;

(sdml-def-skeleton "struct" nil
  _ "\nend" >)

(sdml-def-skeleton "sig" nil
  _ "\nend" >)

(sdml-def-skeleton "val" nil
  @ " = " > _)

(sdml-def-skeleton "fn" nil
  @ " =>" > _)

(sdml-def-skeleton "fun" nil
  @ " =" > _)

;;

(defun sdml-forms-menu (menu)
  (mapcar (lambda (x)
	    (let ((name (car x))
		  (fsym (cdr x)))
	      (vector name fsym t)))
	  sdml-forms-alist))

(defvar sdml-last-form "let")

(defun sdml-electric-space ()
  "Expand a symbol into an SDML form, or just insert a space.
If the point directly precedes a symbol for which an SDML form exists,
the corresponding form is inserted."
  (interactive)
  (let ((abbrev-mode (not abbrev-mode))
	(last-command-char ?\ )
	;; Bind `this-command' to fool skeleton's special abbrev handling.
	(this-command 'self-insert-command))
    (call-interactively 'self-insert-command)))

(defun sdml-insert-form (name newline)
  "Interactive short-cut to insert the NAME common ML form.
If a prefix argument is given insert a NEWLINE and indent first, or
just move to the proper indentation if the line is blank\; otherwise
insert at point (which forces indentation to current column).

The default form to insert is 'whatever you inserted last time'
\(just hit return when prompted\)\; otherwise the command reads with
completion from `sdml-forms-alist'."
  (interactive
   (list (completing-read
	  (format "Form to insert: (default %s) " sdml-last-form)
	  sdml-forms-alist nil t nil)
	 current-prefix-arg))
  ;; default is whatever the last insert was...
  (if (string= name "") (setq name sdml-last-form) (setq sdml-last-form name))
  (unless (or (not newline)
	      (save-excursion (beginning-of-line) (looking-at "\\s-*$")))
    (insert "\n"))
  (unless (/= ?w (char-syntax (preceding-char))) (insert " "))
  (let ((f (cdr (assoc name sdml-forms-alist))))
    (cond
     ((commandp f) (command-execute f))
     (f (funcall f))
     (t (error "Undefined form: %s" name)))))

;; See also macros.el in emacs lisp dir.

(defun sdml-addto-forms-alist (name)
  "Assign a name to the last keyboard macro defined.
Argument NAME is transmogrified to sdml-form-NAME which is the symbol
actually defined.

The symbol's function definition becomes the keyboard macro string.

If that works, NAME is added to `sdml-forms-alist' so you'll be able to
reinvoke the macro through \\[sdml-insert-form].  You might want to save
the macro to use in a later editing session -- see `insert-kbd-macro'
and add these macros to your .emacs file.

See also `edit-kbd-macro' which is bound to \\[edit-kbd-macro]."
  (interactive "sName for last kbd macro (\"sdml-form-\" will be added): ")
  (when (string= name "") (error "No command name given"))
  (let ((fsym (intern (concat "sdml-form-" name))))
    (name-last-kbd-macro fsym)
    (message "Macro bound to %s" fsym)
    (add-to-list 'sdml-forms-alist (cons name fsym))))

;;;###autoload(add-to-list 'auto-mode-alist '("\\.grm\\'" . sdml-yacc-mode))
;; XEmacs hack, autoload a dummy autoload instead of a derived mode.




;;
;; Code to handle nested comments and unusual string escape sequences
;;

(defsyntax sdml-syntax-prop-table
  '((?\\ . ".") (?* . "."))
  "Syntax table for text-properties")

;; For Emacsen that have no built-in support for nested comments
(defun sdml-get-depth-st ()
  (save-excursion
    (let* ((disp (if (eq (char-before) ?\)) (progn (backward-char) -1) nil))
	   (foo (backward-char))
	   (disp (if (eq (char-before) ?\() (progn (backward-char) 0) disp))
	   (pt (point)))
      (when disp
	(let* ((depth
		(save-match-data
		  (if (re-search-backward "\\*)\\|(\\*" nil t)
		      (+ (or (get-char-property (point) 'comment-depth) 0)
			 (case (char-after) (?\( 1) (?* 0))
			 disp)
		    0)))
	       (depth (if (> depth 0) depth)))
	  (put-text-property pt (1+ pt) 'comment-depth depth)
	  (when depth sdml-syntax-prop-table))))))

(defconst sdml-font-lock-syntactic-keywords
  `(("^\\s-*\\(\\\\\\)" (1 ',sdml-syntax-prop-table))
    ,@(unless sdml-builtin-nested-comments-flag
	'(("(?\\(\\*\\))?" (1 (sdml-get-depth-st)))))))

(defconst sdml-font-lock-defaults
  '(sdml-font-lock-keywords nil nil ((?_ . "w") (?' . "w")) nil
    (font-lock-syntactic-keywords . sdml-font-lock-syntactic-keywords)))




;;; sdml-mode.el ends here



(defconst sdml-keywords-regexp
  (sdml-syms-re "and" "andalso" "as"
                "case"
                "datatype" "datasort" "datacon" "do"
                "else" "end"
                "fn" "fun"
                "handle" "hint"
                "if" "in"
                "indexsort" "indexfun" "indexconstant" "indexpred"
                "let" "local"
                "nonfix"
                "of" "op" "orelse"
                "primtive"
                "raise" "rec"
                "some"
                "test'subtype" "then" "try" "type"
                "val"
                "where" "with" "withtype"))
  
(defconst sdml-tyvarseq-re
  "\\(\\('+\\(\\sw\\|\\s_\\)+\\|(\\([,']\\|\\sw\\|\\s_\\|\\s-\\)+)\\)\\s-+\\)?")

(defun sdml-turn-on-fontlock ()
   (set-face-bold-p 'font-lock-keyword-face 't)
   (copy-face 'font-lock-keyword-face 'sdml-eq-face)
;   (set-face-foreground 'sdml-eq-face "dark blue")
   (make-face 'Purple)
   (copy-face 'font-lock-keyword-face 'sdml-fun-face)
   (set-face-foreground 'sdml-fun-face "black")
   (set-face-bold-p 'sdml-fun-face 't)
   (set-face-foreground 'font-lock-keyword-face "black")
   (set-face-underline-p 'sdml-fun-face 't)

   (copy-face 'font-lock-type-face 'sdml-list-face)
   (set-face-highlight-p 'sdml-list-face nil 'global 'tty)
 
   (copy-face 'font-lock-type-face 'sdml-unit-face)
   (set-face-bold-p 'sdml-unit-face 't)
   (set-face-foreground 'sdml-unit-face "cyan")
   (set-face-highlight-p 'sdml-list-face nil 'global 'tty)

   (copy-face 'font-lock-keyword-face 'sdml-ordinary-face)
   (set-face-bold-p 'sdml-ordinary-face 't)
   (set-face-foreground 'sdml-ordinary-face "gray22")

   (copy-face 'font-lock-keyword-face 'sdml-quantifier-face)
   (set-face-bold-p 'sdml-quantifier-face 't)
   (set-face-foreground 'sdml-quantifier-face "snow4")

   (copy-face 'font-lock-keyword-face 'sdml-definite-face)
   (set-face-bold-p 'sdml-definite-face 't)
   (set-face-foreground 'sdml-definite-face "blue3")

   (copy-face 'font-lock-keyword-face 'sdml-indefinite-face)
   (set-face-bold-p 'sdml-indefinite-face 't)
   (set-face-foreground 'sdml-indefinite-face "red4")
       (copy-face 'sdml-indefinite-face 'sdml-union-face)
       (set-face-bold-p 'sdml-union-face 't)

   (copy-face 'font-lock-keyword-face 'sdml-top-face)
   (set-face-bold-p 'sdml-top-face 't)
   (set-face-foreground 'sdml-top-face "blue2")

   (copy-face 'font-lock-keyword-face 'sdml-bot-face)
   (set-face-bold-p 'sdml-bot-face 't)
   (set-face-foreground 'sdml-bot-face "red3")
   
   (copy-face 'sdml-definite-face 'sdml-un-quantifier-face)
;   (set-face-foreground 'sdml-un-quantifier-face "DarkOliveGreen4")

   (copy-face 'sdml-indefinite-face 'sdml-ex-quantifier-face)
;   (set-face-foreground 'sdml-ex-quantifier-face "MediumPurple")

   (make-face 'DarkOliveGreen)
   (copy-face 'font-lock-keyword-face 'sdml-module-face)
   (set-face-foreground 'sdml-module-face "DarkOliveGreen4")
   (set-face-underline-p 'sdml-module-face 't)

   (setq font-lock-keywords
     `(
        (,(concat "\\<\\(fun\\|and\\)\\s-+" "\\([A-Za-z0-9_']+\\)\\s-+[^ \t\n=]")
         (1 font-lock-keyword-face)
         (2 font-lock-function-name-face))
        (,(concat "\\<\\(type\\|withtype\\|datatype\\)\\s-+" "\\([A-Za-z0-9_']+\\)")
         (1 font-lock-keyword-face)
         (2 font-lock-type-def-face))
        ("\\<\\(val\\)\\s-+\\([A-Za-z0-9_']+\\)\\s-*[:]"    ;  val type declaration
         (1 font-lock-keyword-face)
         (2 font-lock-function-name-face))
        ("\\<\\(val\\)\\s-+\\([A-Za-z0-9_']+\\)\\s-*[=]"    ;  val declaration
         (1 font-lock-keyword-face)
         ;;(6 font-lock-variable-def-face nil t)
         (2 font-lock-variable-name-face));    ("\\<\\(signature\\)\\s-+\\(\\sw+\\)"
    ;     (1 font-lock-keyword-face)
    ;     (2 font-lock-interface-def-face))    

        ("=>" . sdml-eq-face)
        ("| " . sdml-eq-face)
        ("()" . sdml-unit-face)

        ("[^&]\\(&\\)[^&]" . sdml-definite-face)
        ("^\\(&\\)[^&]" . sdml-definite-face)
        ("[^&]\\(&&\\)[^&]" . sdml-definite-face)
        ("^\\(&&\\)[^&]" . sdml-definite-face)

        ("[^/]\\(/\\)[^/]" . sdml-union-face)
        ("^\\(/\\)[^/]" . sdml-union-face)
        ("[^/]\\(//\\)[^/]" . sdml-union-face)
        ("^\\(//\\)[^/]" . sdml-union-face)

        ("\\<top\\>" . sdml-top-face)
        ("\\<bot\\>" . sdml-bot-face)

        (":!" . sdml-bot-face)

    ;    ("\\<\\[\\>" . sdml-indefinite-face)
    ;    ("\\<\\]\\>" . sdml-indefinite-face)
        ("{{" . sdml-definite-face)
        ("}}" . sdml-definite-face)

        ("->" . sdml-ordinary-face)
        ("*" . sdml-ordinary-face)

        (,(concat "\\(-\\)\\(\\<all\\)\\>")
         (1 sdml-quantifier-face)
         (2 sdml-un-quantifier-face))
        (,(concat "\\(-\\)\\(\\<exists\\)\\>")
         (1 sdml-quantifier-face)
         (2 sdml-ex-quantifier-face))
        ("\\>- " . sdml-quantifier-face)

        (,sdml-keywords-regexp . font-lock-keyword-face))
             )
   (font-lock-mode))

;; font-lock setup

(defface font-lock-type-def-face
  '((t (:bold t)))
  "Font Lock mode face used to highlight type definitions."
  :group 'font-lock-highlighting-faces)
(defvar font-lock-type-def-face 'font-lock-type-def-face
  "Face name to use for type definitions.")

(defface font-lock-module-def-face
  '((t (:bold t)))
  "Font Lock mode face used to highlight module definitions."
  :group 'font-lock-highlighting-faces)
(defvar font-lock-module-def-face 'font-lock-module-def-face
  "Face name to use for module definitions.")

(defface font-lock-interface-def-face
  '((t (:bold t)))
  "Font Lock mode face used to highlight interface definitions."
  :group 'font-lock-highlighting-faces)
(defvar font-lock-interface-def-face 'font-lock-interface-def-face
  "Face name to use for interface definitions.")




(add-hook 'sdml-mode-hook 'sdml-turn-on-fontlock)


(provide 'sdml-font)
(provide 'sdml-mode)
