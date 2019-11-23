(defpackage :ninja
  (:export
   :escape
   :escape-path
   :escape-for-build
   :build
   :rule
   :explicit-outs
   :implicit-outs
   :explicit-deps
   :implicit-deps
   :order-only-deps
   :vars))

(in-package :ninja)

; ------------------------------------
; Check that a variable name is valid.
; ------------------------------------

(defun check-variable-name (str)
  (map nil
    #'(lambda (c)
      (let ((valid nil))
        (cond
          ((and (char>= c #\A) (char<= c #\Z)) (setf valid t))
          ((and (char>= c #\a) (char<= c #\z)) (setf valid t))
          ((and (char>= c #\0) (char<= c #\9)) (setf valid t))
          ((find c '(#\_ #\- #\.)) (setf valid t)))
        (if (not valid) (error "Invalid variable name")))) str))

; ------------------------------------------
; Escape a single character given the table.
; ------------------------------------------

(defun escape-char (c table)
  (if (find c '(#\Return #\Linefeed #\Newline))
    (error "Cannot escape newline for Ninja"))
  (multiple-value-bind (val found) (gethash c table)
    (if found
      val
      (string c))))

; --------------------------------------
; Escape a whole string given the table.
; --------------------------------------

(defun escape-private (str table)
  (let ((result ""))
    (map nil
      #'(lambda (c)
        (setf result (concatenate 'string result (escape-char c table)))
        nil)
      str)
    result))

; -----------------------------------
; Create tables for escape functions.
; -----------------------------------

(defun make-escape-table ()
  (let ((result (make-hash-table)))
    (setf (gethash #\$ result) "$$")
    result))

(defvar *escape-table* (make-escape-table))

(defun make-escape-path-table ()
  (let ((result (make-escape-table)))
    (setf (gethash #\  result) "$ ")
    result))

(defvar *escape-path-table* (make-escape-path-table))

(defun make-escape-for-build-table ()
  (let ((result (make-escape-path-table)))
    (setf (gethash #\: result) "$:")
    result))

(defvar *escape-for-build-table* (make-escape-for-build-table))

; --------------------------------------
; Escape a string for ordinary contexts.
; --------------------------------------

(defun escape (str)
  (escape-private str *escape-table*))

; ---------------------------
; Escape a string for a path.
; ---------------------------

(defun escape-path (str)
  (escape-private str *escape-path-table*))

; ---------------------------------
; Escape a string for a build line.
; ---------------------------------

(defun escape-for-build (str)
  (escape-private str *escape-for-build-table*))

; -----------------------------------
; An object describing a Ninja build.
; -----------------------------------

(defclass build ()
  ((rule
    :reader rule
    :initarg :rule
    :initform (error "Must supply a rule"))
   (explicit-outs
    :accessor explicit-outs
    :initform nil)
   (implicit-outs
    :accessor implicit-outs
    :initform nil)
   (explicit-deps
    :accessor explicit-deps
    :initform nil)
   (implicit-deps
    :accessor implicit-deps
    :initform nil)
   (order-only-deps
    :accessor order-only-deps
    :initform nil)
   (vars
    :reader vars
    :initform (make-hash-table :test 'equal))))

; ------------------------------------------------
; Write a hash table of variables to a Ninja file.
; ------------------------------------------------

(defun write-variables (vars indent file)
  (let ((pairs nil))
    (maphash
      #'(lambda (key value)
        (setf pairs (cons `(,key ,value) pairs)))
      vars)
    (sort pairs #'string-lessp :key #'(lambda (pair) (car pair)))

    (loop for pair in pairs do
      (check-variable-name (car pair))
      (format file "~a~a = ~a~%" indent (car pair) (escape (cadr pair))))))

; ----------------------------------------
; Write a build statement to a Ninja file.
; ----------------------------------------

(defmethod write-to-file ((build build) file)
  (if (not (explicit-outs build))
    (error "Build must supply at least one explicit output"))

  (format file "build")
  (loop for out in (explicit-outs build) do
    (format file " ~a" (escape-for-build out)))

  (if (implicit-outs build)
    (progn
      (format file " |")
      (loop for out in (implicit-outs build) do
        (format file " ~a" (escape-for-build out)))))

  (format file ": ~a" (rule build))

  (if (explicit-deps build)
    (loop for dep in (explicit-deps build) do
      (format file " ~a" (escape-for-build dep))))

  (if (implicit-deps build)
    (progn
      (format file " |")
      (loop for dep in (implicit-deps build) do
        (format file " ~a" (escape-for-build dep)))))

  (if (order-only-deps build)
    (progn
      (format file " ||")
      (loop for dep in (order-only-deps build) do
        (format file " ~a" (escape-for-build dep)))))

  (format file "~%")
  (write-variables (vars build) "  " file))
