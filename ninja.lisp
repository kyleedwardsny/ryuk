(defpackage :ninja
  (:export :escape :escape-path :escape-for-build))

(in-package :ninja)

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
