(defpackage :spec
  (:export
   :sources
   :object-list
   :target
   :object-lists
   :targets
   :spec
   :read-spec-file
   :environment
   :add-definition
   :definitions
   :functions
   :evaluate))

(defpackage :kira
  (:export
   :compile
   :executable
   :list
   :quote))

(defpackage :kira-user
  (:use :kira))

(in-package :spec)

; --------------------------
; An evaluation environment.
; --------------------------

(defclass environment ()
  ((definitions
    :reader definitions
    :initform (make-hash-table))
   (functions
    :reader functions
    :initform (make-hash-table))
   (spec
    :reader spec
    :initform (make-instance 'spec))))

(defmethod initialize-instance :after ((env environment) &key)
  (add-function env 'kira:list 'evaluate-list)
  (add-function env 'kira:quote 'evaluate-quote)
  (add-function env 'kira:compile 'evaluate-compile)
  (add-function env 'kira:executable 'evaluate-executable))

(defmethod add-function ((env environment) (name symbol) (func symbol))
  (setf (gethash name (functions env)) func))

(defmethod add-definition ((env environment) (name symbol) value)
  (if (not name)
    (error "Variable name must not be nil"))
  (if (not (eql (symbol-package name) (find-package :kira-user)))
    (error "Invalid package for variable"))
  (multiple-value-bind (old-value found) (gethash name (definitions env))
    (if found
      (error "Variable is already declared"))
    (setf (gethash name (definitions env)) value)))

(defmethod get-definition ((env environment) (name symbol))
  (multiple-value-bind (value found) (gethash name (definitions env))
    (if (not found)
      (error "Could not find variable"))
    value))

(defmethod evaluate-function ((env environment) (form list))
  (let* ((name (car form))
         (args (cdr form))
         (all-args (cons env args)))
    (multiple-value-bind (fn found) (gethash name (functions env))
      (if (not found)
        (error "Could not find function"))
      (apply fn all-args))))

(defmethod evaluate ((env environment) form)
  (cond
    ((not form) nil)
    ((stringp form) form)
    ((numberp form) form)
    ((keywordp form) form)
    ((and
       (symbolp form)
       (eql (symbol-package form) (find-package :kira-user)))
     (get-definition env form))
    ((listp form)
     (evaluate-function env form))
    (t (error "Invalid value"))))

; -------------------------
; Functions for evaluation.
; -------------------------

(defmethod evaluate-list ((env environment) &rest args)
  (loop for item in args collect (evaluate env item)))

(defmethod evaluate-quote ((env environment) arg) arg)

(defmethod evaluate-compile ((env environment) name &key language)
  (let ((parsed (make-instance 'object-list :language language)))
    (setf (gethash name (object-lists (spec env))) parsed)
    (add-definition env name parsed)

    parsed))

(defun evaluate-executable ((env environment) name &key objects)
  (let ((parsed (make-instance 'target :name name :type :executable)))
    (loop for obj-list in (evaluate env objects) do
      (if (not (typep obj-list 'object-list))
        (error "Value is not an object list"))
      (setf (object-lists parsed) (cons obj-list (object-lists parsed))))

    (setf (gethash name (targets (spec env))) parsed)
    (add-definition env name parsed)

    parsed))

; ----------------------------------------
; A list of objects to build from sources.
; ----------------------------------------

(defclass object-list ()
  ((sources
    :accessor sources
    :initform nil)
   (language
    :accessor language
    :initarg :language
    :initform (error "Must supply a compile language"))))

; ----------------------------------------------------
; A description of a target from a specification file.
; ----------------------------------------------------

(defclass target ()
  ((name
    :reader name
    :initarg :name
    :initform (error "Must supply a name"))
   (type
    :reader type
    :initarg :type
    :initform (error "Must supply a type"))
   (object-lists
    :accessor object-lists
    :initform nil)))

; ----------------------
; A build specification.
; ----------------------

(defclass spec ()
  ((object-lists
    :reader object-lists
    :initform (make-hash-table))
   (targets
    :reader targets
    :initform (make-hash-table))))

; ---------------------------------------
; Read a build specification from a file.
; ---------------------------------------

(defun read-spec-file (fin)
  (let ((env (make-instance 'environment))
        (object-lists nil)
        (targets nil)
        (obj nil))
    ; Read the entire spec file
    (loop
      (handler-case
        (let ((*package* (find-package :kira-user)))
          (setf obj (read fin)))
        (end-of-file (e) (return)))
      (evaluate env obj))

    ; Done
    (spec env)))
