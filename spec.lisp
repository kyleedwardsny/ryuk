(defpackage :spec
  (:export
   :sources
   :object-list
   :target
   :object-lists
   :targets
   :spec
   :read-spec-file))

(defpackage :kira
  (:export
   :compile
   :executable))

(in-package :spec)

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
  (let ((spec (make-instance 'spec))
        (object-lists nil)
        (targets nil)
        (obj nil))
    ; Read the entire spec file
    (let ((*package* (find-package :kira)))
      (loop
        (handler-case
          (setf obj (read fin))
          (end-of-file (e) (return)))
        (cond 
          ((eql (car obj) 'kira:compile)
           (setf object-lists (cons obj object-lists)))
          ((eql (car obj) 'kira:executable)
           (setf targets (cons obj targets)))
          (t (error "Invalid spec directive")))))

    ; Create the object lists
    (loop for obj-list in object-lists do
      (multiple-value-bind (name parsed) (parse-object-list spec obj-list)
        (setf (gethash name (slot-value spec 'spec:object-lists)) parsed)))

    ; Create the targets
    (loop for tgt in targets do
      (multiple-value-bind (name parsed) (parse-target spec tgt)
        (setf (gethash name (slot-value spec 'spec:targets)) parsed)))

    ; Done
    spec))

(defun parse-object-list (spec obj-list)
  (apply
    #'(lambda (name &key language)
      (let ((parsed (make-instance 'object-list :language language)))
        ; TODO Parse more arguments

        (values name parsed))) (cdr obj-list)))

(defun parse-target (spec target)
  (apply
    #'(lambda (name &key objects)
      (if (not (eql (car objects) 'list)) (error "objects must be a list"))
      (let ((parsed (make-instance 'target :name name :type (car target))))
        (loop for obj-name in (cdr objects) do
          (print obj-name)
          (multiple-value-bind (obj-list found) (gethash obj-name (object-lists spec))
            (if (not found) (error "Unknown object list"))
            (setf (object-lists parsed) (cons obj-list (object-lists parsed)))))

        (values name parsed))) (cdr target)))
