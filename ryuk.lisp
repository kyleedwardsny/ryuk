(defclass cache-entry ()
  ((name
    :initarg :name
    :initform (error "Must supply a name"))
   (value
    :initarg :value
    :initform (error "Must supply a value"))
   (description
    :initarg :description
    :initform nil)))

(defmethod initialize-instance :before ((entry cache-entry) &key name description)
  (cond ((not (stringp name))
         (error "Name must be a string"))
        ((not (or (stringp description) (null description)))
         (error "Description must be a string or nil"))))

(defclass cache ()
  ((entries
    :initform (make-hash-table :test 'equal))))

(defmethod cache-entry ((cache cache) name)
  (gethash name (slot-value cache 'entries)))

(defun (setf cache-entry) (value (cache cache) name)
  (setf (gethash name (slot-value cache 'entries)) value))

(defmethod read-cache-file ((cache cache) filename)
  (with-open-file (fin filename)
    (loop
      (handler-case
        (let* ((entry (read fin))
               (parsed-entry (parse-cache-entry entry))
               (name (slot-value parsed-entry 'name)))
          (setf (cache-entry cache name) parsed-entry))
        (end-of-file (e) (return))))))

(defun parse-cache-entry (entry)
  (if (and (consp entry)
           (consp (cdr entry))
           (equal (car entry) 'cache-entry))
      (apply 'make-instance 'cache-entry (cdr entry))
      (error "Invalid cache entry")))

(defclass executable ()
  ((name
    :initarg :name
    :initform (error "Must supply a name"))
   (sources
    :initarg :sources
    :initform (error "Must supply sources"))))

(defun parse-executable (&key name sources)
  (make-instance 'executable :name name :sources (cadr sources)))

(defun parse-build-file (targets filename)
  (with-open-file (fin filename)
    (loop
      (handler-case
        (let* ((entry (read fin)))
          (cond ((equal (car entry) 'executable)
                 (let ((exe (apply 'parse-executable (cdr entry))))
                   (setf (gethash (slot-value exe 'name) targets) exe)))
                (t (error "Invalid directive"))))
        (end-of-file (e) (return))))))

; Parse build.ryuk
(defvar *targets* (make-hash-table :test 'equal))
(parse-build-file *targets* "build.ryuk")

; Write ninja file
(defun write-target (build.ninja target)
  (let ((objects-str ""))
    (loop for source in (slot-value target 'sources)
      do (let ((object (concatenate 'string ".ryuk/" (slot-value target 'name) "/" source ".o")))
           (setf objects-str (concatenate 'string objects-str " " object))
           (format build.ninja "build ~a: cc ~a~%" object source)))
    (format build.ninja "build ~a: ld~a~%" (slot-value target 'name) objects-str)))
(with-open-file (build.ninja "build.ninja" :direction :output)
  (format build.ninja "rule cc~%  command = /usr/bin/gcc -c $in -o $out~%rule ld~%  command = /usr/bin/gcc $in -o $out~%")
  (maphash #'(lambda (key val)
               (write-target build.ninja val))
           *targets*))
