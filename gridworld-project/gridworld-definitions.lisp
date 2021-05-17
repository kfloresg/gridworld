;; Code used is from Gridworld project code by Lenhart Schubert and Daphne Liu
;; Some comments fromt the original documentation were taken for simplicity 
;; Comments provided with some functions specify where code was added to the original 

(defparameter *roadmap-knowledge* nil) 
(defparameter *general-knowledge* nil) 
(defparameter *extra-initial-knowledge* (make-hash-table :test #'equal))
(defparameter *world-facts* (make-hash-table :test #'equal))
(defparameter *protected-facts* (make-hash-table :test #'equal))

;;TODO: Change predicates that are better suited to the library agent 
(defvar *occluded-preds* '(likes contains is_playable is_edible is_potable))

(defvar *epistemic-preds* '(knows is_obligated_to believes wants))
(defvar *visited-places* nil) 
(defvar *visited-objects* nil) 

(defparameter *left-comoving-preds* '(is_in))
(defparameter *right-comoving-preds* '(has))

;; Defines locations of objects and builds a roadmap 
(defun def-roadmap (points roads)
  (let (tuple name pt-dist-list pt-list dist-list curr trimmed-pt-list road-points leng pt2 pt2 currleng isolated-points unlisted-points rr rc)
    (clrhash *extra-initial-knowledge*) 
    (clrhash *roadmap-knowledge*) 
    (clrhash *world-facts*)
    (clrhash *protected-facts*)
    (setq *general_knowledge* nil) 
    
    (dolist (p points) (remprop p 'next))
    (dolist (r roads)
      (setq name (car r)) 
      (setq pt-dist-list (cdr r))
      (setq pt-list '())
      (setq leng (length pt-dist-list))
      (dotimes (i leng t)
	(setq curr (nth i pt-dist-list))
	(if (evenp i)
	  (if (symbolp curr)
	    (push curr pt-list) 
	    (progn (format t "~%**Road ~a is missing valid segment" name) 
		   (return-from def-roadmap 'ERROR_TERMINATION))))
	(setq trimmed-pt-list (remove-duplicates pt-list))
	(when (< (length trimmed-pt-list) (length pt-list))
	  (format t "~%***Road ~a is self-intersecting" name) 
	  (return-from def-roadmap 'ERROR-TERMINATION))
	(when (not (= (- (length pt-list) 1) (length dist-list))) 
	  (format t "~%***Road ~a is missing a valid segment or distance" name) 
	  (return-from def-roadmap 'ERROR-TERMINATION))
	(setq road-points (union pt-list road-points))
	
	(add_tuple_to_hashtable (cons 'road (list name)) *roadmap-knowledge* 'NIL)
	(add_tuple_to_hashtable (cons 'navigable (list name)) *roadmap-knowledge* 'NIL)
	(setq pt1 (pop pt-list))
	(add_tuple_to_hashtable (list 'is_on pt1 name) *roadmap-knowledge* 'NIL) 
	(while (> (length pt-list) 0)
	       (setq pt2 (pop pt-list))
	       (add_tuple_to_hashtable (list 'is_on pt2 name) *roadmap-knowledge* 'NIL) 
	       (setq currleng (pop dist-list)) 
	       (push (list name pt2 currleng) (get pt1 'next))
	       (push (list name pt1 currleng) (get pt2 'next))
	       (setq pt1 pt2)))

      (setq isolated-points (set-difference points road-points))
      (setq unlisted-points (set-difference road-points points))
      (if isolated-points 
	(format t "~%### ISOLATED POINTS: ~a" isolated-points))
      (if unlisted-points 
	(format t "~%### UNLISTED POINTS ON ROADS: ~a" unlisted-points))
      (dolist (p (unionof road-points isolated-points))
	(add_tuple_to_hashtable (list 'point p) *roadmap-knowledge* 'NIL)) 
      
      (add_htable_to_hashtable *roadmap-knowledge* *world-facts* 'NIL)
      (add_htable_to_hashtable *roadmap-knowledge* *protected-facts* 'NIL)

      (push (list (list 'tells '?x (list 'that '?y)) '=> '?y) *general-knowledge*) 
      (push (list (list 'knows '?x (list 'that '?y)) '=> '?y) *general-knowledge*)))

(defun def-object (obj-type properties) 
  (let ((ante (list obj-type '?x)) conse)
    (dolist (p properties) 
      (setq conse
	    (if (atom p)
	      (list p '?x)
	      (cons (car p) (cons '?x (cdr p)))
	      ))
      (push (list ante '=> conse) *general-knowledge*))))

(defun place-object (name obj-type point time-pt associated-things curr-facts propos-attitudes) 
  (let (facts list-of-terms-in-added-tuple) 
    (push (list obj-type name) facts)
    (push (list 'is_at name point) facts)
    (if (eq name 'AG) (setq *here* point *AG-clock* time-pt))
    (dolist (p associated-things)
      (push p facts)
      (push (list 'is_at (second p) point) facts)
      (push (list 'has_name (second p)) facts))

    (dolist (f (remove-duplicates curr-facts :test #'equal))
      (push f facts) 
      (when (and (eq name 'AG) (not (eq (second f) 'AG)))
	(add_tuple_to_hashtable f *extra-initial-knowledge* 'NIL)))

    (dolist (f propos-attitudes) (push f facts))

    (setq facts (remove-duplicates facts :test #'equal))
    (dolist (f facts)
      (add_tuple_to_hashtable f *world-facts* 'NIL)
      (add_tuple_to_hashtable f *protected-facts* 'NIL))))


