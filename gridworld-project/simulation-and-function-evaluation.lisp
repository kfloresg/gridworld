(DEFUN MEMB (A LAT)
       (COND ((NULL LAT) NIL)
	     ((EQ A (CAR LAT)) T)
	     (T (MEMB A (CDR LAT)))
	     ))

(defun convert_pred_to_hashkey (pred)
  (if (atom pred) 
    pred
    (mapcar #'gen_hashkey_symbol (flatten pred))
    ))

(defun gen_hashkey_symbol (symb)
  (if (var symb)
	   'NIL
	   symb))

(defun generate_allkeys_from_hashkey (thekey) 
  (let ((result (list thekey))
	(num-elements 0)
	(startposn 1) 
	(counter 0)
	(first-arg-posn 1)
	(last-arg-posn 1)
	(init-key-seq 'NIL)
	(new-key 'NIL)
	(accum 'NIL)
	(curr-arg 'NIL)
	posn-reified
	reified-keys)
    (when (atim thekey) (return-from generate_allkeys_from_hashkey result))
    (setq num-elements (length thekey))
    (when (or (<= num-elements 1) (and (= num-elements 2) (eq (car thekey) 'not))))
    (setq posn-reified (position 'that thekey))
    (when (numberp posn-reified) 
      (setq new-key (first-n thekey posn-reified))
      (push (append new-key '(nil)) result)
      (push (append new-key '(that nil)) reified-key)
    )
    (setq posn-reified (position 'whether thekey))
    (when (numberp posn-reified)
      (setq new-key (first-n thekey posn-reified))
      (push (append new-key '(nil)) result)
      (push (append new-key '(whether nil)) reified-keys)
      )

    (when (null reified-keys)
      (push thekey reified-keys)
      )

    (dolist (key reified-keys)
      (setq num-elements (length key)
	    that-posns 'NIL
	    whether-posns 'NIL)
      (if (eq (car key) 'not)
	(progn 
	  (setq startposn 2)
	  (decf num-elements 2)
	  (setq init-key-seq (list (first key) (second key)))
	  )
	(progn 
	  (setq startposn 1)
	  (decf num-elements 1)
	  (setq init-key-seq (list (first key)))
	  ))

      (setq first-arg-posn startposn) 
      (setq last-arg-posn (- (+ first-arg-posn num-elements) 1))
      (setq new-key init-key-seq)
      (push new-key result)

      (setq counter first-arg-posn)
      (while (<= counter last-arg-posn)
	     (cond ((eq (nth counter key) 'that)
		    (push counter that-posns) )
		   ((eq (nth counter key) 'whether)
		    (push counter whether-posns)))
	     (incf counter 1))

      (dotimes (i num-elements) 
	(setq curr-arg (nth startposn key))
	(setq counter first-arg-posn)
	(setq accum 'NIL)
	(while (< counter startposn)
	       (case (nth counter key)
		 ('that (setq accum (append accum '(that))))
		 ('whether (setq accum (append accum '(whether))))

		 (t (setq accum (append accum '(nil))))
		 )
	       (incf counter 1))
	(setq new-key (append init-key-seq (append accum (list curr-arg))))

	(setq accum 'NIL)
	(setq counter (+ startposn 1))

	(while (<= counter last-arg-posn)
	       (case (nth counter key) 
		 ('that (setq accum (append accum '(that))))
		 ('whether (setq accum (append accum '(whether))))
		 (t (setq accum (append accum '(nil))))
		 )
	       (incf counter 1)
	       )

	(setq new-key (append new-key accum))
	(push new-key result)
	(incf startposn 1)
	)
      (when (> num-elements 0)
	(setq counter first-arg-posn)
	(setq accum 'NIL)
	(while (<= counter last-arg-posn)
	       (case (nth counter key) 
		 ('that (setq accum (append accum '(that))))
		 ('whether (setq accum (append accum '(whether))))
		 (t (setq accum (append accum '(nil))))
		 )
	       (incf counter 1)
	       )
	(setq new-key (append init-key-seq accum))
	(push new-key result)))
    (remove-duplicates result :test #'equal)))

(defun contains_reified (rei-op key)
  (cond ((atom key) 'NIL)
	((numberp (position rei-op key)) 'T)
	(t 'NIL)

	))

(defun flatten (lst)
  (cond ((null lst) lst)
	((listp (car lst))
	 (append (flatten (car lst)) (flatten (cdr lst))))
	(t (cons (car lst) (flatten (cdr lst)))) ))

(defun add_tuple_to_hashtable (tuple table to-collect-terms)
  (let ((keys (generate_allkeys_from_hashkey (convert_pred_to_hashkey tuple)))
	new-hash-value old-hash-value all-terms (ct 0))
    (dolist (key keys) 
      (setq old-hash-value (gethash key table))
      (if (not (null old-hash-value))
	(prog2 (setq new-hash-value
		     (unionf (list tuple) (cdr old-hash-value)))
	       (when (and (equal (car new-hash-value) tuple)
			  (not (equal tuple (second old-hash-value))))
		 (setf (gethash key table)
		       (cons (+ 1 (car old-hash-value))
			     new-hash-value))
		 (when (eq to-collect-terms 'T)
		   (incf ct 1) )))
	(prog2 (setf (gethash key table) (list 1 tuple))
	       (when (eq to-collect-terms 'T) (incf ct 1)))))
    (if (> ct 0)
      (make-into-list-of-counts-unique-terms (args tuple) ct) 'NIL)))

(defun add_list_of_tuples_to_hashtable (list-of-tuples table to-collect-terms) 
  (let (list-of-terms-in-added-tuples) 
    (dolist (tuple list-of-tuples) 
      (setq list-of-terms-in-added-tuples
	    (merge_terms_list_with_term_list
	      (add_tuple_to_hashtable tuple table to-collect-terms)
	      list-of-terms-in-added-tuples)))
    list-of-terms-in-added-tuples))

(defun copy_construct_hashtable (old-htable) 
  (let ((new-htable (make-hash-table :test #'equal)))
    (add_htable_to_hashtable old-htable new-table 'NIL)
    new-htable))

(defun make-htable (facts)
  (let ((result (make-hash-table :test #'equal)))
    (dolist (tuple facts)
      (add_tuple_to_hashtable tuple result 'nil))
    result))

(defun make-into-list-of-counts-unique-terms (lst-of-terms &optional (ct 1))
  (let ((result-term-lst 'NIL))
    (dolist (arg lst-of-terms)
      (setq result-term-lst (merge_term_list_with_term_list (list (list ct arg)) result-term-lst))
      )
    result-term-lst))

(defun add_htable_to_hashtable (to-be-added-htable table to-collect-terms)
  (let (old-hash-value new-hash-value new-hash-length old-hash-length
		       (list-of-terms-in-added-tuples 'NIL)
		       cdr-old-hash-value cdr-to-be-added-value)
    (loop for to-be-added-key being the hash-keys of to-be-added-htable using (hash-value to-be-added-value)
	  do
	  (setq old-hash-value (gethash to-be-added-key table))
	  (setq cdr-to-be-added-value (cdr to-be-added-value))
	  (if (not (null old-hash-value))
	    (progn 
	      (setq cdr-old-hash-value (cdr old-hash-value))
	      (setq new-hash-value (unionf cdr-to-be-added-value cdr-old-hash-value))

	      (setq old-hash-length (car old-hash-value))
	      (setq new-hash-length (length new-hash-value))
	      (setf (gethash to-be-added-key table) (cons new-hash-length new-hash-value))

	      (when (and (eq to-collect-terms 'T) (> new-hash-length old-hash-length))
		(setq list-of-terms-in-added-tuples
		      (merge_term_list_with_term_list
			(make-into-list-of-counts-unique-terms
			  (collect-terms-duplicate
			    (set-differencef cdr-to-be-added-value cdr-old-hash-value) ))
			list-of-terms-in-added-tuples))))
	      (prog2 
		(setf (gethash to-be-added-key table) to-be-added-value)
		(when (eq to-collect-terms 'T)
		  (setq list-of-terms-in-added-tuples
			(merge_term_list_with_term_list
			  (make-into-list-of-counts-unique-terms
			    (collect-terms-duplicate cdr-to-be-added-value))
			  list-of-terms-in-added-tuples)))) ))
	  list-of-terms-in-added-tuples))

(defun remove_tuples_from_hashtable (tuple table to-collect-terms) 
  (let ( (keys (generate_allkeys_from_hashkey (convert_pred_to_hashkey tuple)))
	new-hash-value old-hash-value (ct 0))
    (dolist (key keys)
      (setq old-hash-value (gethash key table))
      (when (not (null old-hash-value))
	(setq new-hash-value (remove tuple (cdr old-hash-value) :test #'equal))
	(when (< (length new-hash-value) (car old-hash-value))
	  (when (eq to-collect-terms 'T)
	    (incf ct 1) 
	    )
	  (if (null new-hash-value) 
	    (remhash key table)
	    (setf (gethash key table) (cons (- (car old-hash-value) 1) new-hash-value))
	    ))))
    (if (> ct 0)
      (make-into-list-of-counts-unique-terms (args tuple) ct)
      'NIL)))

(defun remove_list_of_tuples_from_hashtable (list-of-tuples to-collect-terms) 
  (let (list-of-terms-in-removed-tuples)
    (dolist (tuple list-of-tuples) 
      (setq list-of-terms-in-removed-tuples
	    (merge_term_list_with_term_list (remove_tuple_from_hashtable tuple table to-collect-terms) 
					    list-of-terms-in-removed-tuples
					    )))
    list-of-terms-in-removed-tuples))

(defun merge_term_list_with_term_list (lst1 lst2)
  (if (null lst1) (return-from merge_term_list_with_term_list lst2))
  (if (null lst2) (return-from merge_term_list_with_term_list lst1))

  (let* (count_of_term the_term index new_count
		       found_pair (resulting_lst lst2)
		       (list_of_terms (mapcar #'second resulting_lst)))
    (dolist (pair lst1)
      (setq count_of_term (first pair))
      (setq the_term (second pair))
      (setq index (position the_term lst_of_terms))
      (if (numberp index) 
	(prog2 (setq found-pair (nth index resulting_lst))
	       (setq resulting_lst
		     (substitute
		       (list (+ (first found-pair) count_of_term) the_term)
		       found_pair resulting_lst)))
	(prog2 (setq resulting_lst (cons pair resulting_lst))
	       (push the_term lst_of_terms))))
    resulting_lst))

(defun remove_term_list_from_term_list (lst1 lst2)
  (when (OR (null lst1) (null lst2)) (return-from remove_term_list_from_term_list lst2))
  (let* (count_of_term the_term index new_count
		       found_pair new_count
		       (resulting_lst lst2)
		       (lst_of_terms (mapcar #'second resulting_lst)))
    (dolist (pair lst1)
      (setq count_of_term (first pair))
      (setq the_term (second pair))
      (setq index (position the_term lst_of_terms))
      (when (numberp index)
	(setq found_pair (nth index resulting_lst))
	(setq new_count (- (first found_pair) count_of_term))

	(if (> new_count 0)
	  (setq resulting_lst (substitute (list new_count the_term) found_pair resulting_lst))

	  (prog2 (setq resulting_lst (remove found_pair resulting_lst :test #'equal))
		 (setq lst_of_terms (delete the_term lst_of_terms))
		 ))) )
    resulting_lst))

;;;; simulator code ;;;;;;
(defparameter *total-value* 0)
(defparameter *event-queue* nil)
(defparameter *real-clock* 0)
(defparameter *event-timer* 0)

(defstruct op.actual
  name
  instance
  startconds
  stopconds
  deletes
  adds
  starredStopConds
  starredDeletes
  starredAdds
)

(defun current_time? ()
  *real-clock*)

(defun elapsed_time? ()
  *event-timer*
)

(defun price_of? (x)
  (let ((result 0))
    (dolist (wf *world-facts*)
      (when (= 3 (length wf))
	       (when (and (eq 'has_cost (first wf)) (eq x (second wf)))
		 (setq result (third wf))
		 (return-from price_of? result))))
      result
))

(defun generate-ext-op-state-node (action-name state-node-name)
  (let* ((action (eval action-name))
	 (additions (op.actual-adds action))
	 (deletions (op.actual-deletes action))
	 (state-node (eval state-node-name))
	 (old-wff-htable (state-node-wff-htable state-node))
	 (local-value (state-node-local-value state-node))
	 (new-state-node-name (gensym "STATE-NODE"))
	 new-local-value
	 new-forward-value
	 (new-wff-htable (copy_construct_hashtable old-wff-htable))
	 (new-terms (state-node-terms state-node))
	 )
    (setq deletions (set-differencef deletions additions))
    
    (setq new-local-value
	  (state-value additions deletions local-value))

    (setq new-forward-value (expected-rewards old-wff-htable))
    (setq new-terms (remove_term_list_from_term_list
		      (remove_list_of_tuples_from_hashtable deletions new-wff-htable 'T)
		      new-terms))
    (setq new-terms (merge_term_list_with_term_list
		      (add_list_of_tuples_to_hashtable additions new-wff-htable 'T)
		      new-terms))

    (set new-state-node-name
	 (make-state-node
	   :name new-state-node-name
	   :terms new-terms
	   :wff-table new-wf-htable
	   :children nil
	   :operators nil
	   :parent (cons action-name state-node-name)
	   :local-value new-local-value
	   :forward-value new-forward-value ))
    (state-node-wff-htable (eval new-state-node-name))
    new-state-node-name))

(defun instantiate-op.atual (op.actual uni)
  (if (null uni) (return-from instantiate-op.actual nil))
  (let* ((name (op.actual-name op.actual))
	 (instance (gensym (string name)))
	 (pars (op.actual-pars op.actual))
	 (startconds (op.actual-startconds op.actual))
	 (stopconds (op.actual-stopconds op.actual))
	 (deletes (op.actual-deletes op.actual))
	 (adds (op.actual-adds op.actual))
	 (stdeletes (op.actual-starredDeletes op.actual))
	 (stadds (op.actual-starredAdds op.actual))
	 (ststopconds (op.actual-starredStopConds op.actual))
	 ) 
    (when (not (eq uni t))
      (dolist (u uni)
	(setq pars (subst (cdr u) (car u) pars)))
      (dolist (u uni)
	(setq startconds (subst (cdr u) (car u) startconds)))
      (dolist (u uni)
	(setq stopconds (subst (cdr u) (car u) stopconds)))
      (dolist (u uni)
	(setq ststopconds (subst (cdr u) (car u) ststopconds)))
      (dolist (u uni)
	(setq adds (subst (cdr u) (car u) adds)))
      (dolist (u uni)
	(setq deletes (subst (cdr u) (car u) deletes)))
      (dolist (u uni) 
	(setq stadds (subst (cdr u) (car u) stadds)))
      (dolist (u uni)
	(setq stdeletes (subst (cdr u) (car u) stdeletes)))
      )

    (set instance
	 (make-op.actual :name name
			 :instance instance
			 :pars pars
			 :startconds startconds
			 :stopconds stopconds
			 :deletes deletes
			 :adds adds
			 :starredStopConds ststopconds
			 :starredDeletes stdeletes
			 :starredAdds stadds
			 ))
    instance ))

(defun handleFireAndRain (op-name conds-checked)
  (let* ((op (eval op-name))
	 (startconds (op.actual-startconds op))
	 (adds (op.actual-adds op))
	 (deletes (op.actual-deletes op))
	 (stopconds (op.actual-stopconds op))
	 (bindings 'NIL) instances state-nodes implied-facts record 
	 children
	 event
	 evaledStartConds
	 )
    (format t "~% handleFireAndRain ~a ~a" (op.actual-name (eval op-name)) conds-checked)

    (if (eq 'T conds-checked)
      (setq bindings '(T))
      (progn
	(setq evaledStartConds (mapcar #'(lambda (x) (evalFunctionPredicateExt x)) startconds))

	(when (eq 'NIL
		  (or (eq 'T (eval (cons 'memb (list (quote 'UNKNOWN) (list 'quote evaledStartConds)))))
		      (eq 'T (eval (cons 'memb (list (quote 'NIL) (list 'quote evaledStartConds)))))
		  ))
	(setq bindings '(T))
	)))

  (when (equal bindings '(T)) (format t " on~%")
    (setq instances
	  (mapcar #'(lambda (u) (instantiate-op.actual op u)) bindings))
  (setq state-node (mapcar #'(lambda (i)
			   (generate-ext-op-state-node i *curr-state-node*)) instances))
  (setq children (mapcar #'cons instances state-nodes))
  (setf (state-node-children *curr-state-node*) children)
  (setf (state-node-operators *curr-state-node*) (list op-name))
  (setf (state-node-forward-value *curr-state-node*)
	(inclusive-value (car children)))

  (setq *curr-state-node* (eval (cdar children)))
  (setq adds (mapcar #'simplify-value adds))
  (setq deletes (mapcar #'simplify-value deletes))
  (setq deletes (set-differencef deletes adds))

  (remove_list_of_tuples_from_hashtable deletes *protected-facts* 'NIL)
  (add_list_of_tuples_to_hashtable adds *protected-facts* 'NIL)

  (setq *world-facts* (all-inferences *protected-facts* *general-knowledge* *inference-limit*))
  (add_htable_to_hashtable *protected-facts* *world-facts* 'NIL)

  (setq new-state (copy_construct_hashtable (notice-new-local-facts *curr-state-node*)))

  (setq event (cons (caar children) new-state))

  (setq *event-queue* (append *event-queue* (list (cons event *real-clock*))))

  (push (list event *real-clock*) *real-history*)
  (push (list event *AG-clock*) *AG-history)
  (setq *states* (cons new-state (cdr *states*)))
  )))

(defun handleExtOps ()
  (let ((is-fire 'NIL)
	(is-rain 'NIL)
	(is-fire-handled 'NIL)
	(is-rain-handled 'NIL)
	(is-abn 'NIL)
	(is-terminated 'NIL) op name new-terms
	(new-wff-htable (state-node-wff-htable *curr-state-node*))
	ststopconds stopconds adds deletes stadds stdeletes queue-length)

    (setq queue-length (length *event-queue*))

    (dotimes (i queue-length)
      (setq op (caar (pop *event-queue*)))
      (setq name (op.actual-name (eval op)))
      (format t "~%HEOEventName ~a ~a" name (length *event-queue*))
      (setq adds (op.actual-adds (eval op)))
      (setq deletes (op.actual-deletes (eval op)))
      (setq stadds (op.actual-starredAdds (eval op)))
      (setq stdeletes (op.actual-starredDeletes (eval op)))
      (setq ststopconds (op.actual-starredStopConds (eval op)))
      (setq stopconds (op.actual-stopconds (eval op)))
      (setq is-abn 'NIL)
      (setq is-terminated 'NIL)

      (if (equal name 'fire.actual)
	(progn 
	  (setq is-fire 'T)
	  (setq is-fire-handled 'T)
	  (setq is-rain 'NIL))
	(when (equal name 'rain.actual)
	  (setq is-rain 'T)
	  (setq is-rain-handled 'T)
	  (setq is-fire 'NIL)))

      (if (eq 'T
	      (eval (cons 'memb (list (quote 'T) (list 'quote (mapcar #'(lambda (x) (evalFunctionPredicateExt x)) ststopconds))
				      )))
	      )
	(setq is-abn 'T)
	(when (eq 'T
		  (eval (cons 'memb (list (quote 'T)
					  (list 'quote (mapcar #'(lambda (x) (evalFunctionPredicateExt x)) stopconds))
					  )))
		  )
	  (setq is-terminated 'T)
	  )
	)
      
      (if (or (eq 'T is-terminated) (eq 'T is-abn))
	(progn ;dj
	  starredDeletes
	  (format t "~% HEOExt ~a is terminated. " name)
	  (setq stadds (mapcar #'simplify-value stadds))
	  (setq stdeletes (mapcar #'simplify-value stdeletes))
	  (setq stdeletes (set-differencef stdeletes stadds))

	  (remove_list_of_tuples_from_hashtable stdeletes *protected-facts* 'NIL)
	  (add_list_of_tuples_to_hashtable stadds *protected-facts* 'NIL)

	  (setq *world-facts* (all-inferences *protected-facts* *general-knowledge* *inference-limit*))
	  (add_htable_to_hashtable *protected-facts* *world-facts* 'NIL)
	  
	  (setq new-terms (state-node-terms *curr-state-node*))
	  (setq new-wff-htable (state-node-wff-htable *curr-state-node*))

	  (setq new-terms (remove_term_list_from_term_list
			    (remove_list_of_tuples_from_hashtable stdeletes new-wff-htable 'T)
			    new-terms) )
	  
	  (setq new-terms (merge_term_list_with_term_list
			    (add_list_of_tuples_to_hashtable stadds new-wff-htable 'T)
			    new-terms))
	  (setf (state-node-terms *curr-state-node*) new-terms) 
	  (Setq new-state (copy_construct_hashtable (notice-new-local-facts *curr-state-node*)))
	  (setq *states* (cons new-state (cdr *states*)))
	  )

	(if (eq 'T is-fire) 
	  (handleFireAndRain fire.actual 'T)
	  (when (eq 'T is-rain)
	    (handleFireAndRain rain.actual 'T)
	    ))) 
      )
    
    (when (eq 'NIl is-fire-handled)
      (handleFireAndRain fire.actual 'NIL))

    (when (eq 'NIL is-rain-handled)
      (handledFireAndRain rain.actual 'NIL))))

(defun evalFunctionPredicate (wff)
  (let ((wf wff))
    (when (listp wff)
      (setq wf (mapcar #'simplify-value wff))
      )
    (cond 
      ((and (listp wf) (evaluable-func (car wf)))
       (apply (car wf) (cdr wf))
       )
      (T (check-fact-in-kb wf (state-node-wff-htable *curr-state-node*))
	 ))))

(defun evalFunctionPredicateExt (wff)
  (let ((wf wff)) 
    (when (listp wff)
      (setq wf (mapcar #'simplify-value wff))
      )
    (cond 
      ((and (listp wf) (evaluate-func (car wf)))
       (apply (car wf) (cdr wf))
       )
      (T (check-fact-in-kb wf *world-facts* 'T)
	 ))))

(defun epistemic-fact (wff)
  (cond ((atom wff) (member wff *epistemic-preds*))
	(t (and (member (car wff) *epistemic-preds*)
		(not (null (cdr wff)))
		))))


(defun check-fact-in-kb (wff kb &optional (is-world-kb 'NIL))
  (let ((answer 'NIL))
    (when (eq 'T (or (eq wff 'T) (eq wff 'NIL)))
      (return-from check-fact-in-kb wff))

    (when (atom wff)
      (return-from check-fact-in-kb answer))

    (setq first-in-wff (car wff))
    (cond ((eq first-in-wff 'not)
	   (if (gethash (convert_pred_to_hashkey wff) kb)
	     (setq ansewer 'T)
	     (prog2
	       (setq answer (check-fact-in-kb (second wff) kb is-world-kb))
	       (cond ((eq answer 'T) (setq answer 'NIL) )
		     ((eq answer 'NIL)
		      (setq answer 'T))
		     (t (setq answer 'UNKNOWN))
		     )
	       )
	     )
	   )
	  ((gethash (convert_pred_to_hashkey wff) kb)
	   (setq answer 'T))
	  ((eq first-in-wff 'knows)
	   (setq answer (check-epistemic-fact-in-kb wff kb is-world-kb))
	   )
	  (t 
	    (if is-world-kb
	      (setq answer 'NIL)
	      (prog2
		(setq subj (second wff))
		(if (eq subj 'AG)
		  (setq answer 'NIL)
		  (if (member subj *visited-objects*)
		    (if (member first-in-wff *occluded-preds*) 
		      (setq answer 'UNKNOWN)
		      (setq answer 'NIL) )
		    (if (eq 'NIL subj) 
		      (setq answer 'NIL)
		      (setq answer 'UNKNOWN)
		      )
		    )
		  )
		)
	      )
	    )
	  )
    answer
    )
  )	 


(defun check-epistemic-fact-in-kb (wff kb &optional (is-world-kb 'NIL))
  	(let 	((answer 'NIL)
		 			 (wff-key (convert_pred_to_hashkey wff))
					 			 ;(is_agent_kb (equal kb (state-node-wff-htable *curr-state-node*)))
								 			 ;(is_agent_contemplated_kb (equal kb (state-node-wff-htable *node-now*)))
											 			 (first-in-wff (car wff))
														 			 (subj (second wff))
																	 			 (third-in-wff (third wff))
																				 			)
	  				
	  			(when (eq first-in-wff 'knows)
				  				(cond	((not (null (gethash wff-key kb)))
									 							(setq answer 'T)
																						)
															((atom third-in-wff)
															 							(if (eq subj 'AG)
																						  								(setq answer (member third-in-wff *visited-objects*))
																																						(if is-world-kb
																																						  									(setq answer 'NIL)
																																																								(setq answer 'UNKNOWN) ;is_agent_kb is_agent_contemplated_kb
																																																																)
																																													)
																												)
																					((eq 'whether (car third-in-wff))
																					 							(if (eq subj (second (second third-in-wff)))
																												  								(setq answer 'T)
																																												(if is-world-kb
																																												  									(setq answer 
																																																					      										(and (eq subj 'AG) 
																																																															     											 (not (eq 'UNKNOWN (check-fact-in-kb (second third-in-wff) (state-node-wff-htable *curr-state-node*))))))
																																																														(if (eq subj 'AG)
																																																														  										(setq answer (not (eq 'UNKNOWN 
																																																																										      															  (check-fact-in-kb (second third-in-wff) kb))))
																																																																																		(setq answer 'UNKNOWN)
																																																																																											)
																																																																						)
																																																			)
																																		)
																											((eq 'that (car third-in-wff))
																											 							(if (eq subj (second (second third-in-wff)))
																																		  								(setq answer (eq 'T (check-fact-in-kb (second third-in-wff) kb is-world-kb)))
																																																		
																																																		(if (eq subj 'AG)
																																																		  									(prog2
																																																											  										(setq answer (eq 'T (check-fact-in-kb (second third-in-wff) kb is-world-kb)))
																																																																															(when is-world-kb
																																																																															  											(setq answer (and answer
																																																																																												  															  (eq 'T (check-fact-in-kb (second third-in-wff) (state-node-wff-htable *curr-state-node*)))))
																																																																																																					
																																																																																																				)
																																																																																								)
																																																																				(if is-world-kb
																																																																				  										(setq answer 'NIL) 
																																																																																								(if (eq 'T (check-fact-in-kb (second third-in-wff) kb))
																																																																																								  											(setq answer 'UNKNOWN)
																																																																																																														(setq answer 'NIL)
																																																																																																																								)
																																																																																																	)
																																																																												)
																																																									)
																																								)
																																	(t (if is-world-kb (setq answer 'NIL) (setq answer 'UNKNOWN))
																																	   						)
																																					)				
											)
								
							answer
								)
	); end of check-epistemic-fact-in-kb

	 

(defvar *is-actual* nil)

(defun check-yn-fact-in-kb (is_actual wf kb &optional (is-world-kb 'NIL))
  (let* (
	 (*is-actual* is_actual)
	 (ans (check-fact-in-kb wf kb is-world-kb))
	 )
    
    (setq *is-actual* 'NIL)
    (cond ((eq ans 'T) 
	   (setq ans wf)
	   )
	  ((eq ans 'NIL)
	   (setq ans (list 'not wf))
	   )
	  (t (setq ans 'UNKNOWN))
	  )

    (when (eq is_actual 't)
      (if (eq ans 'UNKNOWN)
	(prog2 (verbalize ans wf)
	       (format t "~%~% For the question ~a, AG does not currently know the answer as it may be about an occluded property of a local object or about a non-local object. ~%" wf)
	       )
	(prog2 (verbalize ans)
	       (when (not is-world kb)
		 (format t "~% For the question ~a, according to AG's current knowledge base, AG offers the answer above. ~%" wf)
		 )
	       )
	)
      )
    ans))

(defun check-whq-answer-in-kb (is_actual wf kb)
  (let ((unifiers '()) (result-wffs '()) (is_negated 'NIL) (wff wf)
		       (is_agent_kb (equal kb (state-node-wff-htable *curr-state-node*)))
		       )
    (when (eq (car wff) 'not)
      (setq wff (second wf))
      (setq is_negated 'T)
      )

    (setq unifiers (all-bindings-of-posgoal-to-fact-htable wff kb))
    (setq unifiers (remove-duplicates unifiers :test #'equal))
    (if (null unifiers)
      (when (eq is_actual 'T)
	(if is_agent kb
	  (prog2
	    (verbalize 'UNKNOWN wff 'T)
	    (if (eq is_negated 'NIL)
	      (format t "~%~% For the question ~a, there are no positive instances that AG knows of, so AG assumes nothing as the answer. ~%" wf)
	      (format t "~%~% For the question ~a, there are no positive instances that AG knows of, so AG assumes everything as the answer. ~%" wf)
	      )
	    )
	  (if (eq is_negated 'NIL)
	    (format t "~%~% For the question ~a, there are no positive instances, so nothing is the answer. ~%" wf)
	    (format t "~%~% For the question ~a, there are no positive instances, so everything is the answer. ~%" wf)
	    )
	  )
	)
      (progn 
	(setq result-wffs (MAPCAR #'(LAMBDA (ELEMENT) (SUBST-UNIFIER ELEMENT wff)) unifiers))
	(when (eq is_actual 'T)
	  (MAPCAR #'(LAMBDA (ELEMENT) (VERBALIZE ELEMENT)) result-wffs)
	  (if is_agent-kb
	    (if (eq is_negated 'NIL)
	      (format t "~% For the question ~a, other than the above positive instances(s) that AG knows of, AG assumes nothing else as the answer.~%" wf) 
	      (format t "~% For the question ~a, other than the above positive instance(s) that AG knows of, AG assumes everything else as the answer.~%" wf)
	      )
	    (if (eq is_negated 'NIL) 
	      (format t "~% For the question ~a, other than the above positive instance(s), nothing else is the answer.~%" wf)
	      (format t "~% For the question ~a, other than the above positive instance(s), everything else if the answer. ~%" wf)
	      )
	    )
	  )
	)
      )
    result-wffs
    )
  )

;;;; Question Answering Code ::::::
(defun parseIntoPred (x)
  (cond ((or (not (listp x)) (null x)) x)
	((eq 'not (first x)) (list 'not (parseIntoPred (second x))))
	(t (cons (second x) (cons (first x) (nthcdr 2 x))))
	)
  )

(defun listen! ()
  (let ((user-input 'NIL) (lst 'NIL) (implied-facts 'NIL)
			   (tell-lst 'NIL) (neglst 'NIL) curr-tell curr-ans
			   (new-terms (state-node-terms *curr-state-node*))
			   user-input-intention
			   (new-wff-htable (state-node-wff-htable *curr-state-node*))
			   )
    (format t "You're welcome to ask AG a question or tell it a fact.~%")
    (setq user-input (read))
    (setq user-input (mapcar #'(lambda(y) (list (first y) (parseIntoPred (second y)))) user-input))
    (when (and (listp user-input) (not (null user-input)))
      (dolist (i user-input)
	(cond 
	  ((eq 'ask-yn (car i))
	   (setq user-input-intention (list 'wants 'USER (list 'that (list 'tells 'AG 'USER (list 'whether (second i))))))
	   (push user-input-intention lst)
	   (push (list 'not user-input-intention) neglst)
	   )
	  ((eq 'ask-wh (car i))
	   (setq user-input-intention (list 'wants 'USER (list 'that (list 'tells 'AG 'USER (list 'answer_to_whq (second i))))))
	   (push user-input-intention lst)
	   (push (list 'not user-input-intention) neglst)
	   )
	  ((eq 'tell (car i))
	   (push (second i) tell-lst)
	   )
	  )
	)
      (setq tell-lst (nreverse tell-lst))

      (while tell-lst
	     (setq curr-tell (pop tell-lst))
	     (setq curr-ans (check-yn-fact-in-kb 'NIL curr-tell *world-facts* 'T))
	     (if (equal curr-ans curr-tell)
	       (prog2
		 (push (list 'tells 'USER (list 'that curr-tell)) lst)
		 (if (eq (first curr-tell) 'not)
		   (setq neglst (unionf neglst (second curr-tell)))
		   (setq neglst (unionf neglst (list (list 'not curr-tell))))
		   )
		 )
	       (cond ((eq curr-ans 'UNKNOWN)
		      (format t "~%Your assertion ~a has an unknown truth value in the simulated world so it is not added under the closed world assumption.~%" curr-tell)
		      )
		      (t ;(eq curr-ans 'NIL)
			(format t "~%The negation of your assertion ~a is true in the simulated world so your assertion is not added to avoid introducing inconsistency.~%" curr-tell)
			)
		      )
	       ;(format t "Are you sure you want to add it (enter y or n)?~%" curr-tell)
	       )
	     )
      (setq lst (nreverse lst))
      (remove_list_of_tuples_from_hashtable neglst *protected-facts* 'NIL)
      (add_list_of_tuples_to_hashtable lst *protected-facts* 'NIL)
      (setq *world-facts*  (all-inferences *protected-facts* *general-knowledge* *inference-limit*))

      (add_htable_to_hashtable *protected-facts* *world-facts* 'NIL)
      (setq new-terms (remove_term_list_from_term_list
			(remove_list_of_tuples_from_hashtable neglst new-wff-htable 'T)
			new-terms)
	    )
      (setq new-terms (merge_term_list_with_term_list
			(add_list_of_tuples_to_hashtable lst new-wff-htable 'T)
			new-terms)
	    )
      (setf (state-node-terms *curr-state-node*) new-terms)
      (setq new-state (copy_construct_hashtable (notice-new-local-facts *curr-state-node*)))
      (setq *states* (cons new-state (cdr *states*)))
      )
    T
    )
  )



(defun peer-into-state (ques)
  (cond ((eq (car ques) 'YNQ) 
	 (check-yn-fact-in-kb 'T (second ques) (state-node-wff-htable *curr-state-node*))
	 )
	((eq (car ques) 'WHQ)
	 (check-whq-answer-in-kb 'T (second ques) (state-node-wff-htable *curr-state-node*))
	 )
	)
 )

(defun the_pt+units_from+towards+on_road? (distance start destination path)
  	(let*	((simplified-dist (simplify-value distance))
	 (dist-str (write-to-string simplified-dist))
	 (start-str (string start))							
	 (dest-str (string destination))							
	 (path-str (string path))
	 (result 'NIL))
	(cond	((= 0 simplified-dist)
		(setq result start))
			((= simplified-dist (distance_from+to+on? start destination path))
			 (setq result destination))
													
			(t 									
			  (setq result (INTERN (string-upcase 
						 (concatenate 'string "the_pt_" dist-str "_units_from_" start-str "_towards_" dest-str "_on_road_" path-str)))))
			)
			result))

(defun verbalize (wff &optional (input-wff 'NIL) (print-var 'NIL))
     ;^ extra '@optional' edited out 4/15/20
     ;(format t "input-wff verbalize is ~a ~%" input-wff)
     	(if (and (eq wff 'UNKNOWN) (not (null input-wff)))
	  		(format t "~%~%~A~%" (concatenate 'string "AG DOES NOT KNOW WHETHER " (simplifyString input-wff print-var)))
			(format t "~%~%~A~%" (simplifyString wff))
	)
); end of verbalize

(defun replaceVarWithAnything (wff any-symb)
  	(cond ((atom wff) (if (var wff) any-symb wff))
	      		  (t (cons (replaceVarWithAnything (first wff) any-symb) (replaceVarWithAnything (cdr wff) any-symb)))
	)
)

(defun simplifyString (wff &optional (print-var 'NIL))
  	(let* (answer result-lst-strs
		      (result-str "") posn)
	 ;(format t "wff simplify-string is ~a ~a ~%" wff print-var)		
	  	(if (eq 'T print-var)
		  (setq answer (verbalize-wff 'NIL (replaceVarWithAnything wff 'ANYTHING-non-AG) 'T)) 
		  (setq answer (verbalize-wff 'NIL wff 'T)) 
		)
	;(format t "answer simplify-string is ~a~%" answer)
	(setq result-lst-strs (mapcar #'(lambda(x) (write-to-string x)) answer))		
	(dolist (i result-lst-strs)
	  (setq result-str (concatenate 'string (concatenate 'string result-str i) " "))
	 )
	  (setq result-str (concatenate 'string (string-trim " " result-str) "."))
	  (setq posn (search "IT IS NOT THE CASE THAT IT IS NOT THE CASE THAT " result-str))
	  (while (numberp posn)										 
		 (setq result-str (subseq result-str (+ posn 48)))
		 (setq posn (search "IT IS NOT THE CASE THAT IT IS NOT THE CASE THAT " result-str))
	)
	  ;(format t "~%~%~A~%" result-str)
	result-str											
	)
)

(defun verbalize-wff (result wff right-after-that-whether)	
  	(cond	((null wff)
		 result
		)
		((not (listp wff))
		 (append result  (SPLIT-STRING-TO-SYMBOLS (string wff)))
		)
		((eq (car wff) 'not) 
		 (verbalize-wff (append result (list 'it 'is 'not 'the 'case 'that)) (cadr wff) (listp (cadr wff)))										
		 )
		 ((OR (eq (car wff) 'that) (eq (car wff) 'whether))
			(verbalize-wff (append result (list (car wff))) (cadr wff) (listp (cadr wff)))
			)								
		 ((listp (car wff))
		  (verbalize-wff (verbalize-wff result (car wff) right-after-that-whether) (cdr wff) (listp (cadr wff)))
		)
		((numberp (car wff))
			(append result (list (car wff)))
		)
		((not (search "+" (string (car wff))))
			(if (>= (length wff) 2)
			  (if right-after-that-whether
			    (verbalize-wff 
			      (verbalize-wff (verbalize-wff result (second wff) 'NIL) (first wff) 'NIL)
				(nthcdr 2 wff)
				'NIL
				);It's better to test whether (second wff) is a pred; and only if so do we reverse second and first.
			    (verbalize-wff 
			      (verbalize-wff (verbalize-wff result (first wff) 'NIL) (second wff) 'NIL)
				(nthcdr 2 wff)
				'NIL
				)
			    )
			  (append result (SPLIT-STRING-TO-SYMBOLS (string (first wff)))
				  )
			  )
			)
		( t ;(> (search "+" (string (car wff))) 0)
		  (if (null result) ; topmost parse
		    (append result 
			(append (SPLIT-STRING-TO-SYMBOLS (string (second wff)))
				(SPLIT-STRING-TO-SYMBOLS-INSERT-ARGS-AT-PLUS (STRING (car wff)) (nthcdr 2 wff))
			)
			)
		    (append result 
			(SPLIT-STRING-TO-SYMBOLS-INSERT-ARGS-AT-PLUS (STRING (car wff)) (rest wff))
			)
		)))
); end of verbalize-wff

(DEFUN SPLIT-STRING-TO-SYMBOLS-INSERT-ARGS-AT-PLUS (STRING ARG-LIST &optional (SEPARATORS "-_+? "))
       (UNLESS (SIMPLE-STRING-P STRING)     (SETQ STRING     (COPY-SEQ STRING)))
       (UNLESS (SIMPLE-STRING-P SEPARATORS) (SETQ SEPARATORS (COPY-SEQ SEPARATORS)))
       (LET ( (CHUNKS  '()) (POSITION 0) (NEXTPOS  0) (STRLEN (LENGTH STRING)) )
	    (DECLARE (TYPE SIMPLE-STRING STRING SEPARATORS))
	    (LOOP WHILE (< POSITION STRLEN)
		  DO
		  (LOOP WHILE (AND (< NEXTPOS STRLEN) (NOT (POSITION (CHAR STRING NEXTPOS) SEPARATORS)))
			DO
			(SETQ NEXTPOS (1+ NEXTPOS))
			)
		  (when (> NEXTPOS POSITION)
		    (PUSH (INTERN (string-upcase (SUBSEQ STRING POSITION NEXTPOS) )) CHUNKS)
		    )
		  (when (AND (< NEXTPOS STRLEN) (eq (CHAR STRING NEXTPOS) '#\+))
		    (MAPCAR #'(LAMBDA (ELEMENT) (PUSH ELEMENT CHUNKS)) (SPLIT-STRING-TO-SYMBOLS (STRING (pop ARG-LIST))))
		    )
		  (SETQ POSITION (1+ NEXTPOS))
		  (SETQ NEXTPOS  POSITION)
		  )
	    (when (not (null ARG-LIST))
	      (MAPCAR #'(LAMBDA (ELEMENT) (PUSH ELEMENT CHUNKS)) (SPLIT-STRING-TO-SYMBOLS (STRING (pop ARG-LIST))))
	      )
	    (NREVERSE CHUNKS)
	    )
 )

(DEFUN SPLIT-STRING-TO-SYMBOLS (STRING &optional (SEPARATORS "-_+? "))
       (UNLESS (SIMPLE-STRING-P STRING)     (SETQ STRING     (COPY-SEQ STRING)))
       (UNLESS (SIMPLE-STRING-P SEPARATORS) (SETQ SEPARATORS (COPY-SEQ SEPARATORS)))
       (LET ( (CHUNKS  '()) (POSITION 0) (NEXTPOS  0) (STRLEN (LENGTH STRING)) )
	    (DECLARE (TYPE SIMPLE-STRING STRING SEPARATORS))
	    (LOOP WHILE (< POSITION STRLEN)
		  DO
		  (LOOP WHILE (AND (< NEXTPOS STRLEN) (NOT (POSITION (CHAR STRING NEXTPOS) SEPARATORS))) 
			DO (SETQ NEXTPOS (1+ NEXTPOS))
			)
		  (when (> NEXTPOS POSITION)
		    (PUSH (INTERN (string-upcase (SUBSEQ STRING POSITION NEXTPOS) )) CHUNKS)
		    )
		  (SETQ POSITION (1+ NEXTPOS))
		  (SETQ NEXTPOS  POSITION)
		  )
	    (NREVERSE CHUNKS)
	    )
       )



