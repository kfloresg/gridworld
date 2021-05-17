(defun implement-effects (action-name) 
  (let* ((the-action (action-type action-name))
	 (action (eval action-name))
	 (expected-duration (op-time-required action))
	 (name (op-name action))
	 (name.actual-str (concatenate 'string (string name) ".ACTUAL"))

	 (name.actual
	   (if (find-symbol name.actual-str)
	     (find-symbol name.actual-str)
	     (name-of-actual-operator name.actual-str (eval name)))
	   )
	 (op.actual (eval name.actual))
	 (pars (op-pars op.actual))
	 (par-values (op-pars action))
	 (is-first-iter 'T)
	 (is-terminated 'NIL)
	 (par 'NIL)
	 (par-value 'NIL)
	 (stopconds.actual (op.actual-stopconds op.actual))
	 (adds.actual (op.actual-adds op.actual))
	 (deletes.actual (op.actual-deletes op.actual))
	 tempdeletes adds deletes stopconds implied-facts bindings
	 new-state deletes-copy new-wff-htable new-terms)

    (while pars 
	   (setq par (pop pars))
	   (setq adds.actual (subst par-value par adds.actual))
	   (setq deletes.actual (subst par-value par deletes.actual))
	   (setq stopconds.actual (subst par-value par stopconds.actual)))

    (setq *total-value*
	  (incf *total-value* (+ (op-value action)
				 (state-node-local-value *curr-state-node*))))
    (setq *event-timer* 0)
    (while (or (eq 'T is-first-iter) (eq is-terminated 'NIL))
	   (incf *event-timer* 1)
	   (if (eq 'T is-first-iter)
	     (setq is-first-iter 'NIL)
	     (progn 
	       (setq stopconds (mapcar #'simplify-value stopconds.actual))
	       (if (evaluable-func (car stopconds))
		 (setq stopconds (simplify-value stopconds)))
	       (if (eq 'T
		       (eval (cons 'memb
				   (list (quote 'T)
					 (list 'quote
					       (mapcar 
						 #'(lambda (x)
						     (evalFunctionPredicate x))
						 stopconds))))))
		 (setq is-terminated 'T))
	       ))
	   
	   (when (eq 'NIL is-terminated)
	     (setq adds (mapcar #'simplify-value adds.actual))
	     (if (evaluable-func (car adds))
	       (setq adds (simplify-value adds))
	       )

	     (setq deletes (mapcar #'simplify-value deletes.actual))
	     (if (evaluable-func (car deletes))
	       (setq deletes (simplify-value deletes)))
	     (setq deletes (set-differencef deletes adds))

	     (setq bindings (remove-if #'degenerate-binding
				       (all-bindings-of-goals-to-fact-htable deletes
									     (state-node-wff-htable *curr-state-node*))))
	     (setq bindings (remove-duplicates bindings :test #'equal))
	     
	     (when (and (not (equal '(T) bindings)) (not (null bindings)))
	       (setq tempdeletes 'NIL)
	       (dolist (u bindings)
		 (setq deletes-copy deletes)
		 (dolist (b u)
		   (setq deletes-copy
			 (subst (cdr b) (car b) deletes-copy)))
		 (setq tempdeletes (unionof deletes-copy tempdeletes))
		 )
	       (setq tempdeletes (remove-duplicates tempdeletes :test #'equal))
	       (setq tempdeletes (mapcar #'simplify-valu tempdeletes))
	       (setq deletes (set-differencef tempdeletes adds)))

	     (remove_list_of_tuples_from_hashtable deletes *protected-facts* 'NIl)
	     (add_list_of_tuples_to_hashtable adds *protected-facts* 'NIL)
	     (setq *world-facts* (all-inferences *protected-facts*
						 *general-knowledge* *inference-limit* ))
	     (add_htable_to_hashtable *protected-facts* *world-facts* 'NIL)

	     (setq new-terms (state-node-terms *curr-state-node*))
	     (setq new-wff-htable (state-node-wff-htable *curr-state-node*))
	     (setq newterms
		   (remove_term_list_from_term-list
		     (remove_list_of_tuples_from_hashtable deletes new-wff-htable 'T)
		     new-terms))
	     (setq new-terms
		   (merge_term_list_with_term_list
		     (add_list_of_tuples_to_hashtable adds new-wff-htable 'T)
		     new-terms))
	     (setf (state-node-terms *curr-state-node*) new-terms)

	     (setq new-state (copy_construct_hashtable
			       (notice-new-local-facts *curr-state-node*)))
	     (setq *states* (cons new-state (cdr *states*)))

	     (push (list (cons the-action new-state) *event-timer*
			 expected-duration *real-clock*) *real-history*)

	     (if (= 1 *event-timer*)
	       (push (list (cons the-action new-state)
			   *event-timer* expected-duration *AG-clock*)
		     *AG-history*))
	     )
	   (incf *real-clock* 1)
	   (incf *AG-clock* 1)
	   )
    (when (> *event-timer* 2) 
      (push (list (cons the-action new-state) (- *event-timer* 1)
		  expected-duration (- *AG-clock* 2)) *AG-history*))))
