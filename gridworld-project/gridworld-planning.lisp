(defvar *plan* nil)
(defvar *states* nil)
(defvar *inference-limit* 2)
(defvar *real-history* nil)
(defvar *AG-history* nil)
(defvar *operators* nil)
(defvar *search-beam* nil)

(defun put (atm indic val) (setf (get atm indic) val))
(defun unionof (x y) (union x y :test #'equal))
(defun memberf (x y) (member x y :test #'equal))
(defun intersectionf (x y) (intersection x y :test #'equal))
(defun set-differencef (x y) (set-difference x y :test #'equal))

(defun removef (lst1 lst2)
  (let ((result lst2))
    (dolist (x lst1)
      (setq result (remove x result :count 1 :test #'equal)))
    result))

(defun var (x) 
  (if (and x (symbolp x))
    (char= (nth 0 (coerce (string x) 'list)) #\?) 
    nil))

(defun *append (u v)
  (if (equal u T) v (if (equal v T) u (append u v))))

(defun first-n (x n)
  (if (atom x) x (butlast x (max 0 (- (length x) n)))))

(defun all-bindings-of-goals-to-fact-htable (goals fact-htable terms)
  (let ((gg goals) (ff fact-htable)
		   (wff-terms (remove-duplicates terms :test #'equal)))
    (setq gg (sort (copy-list gg) #'> :key #'rank-for-goal-sorting))
    (all-bindings-of-goals-to-fact-htable1 gg ff wff-terms)))

(defun rank-for-goal-sorting (goal)
  (let ((rank (if (poslit goal) 200 0))
	(var-count (length (remove-duplicates (vars goal))))
	(term-count+1
	  (if (poslit goal) (length goal) (length (second goal)))))
    (decf rank (* 10 var-count))
    (incf rank term-count+1)
    (when (contains-evaluable-expr goal)
      (decf rank 400))
    rank))

(defun contains-evaluable-expr (expr)
  (cond ((atom expr) nil)
	((evaluable-func (car expr)) t)
	((atom (car expr))
	 (if (member t (mapcar #'contains-evaluable-expr (cdr expr)))
	   t nil))
	(t (if (member t (mapcar #'contains-evaluable-expr expr))
	     t nil))))

(defun all-bindings-of-goals-to-fact-htable1 (goals fact-htable terms)
  (prog ((gg goals) g results uu vv)
	(setq g (pop gg))
	(setq uu (all-bindings-of-goal-to-fact-htable g fact-htable terms))
	(when (null gg) (return uu))
	(when (equal uu '(t))
	  (return (all-bindings-of-goals-to-fact-htable1 gg fact-htable terms)))
	(dolist (u (reverse uu))
	  (setq vv (all-bindings-of-goals-to-fact-htable1
		     (subst-unifier-in-wffs u gg) fact-htable terms))
	  (when vv
	    (setq vv (mapcar #'(lambda (v) (*append u v)) vv))
	    (setq results (append vv results))))
	(return results)))

(defun all-bindings-of-goal-to-fact-htable (g ff terms)
  (if (poslit g) 
    (all-bindings-of-posgoal-to-fact-htable g ff)
    (all-bindings-of-neggoal-to-fact-htable g ff terms)))

(defun all-bindings-of-posgoal-to-fact-htable (g ff)
  (prog ((g1 g))
	(when (contains-evaluable-expr g1)
	  (setq g1 (simplify-value g1))
	  (if (eq g1 t)
	    (return '(t))
	    (when (or (eq g1 nil)
		      (contains-evaluable-expr g1))
	      (return nil))))
	  (return (remove-if #'null
			     (mapcar #'(lambda (f) (unifier g f))
				     (possible-positive-unifiers g ff))))))

(defun possible-positive-unifiers (g ff) 
  (let* ((shortest-leng 0) hash-value hash-leng
			   shortest-hash-value (shortest-index -1)
			   (keys (generate_allkeys_from_hashkey (convert_pred_to_hashkey g)))
			   (keys-leng (length keys))
			   (first-non-null-hash-value-reached 'NIL)
			   )
    (dotimes (i keys-leng)
      (setq hash-value (gethash (nth i keys) ff))
      (when (not (null hash-value))
	(setq hash-leng (car hash-value))
	      (when (and (> hash-leng 0)
			 (or (> shortest-leng hash-leng) (null first-non-null-hash-value-reached)))
		(setq shortest-leng hash-leng)
		(setq shortest-index i)
		(setq shortest-hash-value (cdr hash-value))
		(setq first-non-null-hash-value-reached 'T))))
      shortest-hash-value))

(defun all-bindings-of-neggoal-to-fact-htable (g ff terms)
  (complement-unifiers
    (all-bindings-of-posgoal-to-fact-htable (second g) ff) (vars g) terms))

(defun alphabetically-order (uu) 
  (mapcar #'(lambda (u)
	      (if (eq u t) t
		(sort (copy-list u) #'string<
		      :key #'(lambda (x) (string (car x))) )))
	  uu))

(defun complement-unifiers (uu vars terms)
  (when (null vars) 
    (return-from complement-unifiers (if (null uu) '(t) nil)))
  (when (null terms)
    (return-from complement-unifiers nil))
  (let (ordered-vars ordered-uu vv)
    (setq ordered-vars
	  (sort (copy-list vars) #'string<
		:key #'(lambda (x) (string x))))
  (setq ordered-uu (alphabetically-order uu))
  (setq vv (all-bindings ordered-vars terms))
  (reverse (set-differencef vv ordered-uu))))

(defun all-bindings (vars terms) 
  (let (vv ww)
    (cond ((and vars terms)
	   (setq vv (mapcar #'(lambda (x) (cons (car vars) x)) terms))
	  (setq ww (all-bindings (cdr vars) terms))
	  (combine-sets-of-unifiers (mapcar #'list vv) ww))
    (t nil))))

(defun combine-sets-of-unifiers (uu vv)
  (when (null uu) (return-from combine-sets-of-unifiers vv))
  (when (null vv) (return-from combine-sets-of-unifiers uu))
  (let (result)
    (dolist (u (reverse uu))
      (setq result
	    (append (mapcar #'(lambda (v) (*append u v)) vv) result)))
    result))

(defun poslits (lits)
  (remove-if-not #'poslit lits))

(defun neglits (lits)
  (mapcar #'second 
	  (remove-if-not #'neglit lits)))

(defun poslit (lit) (not (neglit lit)))

(defun neglit (lit) (and (listp lit) (eq (car lit) 'not)))

(defun collect-terms (lits) 
  (remove-duplicates
    (apply #'append (mapcar #'args lits)) :test #'equal))

(defun collect-terms-duplicate (lits) 
  (apply #'append (mapcar #'args lits)))

(defun vars (lit)
  (if (atom lit) nil (remove-if-not #'var (args lit))))

(defun collect-vars (lits)
  (remove-duplicates (apply #'append (mapcar #'vars lits))))

(defun args (lit)
  (cond ((atom lit) nil)
	((eq (car lit) 'not) (cdr (second lit)))
	(t (cdr lit))))

(defun find-all-positive-bindings (poslits db)
  (prog (results phi u remlits vv)
	(if poslits
	  (setq phi (car poslits))
	  (return '(T)))
	(dolist (phi1 (if (equal (car phi) 'EQ) (equalities db) db))
	  (setq u (unifier phi phi1))
	  (when u 
	    (setq remlits
		  (mapcar #'(lambda (x) (subst-unifier u x))
			  (cdr poslits)))
	    (setq vv (find-all-positive-bindings remlits db))
	    (when vv
	      (setq results
		    (unionf (mapcar #'(lambda (v) (*append u v)) vv)
			    results)))))
	(return results)))

(defun equalities (db)
  (let ((constants (remove-duplicates (reduce #'append (mapcar #'cdr db)))))
    (mapcar #'(lambda (x) (list 'EQ x x)) constants)))

(defun unifier (lit1 lit2)
  (if (not (equal (car lit1) (car lit2)))
    nil (if (equal (cdr lit1) (cdr lit2))
	  T
	  (if (equal (car lit1) 'not) 
	    (unifier (second lit1) (second lit2))
	    (if (not (equal (length lit1) (length lit2)))
	      nil
	      ((lambda (x) (if (null x) T
			     (if (member nil x)
			       nil 
			       x)))
	       (arglist-unifier (cdr lit1) (cdr lit2))))))))

(defun subst-unifier (uni wff)
  (prog ((wff-out wff))
	(when (equal uni t) (return wff))
	(dolist (pair uni)
	  (setq wff-out (subst (cdr pair) (car pair) wff-out)))
	(return wff-out)))

(defun subst-unifier-in-wffs (uni wffs) 
  (mapcar #'(lambda (wff) (subst-unifier uni wff)) wffs))

(defun arglist-unifier (list1 list2) 
  (if (null list1)
    nil
    (if (equal (car list1) (car list2))
      (arglist-unifier (cdr list1) (cdr list2))
      (if (var (car list1))
	(cons (cons (car list1) (car list2))
	      (arglist-unifier 
		(subst (car list2) (car list1) (cdr list1))
		(subst (car list2) (car list1) (cdr list2))))
	(if (and (listp (car list1)) (listp (car list2))
		 (= (length (car list1)) (length (car list2))))
	  (let ((uni (arglist-unifier (car list1) (car list2))))
	    (append uni
		    (arglist-unifier 
		      (subst-unifier uni (cdr list1))
		      (cdr list2))))
	  '(nil))))))
(defstruct op 
  name 
  instance
  pars
  preconds
  effects
  time-required
  value)

(defun instantiate-op (op uni)
  (when (null uni) (return-from instantiate-op nil))
  (let* ((name (op-name op))
	 (instance (gensym (string name)))
	 (pars (op-pars op))
	 (preconds (op-preconds op))
	 (effects (op-effects op))
	 (time-required (op-time-required op))
	 (value (op-value op)))
    (when (not (eq uni t))
      (dolist (u uni) 
	(setq pars (subst (cdr u) (car u) pars)))
      (dolist (u uni) 
	(setq effects (subst (cdr u) (car u) effects)))
      (setq effects (mapcar #'simplify-value effects))
      (when (evaluable-func (car effects))
	(setq effects (simplify-value effects)))
      (dolist (u uni)
	(setq time-required (subst (cdr u) (car u) time-required)))
      (setq time-required (simplify-value time-required))
      (dolist (u uni) 
	(setq value (subst (cdr u) (car u) value)))
      (setq value (simplify-value value)))

    (set instance 
	 (make-op :name name
		  :instance instance
		  :pars pars
		  :preconds preconds
		  :effects effects
		  :time-required time-required
		  :value value))
    instance))

(defun simplify-value (expr) 
  (cond ((atom expr) expr)
	((and (not (contains-var expr))
	      (evaluable-func (car expr)))
	 (apply (car expr) (mapcar #'simplify-value (cdr expr))))
	((or (eq (car expr) 'answer_to_whq.actual?)
	     (eq (car expr) 'answer_to_whq?))
	 (apply (car expr) (mapcar #'simplify-value (cdr expr))))
	(t (cons (car expr) (mapcar #'simplify-value (cdr expr))))))

(defun evaluable-func (f)
  (and (symbolp f) (or (member f '(+ - * / < <= = >= >))
		       (eq f 'random)
		       (char= (car (last (coerce (string f) 'list))) #\?))))

(defun contains-var (expr)
  (cond ((var expr) t)
	((atom expr) nil)
	((find-if #'contains-var expr) t)
	(t nil)))

(defstruct state-mode
  terms
  name 
  wff-table
  children 
  operators
  parent 
  local-value
  forward-value)

(defun chain-forward (state-node search-beams) 
  (if (null search-beams) (return-from chain-forward nil))
  (let* ((state-node-name (state-node-name state-node))
	 (wff-htable (state-node-wff-htable state-node))
	 (children (state-node-children state-mode))
	 (operators (state-node-operators state-node))
	 (beam (car search-beams))
	 (nbest (car beam))
	 (ops (cdr beam))
	 (extra-ops (set-difference ops operators))
	 action-state-pairs random-best (max-value 0) (index 1))
    (setq *node-now* state-node)
    (when extra-ops
      (setf (state-node-operators state-node)
	    (append extra-ops operators))
      (setq action-state-pairs
	    (apply #'append
		   (mapcar #'(lambda (o) 
			       (all-instances-of-operator o state-node-name))
			   extra-ops)))
      (setq action-state-pairs 
	    (sort action-state-pairs #'> :key #'inclusive-value))
      (setq children 
	    (merge 'list action-state-pairs children #'> 
		   :key #'inclusive-value)))
    (setq action-state-pairs (first-n children nbest))
    (dolist (pair action-state-pairs)
      (chain-forward (eval (cdr pair)) (cdr search-beams)))
    (setq action-state-pairs
	  (sort action-state-pairs #'> :key #'inclusive-value))
    (setq children 
	  (merge 'list action-state-pairs (nthcdr nbest children)
		 #'> :key #'inclusive-value))
    (when children 
      (setq max-value (inclusive-value (car children)))
      (while (and (< index (length children)) (= max-value (inclusive-value (nth index children))))
	     (setq index (incf index 1)))
      (when (> index 1)
	(setq random-best (nth (random index) children))
	(setq children (delete random-best children :test #'equal))
	(setq children (push random-best children))))
    (setf (state-node-children state-node) children)
    (when children
      (setf (state-node-forward-value state-node)
	    (inclusive-value (car children)))
      (setq *plan* (leftmost-action-sequence (car children)))
      (setq *states* (leftmost-state-sequence (car children))))
    (show-actions-and-forward-values children)))

(defun leftmost-action-sequence (action-state-pair)
  (prog ((pair action-state-pair) action-name state-node-name plan children)
	(if (null pair) (return nil))
	next (setq action-name (car pair) state-node-name (cdr pair))
	(push (action-type action-name) plan)
	(setq children (state-node-children (eval state-node-name)))
	(if (null children) (return (reverse plan)))
	(setq pair (car children))
	(go next)))

(defun leftmost-state-sequence (action-state-pair)
  (prog ((pair action-state-pair)
	 (parent (state-node-parent (eval (cdr action-state-pair))))
	 action-name state-node-name states children)
	(if (null pair) (return nil))
	(if parent 
	  (setq states
		(list (state-node-wff-htable (eval (cdr parent))))))
	next (setq action-name (car pair) state-node-name (cdr pair))
	(push (state-node-wff-htable (eval state-node-name)) states)
	(setq children (state-node-children (eval state-node-name)))
	(if (null children) (return (reverse states)))
	(setq pair (car children))
	(go next)))

(defun action-type (action-name)
  (cons (op-name (eval action-name))
	(op-pars (eval action-name))))

(defun show-actions-and-forward-values (action-state-pairs) 
  (mapcar #'(lambda (pair) 
	  (cons (action-type (car pair))
		(inclusive-value pair)))
  action-state-pairs))

(defun inclusive-value (action-state-pair)
  (let ((num1 'NIL) nnum2 num3)
    (setq num1 (op-value (eval (car action-state-pair))))
    (when (not (numberp num1))
      (setq num1 0)) 
    (setq num2 (state-node-local-value (eval (cdr action-state-pair))))
    (setq num3 (state-node-forward-value (eval (cdr action-state-pair))))
    (state-node-name (eval (car action-state-pair)))
    (+ num1 num2 num3)))

(defun all-instance-of-operator (op-name state-node-name) 
  (let* ((op (eval op-name))
	 (state-node (eval state-node-name))
	 (preconds (op-preconds op))
	 (wff-terms (state-node-terms state-node))
	 (wff-htable (state-node-wff-htable state-node))
	 bindings
	 instances
	 state-nodes)
    (setq bindings (all-bindings-of-goals-to-fact-htable preconds wff-htable wff-terms))
    (setq bindings (remove-duplicates (remove-if #'degenerate-binding bindings) :test #'equal))
    (setq instance (mapcar #'(lambda (u) (instantiate-op op u)) bindings))
    (setq state-nodes (mapcar #'(lambda (i) (generate-state-node i state-node-name))
	  instances))
  (mapcar #'cons instances state-node)))

(defun degenerate-bindings (u)
  (if (atom u) nil
    (> (length u)
       (length (remove-duplicates (mapcar #'cdr u) :test #'equal)))))

(defun generate-state-node (action-name state-node-name) 
  (let* ((action (eval action-name))
	 (effects (op-effects action))
	 (deletions (neglits effects))
	 (additions (poslits effects))
	 (state-node (eval state-node-name))
	 (new-terms (state-node-terms state-node))
	 (old-wff-htable (state-node-wff-htable state-node))
	 (local-value (state-node-local-value state-node))
	 (new-state-node-name (gensym "STATE-nODE"))
	 new-local-value
	 new-forward-value
	 (new-wff-htable (copy_construct_hashtable old-wff-htable)))
    (setq deletions (set-differencef deletions additions))
    (setq new-local-value
	  (state-value additions deletions local-value))
    (setq new-forward-value 
	  (expected-rewards old-wff-htable))
    (setq new-terms (removef (remove_list_of_tuples_from_hashtable deletions new-wff-htable 'T)
			     new-terms))
    (setq new-terms (append (add_list_of_tuples_to_hashtable additions new-wff-htable 'T)
			    new-terms))
    (set new-state-node-name 
	 (make-state-node 
	   :terms new-terms
	   :name new-state-node-name
	   :wff-htable new-wff-htable
	   :children nil
	   :operators nil
	   :parent (cons action-name state-node-name)
	   :local-value new-local-value
	   :forward-value new-forward-value))
    new-state-node-name))

(defun name-of-actual-operator (name.actual-str state-node) 
  (let ((name.actual (intern name.actual-str)))
    (set name.actual (copy-state-node state-node))
    (setf (op-name (eval name.actual)) name.actual)
    name.actual))

(defun initialize-state-node ()
  (let (local-facts local-facts-terms-triple implied-facts
		    (name-state-node-name (gensym "STATE-NODE"))
		    (location (find-location 'AG *world-facts*)))
    (when (null *roadmap-knowledge*)
      (return-from initialize-state-node
		   "** You need to do a place-object for AG before initializing"))
    (setq *visited-places* (list location))
    (setq *visited-objects* nil)
    (setq implied-facts
	  (all-inferences *world-facts* *general-knowledge* *inference-limit*))
    (add_htable_to_hashtable implied-facts *world-facts* 'NIL)
    (setq local-facts-terms-triple (facts-evident-to 'AG *world-facts* 'T))

    (setq local-facts (first local-facts-terms-triple))
    (setq new-terms (second local-facts-terms-triple))
    (setq new-terms (append new-terms (add_htable_to_hashtable *extra-initial-knowledge* local-facts 'T)))
    (setq new-terms (append new-terms (add_htable_to_hashtable *roadmap-knowledge* local-facts 'T)))

    (setq new-terms (append new-terms (add_htable_to_hashtable (all-inferences local-facts *general-knowledge* *inference-limit*) local-facts 'T)))

    (set new-state-node-name
	 (make-state-node 
	   :terms new-terms
	   :name new-state-node-name
	   :wff-htable local-facts
	   :local-value 0 
	   :forward-value 2))

    (setq *event-queue* '())
    (setq *real-clock* 0)
    (setq *AG-clock* 0)
    (setq *total-value* 0)
    (setq *real-history* '())
    (setq *AG-history* '())
    (setq *curr-state-node* (eval new-state-node-name))
    (setq *node-now* *curr-state-node*)))

(defun facts-evident-to (agent wff-htable to-collect-terms)
  (let* ((objects (objects-colored-with agent wff-htable))
	 (aug-objects (cons agent objects))
	 (evident-wff-htable (make-hash-table :test #'equal))
	 wffs-at-curr-key
	 terms-evident-to
	 list-of-evident-wffs)
    (loop for value being the hash-values of wff-htable
	  using (hash-key key)
	  do (setq wffs-at-curr-key
		   (remove-if #'occluded-fact
			      (remove-if-not 
				#'(lambda (w) (memberf (second w) aug-objects)) (cdr value))))
	  (setq terms-evident-to (append
				   (add_list_of_tuples_to_hashtable
				     wffs-at-curr-key evident-wff-htable to-collect-terms)
				   terms-evident-to))
	  (setq list-of-evident-wffs (unionf wffs-at-curr-key list-of-evident-wffs)))
    (cons evident-wff-htable (list terms-evident-to list-of-evident-wffs))))

(defun objects-colocated-with (agent wff-htable) 
  (prog (loc key local-objects left-comoving-wffs right-comoving-wffs something-new)

	(setq loc (find-location agent wff-htable))
	(setq key (convert_pred_to_hashkey (list 'is_at '?x loc)))
	(setq local-objects
	      (mapcar #'second (cdr (gethash key wff-htable))))

	(setq left-comoving-wffs
	      (apply 'append
		     (mapcar #'(lambda (x) (cdr x))
			     (mapcar #'(lambda (key) (gethash (list key) wff-htable)) *left-comoving-preds*)
		     )
	      )
	)

	(setq right-comoving-wffs
	      (apply 'append
		     (mapcar #'(lambda (x) (cdr x))
			     (mapcar #'(lambda (key) (gethash (list key) wff-htable)) *right-comoving-preds*)
			     )
		     )
	      )

	more (setq something-new nil)
	(dolist (wff left-comoving-wffs)
	  (when (memberf (third wff) local-objects)
	    (setq something-new nil)
	    (push (second wff) local-objects)))
	
	(dolist (wff right-comoving-wffs)
	  (when (memberf (second wff) local-objects)
	    (setq something-new nil)
	    (push (third wff) local-objects) ))

	(if something-new (go more))

	(setq local-objects (remove-duplicates local-objects :test #'equal))
	(setq *visited-objects* (unionf *visited-objects* local-objects))
	(return local-objects)))

(defun occluded-fact (wff) 
  (cond ((atom wff) (member wff *occluded-preds*))
	(t (and (member (car wff) *occluded-preds*)
		(or (null (second wff))
		    (not (eq (second wff) 'AG)) ))) ))

(defun all-inferences (ground-facts-htable general-facts limit)
  (let ((rule-packets (mapcar #'list general-facts))
	(facts-htable ground-facts-htable)
	facts-and-packets
	(inference-htable (make-hash-table :test #'equal)))
    (dotimes (i limit)
      (when (zerop (hash-table-count facts-htable))
	(return-from all-inferences inferences-htable))
      (setq facts-and-packets
	    (new-inferences facts-htable rule-packets inferences-htable))
      (setq facts-htable (car facts-and-packets)
	    rule-packets (cdr facts-and-packets)))
    inference-htable))

(defun new-inferences (facts-htable rule-packets inferences-htable)
  (let ((double-packets
	  (mapcar 
	    #'(lambda (x) (cons (car x) (cons nil (cdr x))))
	    rule-packets))
	new-packets)
    (dolist (rp double-packets)
      (setq double-packets
	    (mapcar #'(lambda (p) (graft-into-packet facts-htable p)) double-packets)))

    (dolist (augm-packet double-packets)
      (when (second augm-packet)
	(shake-packet augm-packet inferences-htable)))

    (setq new-packets
	  (mapcar #'(lambda (x) (append (list (car x)) (second x) (cddr x)))
		  double-packets))
    (cons inferences-htable new-packets)))

(defun graft-into-packet (facts-htable augm-packet)
  (let* ((result augm-packet)
	 (rule (car result))
	 (goals (goals-of-rule rule))
	 (wff-list (cdr (gethash (convert_pred_to_hashkey (car rule)) facts-htable))))
    (dolist (wff wff-list)
      (when (and (not (memberf wff (second result)))
		 (not (memberf wff (cddr result)))
		 (find-if #'(lambda (g) (unifier g wff)) goals))
	(setq result (cons rule (cons (cons wff
					    (second result)) (cddr result))))))
    result))

(defun goals-of-rule (rule)
  (let ((goals (car rule)))
    (cond ((null goals) nil)
	  ((atom goals) (list goals))
	  ((eq (car goals) 'and) (cdr goals))
	  ((listp (car goals)) goals)
	  (t (list goals)))
    ))

(defun shake-packet (augm-packet inferences-htable)
  (let* ((rule (car augm-packet))
	 (new-facts (second augm-packet))
	 (old-facts (cddr augm-packet))
	 (all-facts (append new-facts old-facts))
	 (new-facts-htable (make-htable new-facts))
	 goals
	 goals2
	 bindings
	 bindings2
	 )
    (setq goals (goals-of-rule rule))
    (setq bindings
	  (apply #'append
		 (mapcar 
		   #'(lambda (g)
		       (all-bindings-of-posgoal-to-fact-htable g new-facts-htable))
		   goals)))
    (dolist (u bindings)
      (setq goals2 (subst-unifier-in-wffs u goals))
      (setq goals2 (set-differencef goals2 new-facts))
      (setq bindings2 
	    (find-all-positive-bindings goals2 all-facts))
      (setq bindings2
	    (mapcar #'(lambda (u2) (*append u u2)) bindings2))
      (dolist (u2 bindings2)
	(add_tuple_to_hashtable (subst-unifier u2 (third rule)) inferences-htable 'NIL)))
    inferences-htable))

(defun notice-new-local-facts (state-node)
  (let* ((wff-htable (state-node-wff-htable state-node))
	 (new-terms (state-node-terms state-node))
	 (local-beliefs (facts-evident-to 'AG wff-htable 'NIL))
	 (local-facts (facts-evident-to 'AG *world-facts* 'NIL))
	 falsified-facts implied-facts)
    (setq falsified-facts
	  (set-differencef (third local-beliefs) (third local-facts)))
    (setq new-terms (removef
		      (remove_list_of_tuples_from_hashtable falsified-facts wff-htable 'T)
		      new-terms))
    (setq new-terms (append
		      (add_list_of_tuples_to_hashtable (third local-facts) wff-htable 'T)
		      new-terms))
    (setq implied-facts
	  (all-inferences wff-htable *general-knowledge* *inference-limit*))
    (setq new-terms (append
		      (add_htable_to_hashtable implied-facts wff-htable 'T)
		      new-terms))
    (setf (state-node-terms state-node) new-terms)
    (setq *here* (find-location 'AG wff-htable))
    (setq *visited-places* (remove-duplicates (cons *here* *visited-places*)))
    wff-htable))

(defun find-location (obj wffs-htable) 
  (let ((key (convert_pred_to_hashkey (list 'is_at obj '?x))) result)
    (when (gethash key wffs-htable)
      (setq result (third (second (gethash key wffs-htable))))
      )
    result))


;;;;;;;; Next two functions need to be changed to match the new agent ;;;;;;;;;;;;

(defun state-value (additions deletions prior-local-value)
  (let ((local-value prior-local-value) pred incr)
    (dolist (wff additions)
      (when (listp wff)
	(setq pred (car wff))
	(setq incr
	      (case pred
		((knows has) 
		 (if (eq (second wff) 'AG) 1 0) )
		(wants 
		  (if (eq (second wff) 'AG) 1 0))
		(wants
		  (if (eq (second wff) 'USER) 
		    (if (listp (third wff))
		      (if (> (length (third wff)) 1)
			(if (listp (second (third wff)))
			  (if (> (length (second (third wff))) 3)
			    (if (and (eq (first (second (third wff)))
					 'tells)
				     (eq (second (second (third wff))) 'AG)
				     (eq (third (second (third wff))) 'USER))
			      )
			    0
			    )
			  0
			  )
			0
			)
		      0
		      )
		    0
		    ))
		(likes 
		  (if (eq (third wff) 'AG) 1 0))
		(bored 
		  (if (eq (second wff) 'AG) -1 0))
		(is_thirsty_to_degree
		  (if (eq (second wff) 'AG) (- (third wff)) 0))
		(is_hungry_to_degree
		  (if (eq (second wff) 'AG) (- (third wff)) 0))
		(t 0)))
	(incf local-value incr)))
    (dolist (wff deletions)
      (when (listp wff)
	(setq pred (car wff))
	(setq incr
	      (case pred
		(wants 
		  (if (eq (second wff) 'USER)
		    (if (listp (third wff))
		      (if (listp (second (third wff)))
			(if (> (length (second (third wff))) 3)
			  (if (and (eq (second (third wff))) 'tells)
			    (eq (second (second (third wff))) 'AG)
			    (eq (third (second (third wff))) 'USER))
			  50 0) 
			0)
		      0)
		    0)
		  0)
		0)
	      )
	(likes 
	  (if (eq (third wff) 'AG) -1 0))
	(bored 
	  (if (eq (second wff) 'AG) 1 0))
	(is_thirsty_to_degree
	  (if (eq (second wff) 'AG) (third wff) 0))
	(is_hungry_to_degree
	  (if (eq (second wff) 'AG) (third wff) 0))
	(is_tired_to_degree
	  (if (eq (second wff) 'AG) (third wff) 0))
	(t 0)  ))
    


(defun expected-rewards (wff-htable) 
  2)

