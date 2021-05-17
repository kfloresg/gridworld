;;; Compiling error? ;;;

(defun go! ()
  (let (poss-actions step action-name old-wffs old-terms) 
    (format t "~% GO ~%") 

    (setq poss-actions
	  (chain-forward *curr-state-node* *search-beam*))
    (when (null poss-action)
      (incf *Ag-clock* 1)
      (incf *real-world* 1)
      (return-from go! "NO MORE ACTIONS POSSIBLE")
      )
    (format t "~%~% POSSIBLE ACTIONS & VALUES: ~a" poss-actions) 
    (format t "~% SEEMINGLY BEST PLAN: ~a" *plan*) 

    (setq old-wffs (state-node-wff-htable *curr-state-node*)) 
    (setq old-terms (state-node-terms *curr-state-node*))
    (setq *curr-state-node* 
	  (eval (cdar (state-node-terms *curr-state-node*))))

    (setf (state-node-terms *curr-state-node*) old-terms)
    (clrhash (state-node-wff-htable *curr-state-node*))
    (add_htable_to_hashtable old-wffs
			     (state-node-wff-htable *curr-state-node*) 'NIL)

    (setq step (pop *plan*))

    (format t "~%~% STEP TO BE TAKEN: ~a" step) 
    (format t "~% EXPECTED STATE: ~% ~a" (second *states*))

    (pop *plan*) 
    (pop *states*) 

    (setf (state-node-operators *curr-state-node*) nil) 
    (setf (state-node-children *curr-state-node*) nil)

    (if (state-node-parent *curr-state-node*) 
      (if (state-node-parent (eval (cdr (state-node-parent *curr-state-node*))))
	(setf (state-node-parent (eval (cdr (state-node-parent *curr-state-node*))))
	      nil)))

    (setq action-name (car (state-node-parent *curr-state-node*)))
    (setq *node-now* *curr-state-node*)
    (implement-effects action-name)
    )
  )
