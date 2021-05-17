;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Gridworld = Library Agent
;;
;; Kenda Flores-Garcia
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-roadmap 
  '(front-desk reserved-shelf return-bin costumer-care) 
  '((p1 front-desk 1 return-bin) 
    (p2 front-desk 2 reserved-shelf) 
    (p3 front-desk 3 costumer-care)
    (p4 costumer-care 5 lounge)
    (p5 lounge 1 kitchen)
    )
)

(def-object 'robot '(is_animate can_talk))
(def-object 'patron '(is_animate can_talk))
(def-object 'rep '(is_animate can_talk is_friend is_working))
(def-object 'book '(is_inanimate is_due can_renew is_reserved))
(def-object 'hamburger '(is_inanimate is_edible (has_cost 3.0)))
(def-object 'game '(is_fun (has_cost 4.0)))

(place-object 'LG 'robot 'fron-desk 0
	      nil 
	      ;current-facts
	      '((is_hungry_to_degree LG 2.0)
		(is_tired_to_degree LG 1.0)
		(is_bored_to_degree LG 3.0)
		(can_talk costumer)
		(is_at costumer front-desk)
		(is_at book1 reserved-shelf))
	      ;attitudes
	      '((knows LG (whether (is_reserved book1)))
		(knows LG (that (knows friend (whether (can_borrow book2))))))
)

(place-object 'book1 'book 'reserved-shelf 0 nil 
             ;;current facts
	      '((is_reserved book1))
	      nil
)

(place-object 'book2 'book 'returned-bin 0 nil
	      '((can_borrow book2))
	      nil
	      )

(place-object 'costumer 'patron 'front-desk 0 nil
       ;;current facts
       nil 
       ;;attitudes
       '((knows costumer (whether (can_borrow book2))))
       )

(place-object 'friend 'rep 'costumer-service 0 nil
	      '((is_working friend))
	      nil )

(place-object 'hamburger1 'hamburger 'kitchen 0 nil
	      '((is_edible hambuger1))
	      nil)

(place-object 'mariokart 'game 'lounge 0 nil
	      '((is_fun mariokart))
	      nil)

(setq *operators* '(walk eat can_sleep  answer_user_ynq answer_user_whq play return_book get_book)) 
(setq *search-beam* (list (cons 3 *operators*) (cons 2 *operators*) (cons 2 *operators*) (cons 2 *operators*)))

(defun answer_to_ynq? (wff)
  (check-yn-fact-in-kb 'NIL wff (state-node-wff-htable *curr-state-node*))
)

(defun answer_to_ynq.actual? (wff) 
  (check-yn-fact-in-kb 'T wff (state-node-wff-htable *curr-state-node*))
 )

(defun answer_to_whq? (wff)
  (check-whq-answer-in-kb 'NIL wff (state-node-wff-htable *curr-state-node*))
  )

(defun answer_to_whq.actual? (wff)
  (check-whq-answer-in-kb 'T wff (state-node-wff-htable *curr-state-node*))
  )

(setq emergency.actual
      (make-op.actual :name 'emergency.actual :pars '()
		      :startconds '((not (there_is_help))
				    (+ 3 (random 20)))
		      :starredconds '((= 1 (random 2))
				      (there_is_help))
		      :starredDeletes '((there_is_a_emergency))
		      :starredAdds '((navigable PATH1) (navigable PATH2) (navigable PATH3) (navigable PATH4))
		      :deletes '((navigable PATH1) (navigable PATH2) (navigable PATH3) (navigable PATH4))
		      :adds '((there_is_a_emergency))
		      )
      )

(setq help.actual
      (make-op.actual :name 'help.actual :pars '()
		      :startconds '((= 1 (random 3)))
		      :starredStopConds '((= 2 (random 4)))
		      :starredDeletes '((there_is_rain))
		      :adds '((there_is_help)) 
		      )
      )

(setq answer_user_ynq 
      (make-op :name 'answer_user_ynq :pars '(?q)
	       :preconds '( (wants USER (that (tells LG USER (whether ?q)))) )
	       :effects '( (not (wants USER (that (tells LG USER (whether ?q)))))
			  (knows USER (that (answer_to_ynq? ?q)))
			  )
	       :time-required 1
	       :value 10
	       )
      )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(setq answer_user_ynq.actual 
      	(make-op.actual :name 'answer_user_ynq.actual :pars '(?q)
	:startconds '( (wants USER (that (tells LG USER (whether ?q)))) )
	:stopconds '( (not (wants USER (that (tells LG USER (whether ?q))))) )
	:deletes '( (wants USER (that (tells LG USER (whether ?q)))) )
	:adds '( 
		 (says+to+at_time LG (that (answer_to_ynq.actual? ?q)) USER (current_time?))
		  (not (wants USER (that (tells LG USER (whether ?q)))))
		  )
	)
)

(setq answer_user_whq 
      	(make-op :name 'answer_user_whq :pars '(?q)
	:preconds '( (wants USER (that (tells LG USER (answer_to_whq ?q)))) )
	:effects '( (not (wants USER (that (tells LG USER (answer_to_whq ?q)))))
			(knows USER (that (answer_to_whq? ?q)))
		 )
	:time-required 1
	:value 10
	)
)

(setq answer_user_whq.actual 
      	(make-op.actual :name 'answer_user_whq.actual :pars '(?q)
	:startconds '( (wants USER (that (tells LG USER (answer_to_whq ?q)))) )
	:stopconds '( (not (wants USER (that (tells LG USER (answer_to_whq ?q))))) )
	:deletes '( (wants USER (that (tells LG USER (answer_to_whq ?q)))) )
	:adds	'( ;(knows USER (that (answer_to_whq.actual? ?q)))				
		(says+to+at_time AG (that (answer_to_whq.actual? ?q)) USER (current_time?))
		 (not (wants USER (that (tells LG USER (answer_to_whq ?q)))))
		 )
	)	
)

(setq walk 
      	(make-op :name 'walk :pars '(?x ?y ?z ?f)
	:preconds '((is_at LG ?x)        
			(is_on ?x ?z)        
			(is_on ?y ?z) (point ?y)
			(navigable ?z)
		(is_tired_to_degree AG ?f) )
	:effects '((is_at LG ?y) 
		(not (is_at LG ?x))
		(is_tired_to_degree LG (+ ?f (* 0.5 (distance_from+to+on? ?x ?y ?z))))  
		(not (is_tired_to_degree LG ?f)) )
	:time-required '(distance_from+to+on? ?x ?y ?z)
	:value '(- 3 ?f)
	)
)

(defun distance_from+to+on? (x y z)
  	(let (result pt1 pt2 units index1 index2 str)
		(if (and (evalFunctionPredicate (cons 'point (list x))) (evalFunctionPredicate (cons 'point (list y))))
			(dolist (triple (get x 'next))
			  (when (and (eq z (first triple)) (eq y (second triple)))
				(setq result (third triple))
				(return-from distance_from+to+on? result)
			  )
			)
			(progn
				(if (atom x)
					(setq str (string x))
					(setq str (apply (car x) (cdr x))); (string x))
				)					
				(setq index1 (search "PT_" str))
				(setq index2 (search "_UNITS" str))
				(setq units (parse-integer (subseq str (+ index1 3) index2)))
				(setq index1 (search "FROM_" str))
				(setq index2 (search "_TOWARDS" str))									       (setq pt1 (INTERN (string-upcase (subseq str (+ index1 5) index2))))	
				(setq index1 (+ index2 9))										       (setq index2 (search "_ON" str))										      (setq pt2 (INTERN (string-upcase (subseq str index1 index2))))
				(if (and (eq pt1 x) (eq pt2 y))												(return-from distance_from+to+on? (- (distance_from+to+on? pt1 pt2 z) units))
				  (return-from distance_from+to+on? units)
																		)													)
			)
		)
	)

(setq walk.actual 
      	(make-op.actual :name 'walk.actual :pars '(?x ?y ?z ?f)
	:startconds '((is_at LG ?x)        
		      (is_on ?x ?z)        
		      (is_on ?y ?z) (point y)
		      (navigable ?z)
		      (is_tired_to_degree AG ?f) )
	:stopconds '((not (navigable ?z)) 
		     (is_at LG ?y) )
	:deletes '((is_at LG ?#1)
		   (is_tired_to_degree LG ?#2))
	:adds '((is_at AG (the_pt+units_from+towards+on_road? (* 1 (elapsed_time?)) ?x ?y ?z))
		(is_at AG (the_pt+units_from+towards+on_road? (- (distance_from+to+on? ?x ?y ?z) (* 1 (elapsed_time?))) ?y ?x ?z))
		(is_on (the_pt+units_from+towards+on_road? (* 1 (elapsed_time?)) ?x ?y ?z) ?z)
		(is_on (the_pt+units_from+towards+on_road? (- (distance_from+to+on? ?x ?y ?z) (* 1 (elapsed_time?))) ?y ?x ?z) ?z)										        		(is_tired_to_degree LG (+ ?f (* 0.5 (elapsed_time?)))) )
	 )
)

(setq can_sleep 
      	(make-op :name 'sleep :pars '(?f ?h)
		 :preconds '((is_at LG lounge)
			     (is_tired_to_degree LG ?f 0.5)
			     (>= ?f 2.5);(>= ?f 0.5)
			     (is_hungry_to_degree LG ?h)
			     (> ?f ?h) ; more tired than hungry
			     (not (there_is_a_emergency))						
			     (not (there_is_help)) )
		 :effects '((is_tired_to_degree LG 0.0)
			    (not (is_tired_to_degree LG ?f))
			    (is_hungry_to_degree LG (+ ?h (* 0.5 ?f))) )
		 :time-required '(* 4 ?f)
		 :value '(* 1 ?f)
		 )
	)

(setq can_sleep.actual 
      (make-op.actual :name 'sleep.actual :pars '(?f ?h) ; level of fatigue ?f 
		      :startconds '((is_at LG lounge)
				    (is_tired_to_degree LG ?f)
				    (>= ?f 2.5)
				    (is_hungry_to_degree LG ?h)
				    (> ?f ?h) ); more tired than hungry
		      :stopconds '((there_is_a_emergency)
				   (is_tired_to_degree LG 0.0))
		      :deletes '((is_tired_to_degree LG ?#1) 
				 (is_hungry_to_degree LG ?#2) )
		      :adds '((is_tired_to_degree LG (- ?f (* 0.5 (elapsed_time?))))
			      (is_hungry_to_degree LG (+ ?h (* 0.25 (elapsed_time?)))) ) 
		      )
      )

(setq eat 
      (make-op :name 'eat :pars '(?h ?x ?y) ; level of hunger ?h
	       :preconds '( (is_hungry_to_degree LG ?h) 
			   (>= ?h 2.0)
			   (is_at LG ?y) 
			   (is_at ?x ?y) 
			   (is_edible ?x) 
			   (knows LG (whether (is_edible ?x)))
			   (not (there_is_a_emergency))
			   (not (there_is_help)) )
	       :effects '( (is_hungry_to_degree LG 0.0) 
			  (not (is_hungry_to_degree LG ?h)) )
	       :time-required 1
	       :value '(* 2 ?h)
	       )
      )

(setq eat.actual 
      (make-op.actual :name 'eat.actual :pars '(?h ?x ?y)
		      :startconds '( (is_hungry_to_degree AG ?h) 
				    (>= ?h 2.0)
				    (is_at LG ?y) 
				    (is_at ?x ?y) 
				    (is_edible ?x) 
				    (knows LG (whether (is_edible ?x))) )
			:stopconds '( (there_is_a_emergency)
				     (there_is_help) 
				      (is_hungry_to_degree LG 0.0) )
			:deletes '( (is_hungry_to_degree LG ?#1) )
			:adds '( (is_hungry_to_degree LG 0.0) )
			)
      )

(setq play 
      (make-op :name 'play :pars '(?h ?f ?x ?y) 
	       :preconds '( (is_bored LG) 
			   (is_at LG ?y) 
			   (is_at ?x ?y) 
			   (is_playable ?x) 
			   (is_thirsty_to_degree LG ?h)
			    (is_tired_to_degree LG ?f)
			    (knows LG (whether (is_playable ?x))) )
	       :effects '( (not (is_bored LG)) 
			  (not (is_thirsty_to_degree LG ?h))
			  (not (is_tired_to_degree LG ?f))
			  (is_thirsty_to_degree LG (+ ?h 0.5))
			  (is_tired_to_degree LG (+ ?f 0.5)) )
	       :time-required 1
	       :value 3
	       )
      )

(setq play.actual
      (make-op.actual :name 'play.actual :pars '(?h ?f ?x ?y)
		      :startconds '( (is_bored LG)
				    (is_at LG ?y)
				    (is_playable ?x) 
				    (is_thirsty_to_degree LG ?h)
				    (is_tired_to_degree LG ?f)
				    (knows LG (whether (is_playable ?x))) ) 
		      :stopconds '( (not (is_bored LG)) )
		      :deletes '( (is_tired_to_degree LG ?#2) 
				 (is_thirsty_to_degree LG ?#1)
				  (is_bored LG) )
		      :adds '( (is_tired_to_degree LG (+ ?f (* 0.5 (elapsed_time?))))
			      (is_thirsty_to_degree LG (+ ?h (* 0.5 (elapsed_time?)))) ) 
		      )
      )

(setq return_book 
      (make-op :name 'return-book :pars '(?x ?y)
		      :preconds '((is_at LG ?y)
				  (is_at ?x ?y))
		      :effects '((is_tired_to_degree LG .5))
		      :time-required 1
		      :value 2))

(setq return_book
      (make-op.actual :name 'return-book.actual :pars '(?x ?y)
		      :startconds '((is_at LG ?y)
				    (is_at ?x ?y))
		      :stopconds '((returned ?x))
		      :deletes nil
		      :adds '((is_tired_to_degree LG .5))))

(setq get_book
      (make-op :name 'get_book :pars '(?x ?y)
	       :preconds '((is_at LG ?y)
			   (is_at ?x ?y))
	       :effects '((is_tired_to_degree LG .5))
	       :time-required 1
	       :value 2))

(setq get_book.actual
      (make-op :name 'get_book.actual :pars '(?x ?y)
	       :preconds '((is_at LG ?y)
			   (is_at ?x ?y))
	       :stopconds '((is_at LG ?x))
	       :deletes nil 
	       :adds '((is_tired_to_degree LG .5)) ))
