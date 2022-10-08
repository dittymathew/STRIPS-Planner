(define (problem pb4)
   (:domain blocksworld)
   (:objects a b c d)
   (:init  (on-table a) (on b a)  
            (arm-empty))

   (:goal (and (on a b) )))
