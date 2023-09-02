(define fibonacci (n) 
    (cond ((<= n 2) 1)
          (#t (+ (fibonacci (- n 1)) (fibonacci (- n 2))))))

; print the 10th fibonacci number
(print (fibonacci 10))
