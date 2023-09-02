(define factorial (n)
    (cond ((<= n 1) n)
          (#t (* n (factorial (- n 1))))))

; print the value of 5!
(print (factorial 5))
