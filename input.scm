;;check define
;;(define a 3)


;;check set free 
;;(set! a 5)
;;a

;;check set param 
;;((lambda (x) (set! x 3) x) 2)

;;check set bound 
;;(((lambda (x) (lambda (y) (set! x 3) x)) 2) 5) dont padd 

;;check var param, var bound, setBox 
;;(lambda (x) (x (lambda () (set! x 4)))) dont pass

;;check or
;;(or #f 2 (lambda (x) x))

;;check seq
;;(begin 1 2 3) 
;;((lambda (x) 1 2 x) 3) 

;;'helloooo

(car '(1 2 3))

