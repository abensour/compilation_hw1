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
;;(car '(1 2 3))
;;(cdr '(1 2 3))
;;(cons 1 2)
;;(define x '(1 2 3))
;;(set-car! x 4)
;;x
;;(set-cdr! x '(1 2))
;;x
;;(apply + '(1 2))
(apply cons '(5 6))
;;(< 1 1)
;;'(#{x}=#{y}=2 #{x} #{y}) 
;;(define y '(#{a}=#t #{a}))
;;y
;;'#{x}=(1 . #{x})


