(let ((x #f))
  (let ()
    x))
(let ((x #f) (y #t))
  (let ((x #f))
    (let ((x #f) (z #f) (t #f))
      (let ((x #f) (t #f))
	y))))
(((((lambda (x) ((x x) (x x)))
    (lambda (x)
      (lambda (y)
	(x (x y)))))
   (lambda (p)
     (p (lambda (x y)
	  (lambda (p)
	    (p y x))))))
  (lambda (z) (z #t #f)))
 (lambda (x y) x))