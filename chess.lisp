;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; chess.lisp
;;;
;;; christopher bowron - bowronch@cse.msu.edu
;;;
;;;            digital dreamland 1999
;;; ... we came, we saw, we got bored and left ...

;;; copyright 1999 christopher bowron

;; to do.. 
;; ???

;; done
;; fix domove, save-variables only when they change
;; declare all variable types - do, do*, dolist left


(proclaim '(optimize (speed 3)))
;;		     (compilation-speed 0)
;;		     (debug 0)
;;		     (safety 0)))

;;(setq ext:*gc-verbose* nil)

(deftype chess-board ()
  '(simple-array symbol (8 8)))

(deftype chess-move ()
  'cons)

(deftype chess-color ()
  '(integer -1 1))

;; functions for dealing with moves
(defmacro make-move (sq1 sq2)
  `(cons ,sq1 ,sq2))

(defmacro square1 (move)
  `(car ,move))

(defmacro square2 (move)
  `(cdr ,move))

(defmacro empty-move ()
  `(make-move (make-square 8 8)
	      (make-square 8 8)))


(defvar checkmate 30000)
(defvar stalemate 15000)

(deftype small-fixnum ()
;;  `(signed-byte 32))
  `(integer -30000 30000))

;; functions for dealing with squares
(deftype chess-square ()
  'cons)

(defmacro make-square (x y)
  `(cons ,x ,y))

(defmacro squarex (square)
  `(the small-fixnum (car ,square)))

(defmacro squarey (square)
  `(the small-fixnum (cdr ,square)))

;;;(deftype chess-square ()
;;;  '(simple-array small-fixnum)) 

;;;(defmacro make-square (x y)
;;;  `(make-array 2 :element-type 'small-fixnum :initial-contents '(,x ,y)))

;;;(defmacro squarex (square)
;;;  `(aref ,square 0))

;;;(defmacro squarey (square)
;;;  `(aref ,square 1))

(defmacro nil-square ()
  `(make-square 8 8))

(defvar draw-rep
  (make-square 8 8))

;; global special variables
(defvar *black* -1)
(defvar *white*  1)
(defvar wcancastle (cons t t))
(defvar bcancastle (cons t t))
(defvar wenpassant nil)
(defvar benpassant nil)
(defvar turn 1)
(defvar computer-controlled (cons nil nil))

;; are these right/useful?
(proclaim '(type chess-color turn *white* *black*))
(proclaim '(type cons wcancastle bcancastle computer-controlled))
(proclaim '(type (or null small-fixnum) wenpassant benpassant))
	  

;; not just the hamburger joint
(defvar white-castle (list (make-move (make-square 4 0) (make-square 6 0))
			   (make-move (make-square 4 0) (make-square 2 0))))
(defvar black-castle (list (make-move (make-square 4 7) (make-square 6 7))
			   (make-move (make-square 4 7) (make-square 2 7))))

(proclaim '(type list white-castle black-castle))

;; initial board setup
(defvar *board*
  (make-array '(8 8) :element-type 'symbol
	      :initial-contents
	      '(; mirror image
		(wr  wn  wb  wq  wk  wb  wn  wr)
		(wp  wp  wp  wp  wp  wp  wp  wp)
		(empty empty empty empty empty empty empty empty)
		(empty empty empty empty empty empty empty empty)
		(empty empty empty empty empty empty empty empty)
		(empty empty empty empty empty empty empty empty)
		(bp  bp  bp  bp  bp  bp  bp  bp)
		(br  bn  bb  bq  bk  bb  bn  br)
		)))

(proclaim '(type chess-board *board*))

;; +---------------------------------------------------------------------+
;; is location sq off of the board?
(defun offboardp (sq)
  (declare (type chess-square sq))
  (let ((a (squarex sq))
	(b (squarey sq)))
    (declare (type small-fixnum a b))
    (cond
     ((> a 7) t)
     ((> b 7) t)
     ((< a 0) t)
     ((< b 0) t)
     (t nil))))

;; does a clear path exist directly from sq1 to sq2 ?
(defun clearpathp (sq1 sq2 board)
  (declare (type chess-square sq1 sq1)
	   (type chess-board board))
  (let* ((sx (squarex sq1))
	 (ex (squarex sq2))
	 (sy (squarey sq1))
	 (ey (squarey sq2))
	 (dx (- ex sx))
	 (dy (- ey sy))
	 (res t)
	 (done nil)
	 (x 0)
	 (y 0))
    (declare (type small-fixnum sx ex sy ey dx dy x y)
	     (type symbol res done))

    (setq dx
	  (cond
	   ((= 0 dx) 0)
	   ((> 0 dx) -1)
	   (t 1)))

    (setq dy
	  (cond
	   ((= 0 dy) 0)
	   ((> 0 dy) -1)
	   (t 1)))
    
    
    (setq x sx)
    (setq y sy)
    
    (loop
     (setq x (+ x dx))
     (setq y (+ y dy))

     (when (and (= x ex)
		(= y ey))
       (return))
     (when done
       (return))
     
     (when (not (equalp (getpiecexy x y board) 'empty))
       (setq res nil)
       (setq done t)))
    res))
	
;; functions for accessing board
;; +---------------------------------------------------------------------+
;; get piece at '(x . y)	    
(defun getpiece (locale board)
  (declare (inline) (type chess-square locale) (type chess-board board))
  (aref board (squarey locale) (squarex locale)))

(defun getpiecexy (x y board)
  (declare (inline) (type small-fixnum x y) (type chess-board board))
  (aref board y x))

(defun setpiecexy (x y board piece)
  (declare (inline) (type small-fixnum x y) (type chess-board board)
	   (type symbol piece))
  (setf (aref board y x) piece))

(defun setpiece (locale board piece)
  (declare (inline) (type chess-square locale) (type chess-board board)
	   (type symbol piece))
  
  (setf (aref board (squarey locale) (squarex locale)) piece))


(proclaim '(type (function (chess-square chess-board) symbol) getpiece))
(proclaim '(type (function (small-fixnum small-fixnum chess-board) symbol) getpiecexy))
(proclaim '(type (function (small-fixnum small-fixnum chess-board symbol) nil) setpiecexy))
(proclaim '(type (function (chess-square chess-board symbol) nil) setpiece))

;; +---------------------------------------------------------------------+

;; valid move checker for pawns
(defun pcheck (move board)
  (declare (type chess-board board) (type chess-move move))
  (let* ((sq1 (square1 move))
	 (sq2 (square2 move))
	 (hor (- (squarex sq2) (squarex sq1)))
	 (ver (- (squarey sq2) (squarey sq1)))
	 (color (getcolor (getpiece sq1 board)))
	 (direction color)
	 (start (the small-fixnum (if (= color *white*) 1 6)))
	 (sq2piece (getpiece sq2 board))
	 (sq2color (getcolor sq2piece))
	 (sq2y (squarey sq2))
	 (sq1y (squarey sq1))
	 (newxycolor (getcolor (getpiecexy
			 (squarex sq2) (+ direction (squarey sq1)) board)))
	 )

    (declare (type small-fixnum hor ver direction)
	     (type small-fixnum start sq2y sq1y)
	     (type chess-color color sq2color newxycolor)
	     (type symbol sq2piece)
	     (type chess-square sq1 sq2))
    
    (cond
     ;; pawn can move forward one
     ((and (= sq2color 0)
	   (= 0 hor)
	   (= direction ver))
      t)
     ;; pawn can move forward 2 on first move
     ((and (= 0 hor)
	   (= (* 2 direction) ver)
	   (= sq2color 0)
	   (= newxycolor 0)
	   (= sq1y start))
      t)
     ;; pawns can attack 1 square diagonally
     ((and (= direction ver)
	   (or (= -1 hor) (= 1 hor))
	   (= sq2color (- color)))
      t)
     ;; white pawns can do en passant
     ((and (= direction ver)
	   (or (= -1 hor) (= 1 hor))
	   (equalp (squarey sq2) 5)
	   (= color *white*)
	   (equalp (squarex sq2) wenpassant))
      t)
     ;; so can black pawns
     ((and (= direction ver)
	   (or (= -1 hor) (= 1 hor))
	   (equalp sq2y 2)
	   (= color *black*)
	   (equalp (squarex sq2) benpassant))
      t)

     ;; and thats all pawns can do
     (t nil))))


(defun ncheck (move board)
  (declare (ignore board) (type chess-move move))
  (let* ((sq1 (square1 move))
	 (sq2 (square2 move))
	 (hor (- (squarex sq2) (squarex sq1)))
	 (ver (- (squarey sq2) (squarey sq1))))
    (declare (type chess-square sq1 sq2)
	     (type small-fixnum hor ver))
    (cond
     ;; knights move (2, 1)
     ((and (= (abs hor) 2)
	   (= (abs ver) 1)) t)

     ;; knights move (1, 2)
     ((and (= (abs ver) 2)
	   (= (abs hor) 1)) t)

     ;; and thats all knights do
     (t nil))
    ))

(defun bcheck (move board)
  (declare (type chess-board board) (type chess-move move))
  (let* ((sq1 (square1 move))
	 (sq2 (square2 move))
	 (hor (- (squarex sq2) (squarex sq1)))
	 (ver (- (squarey sq2) (squarey sq1))))
    (declare (type chess-square sq1 sq2)
	     (type small-fixnum hor ver))
    (cond
     ;; dont divide by zero
     ((= 0 ver) nil)

     ;; bishops move diagaonally
     ((and (or (= hor ver) (= hor (- ver)))
	   (clearpathp sq1 sq2 board))
      t)

     ;; and thats all bishops do
     (t nil))))

(defun rcheck (move board)
  (declare (type chess-board board) (type chess-move move))
  (let* ((sq1 (square1 move))
	 (sq2 (square2 move))
	 (hor (- (squarex sq2) (squarex sq1)))
	 (ver (- (squarey sq2) (squarey sq1))))
    (declare (type chess-square sq1 sq2)
	     (type small-fixnum hor ver))
    (cond
     ;; rooks move side to side
     ((and (= hor 0)
	   (clearpathp sq1 sq2 board)) t)

     ;; rooks move up and down
     ((and (= ver 0)
	   (clearpathp sq1 sq2 board)) t)

     ;; and thats all rooks do
     (t nil))))

(defun qcheck (move board)
  (declare (type chess-board board) (type chess-move move))
  ;; queens can do any move rook or bishop can do
  (or
   (bcheck move board) 
   (rcheck move board)))

;; what can the king do?
(defun kcheck (move board)
  (declare (type chess-board board) (type chess-move move))
  (let* ((sq1 (square1 move))
	 (sq2 (square2 move))
	 (hor (- (squarex sq2) (squarex sq1)))
	 (ver (- (squarey sq2) (squarey sq1))))
    (declare (type chess-square sq1 sq2)
	     (type small-fixnum hor ver))
    (cond
     ;; king can move 1 in any direction
     ((and (<= (abs hor) 1)
	   (<= (abs ver) 1)) t)

     ;; white castling
     ;; king side
     ((and (equalp move (nth 0 white-castle))
	   (clearpathp sq1 sq2 board)
	   (car wcancastle)
	   (not (incheckp *white* board))
	   (not (check-checker '((4 . 0) . (5 . 0)) *white* board)))
      t)
     ;; queen side
     ((and (equalp move (nth 1 white-castle))
	   (clearpathp sq1 '(0 . 0) board)
	   (cdr wcancastle)
	   (not (incheckp *white* board))
	   (not (check-checker '((4 . 0) . (3 . 0)) *white* board)))
      t) 

     ;; black castling - king side
     ((and (equalp move (nth 0 black-castle))
	   (clearpathp sq1 sq2 board)
	   (car bcancastle)
	   (not (incheckp *black* board))
	   (not (check-checker '((4 . 7) . (5 . 7)) *black* board)))
      t)
     ;; queen side
     ((and (equalp move (nth 1 black-castle))
	   (clearpathp sq1 '(0 . 7) board)
	   (cdr bcancastle)
	   (not (incheckp *black* board))
	   (not (check-checker '((4 . 7) . (3 . 7)) *black* board)))
      t)
     
     (t nil))))

;; empty squares just arent what they used to be
(defun echeck (move board)
  (declare (ignore move board))
  nil)

;; +---------------------------------------------------------------------+
;; piece declarations
(defvar wp `("P" ,#'pcheck ,1   pawn-moves  ))
(defvar wn `("N" ,#'ncheck ,3   knight-moves))
(defvar wb `("B" ,#'bcheck ,3   bishop-moves))
(defvar wr `("R" ,#'rcheck ,5   rook-moves  ))
(defvar wq `("Q" ,#'qcheck ,10  queen-moves ))
(defvar wk `("K" ,#'kcheck ,200 king-moves ))

(defvar bp `("p" ,#'pcheck ,-1   pawn-moves  ))
(defvar bn `("n" ,#'ncheck ,-3   knight-moves))
(defvar bb `("b" ,#'bcheck ,-3   bishop-moves))
(defvar br `("r" ,#'rcheck ,-5   rook-moves  ))
(defvar bq `("q" ,#'qcheck ,-10  queen-moves ))
(defvar bk `("k" ,#'kcheck ,-200 king-moves  ))

(defvar empty `(" " ,#'echeck ,0))

(proclaim '(type list wp wn wb wr wq wk))
(proclaim '(type list bp bn bb br bq bk))
(proclaim '(type list empty))
;; +---------------------------------------------------------------------+
;; return 1 for white, -1 for black, 0 for empty

(defun getcolor (piece)
  (declare (inline) (type symbol piece))
  (let ((temp (third (symbol-value piece))))
    (declare (type small-fixnum temp))
    (cond
     ((= 0 temp) 0)
     ((> 0 temp) -1)
     (t 1))))

(proclaim '(type (function (symbol) chess-color) getcolor))

;;; print out the current board 
(defun printboard (board)
  (declare (type chess-board board))
  (format t "    a   b   c   d   e   f   g   h  ~%")
  (format t "  +---+---+---+---+---+---+---+---+~%")
  (do ((x 7 (- x 1)))
      ((< x 0) nil)
      (declare (type small-fixnum x))
      (format t "~a |" (1+ x))
      (do ((y 0 (+ y 1)))
	  ((> y 7) nil)
	  (declare (type small-fixnum y))
	  ;;(if (= (mod (+ x y) 2) 1)
	      (format t " ~a |"
		      (car (symbol-value (getpiecexy y x board))))
	  ;;   (format t "*~a*|"
          ;;    (car (symbol-value (getpiecexy y x board)))))
	    
	  )
	    
      (format t " ~a~%" (1+ x))
      (format t "  +---+---+---+---+---+---+---+---+~%")
      )
  (format t "    a   b   c   d   e   f   g   h  ~%"))

;; get move from player
(defun getmove ()
  (let ((s1 "")
	(s2 "")
	(sq1 (nil-square))
	(sq2 (nil-square))
	(r (string-downcase (read-line t nil nil))))
    (declare (type string s1 s2)
	     (type chess-square sq1 sq2)
	     (string r))
    (format t "~a~%" r)

    (cond
     ((equalp r "draw")
      (format t "you offer draw~%")
      draw-rep)
     ((not (equalp (position #\- r) 2)) nil)
     (t
      (setq s1 (subseq r 0 (position #\- r)))
      (setq s2 (subseq r (1+ (position #\- r))))
      (setq sq1
	    (make-square (- (char-int (char s1 0)) (char-int #\a))
			 (- (char-int (char s1 1)) (char-int #\1))))
      (setq sq2
	    (make-square (- (char-int (char s2 0)) (char-int #\a))
			 (- (char-int (char s2 1)) (char-int #\1))))
      
      (format t "move : from ~a to ~a~%" sq1 sq2)
      (make-move sq1 sq2)))))

;; initialize board
(defun initboard ()
  (setq wcancastle (cons t t))
  (setq bcancastle (cons t t))
  (setq wenpassant nil)
  (setq benpassant nil)
  (setq turn 1)
  (setq *board*
	(make-array '(8 8) :element-type 'symbol
		    :initial-contents
		    '(; mirror image
		      (wr  wn  wb  wq  wk  wb  wn  wr)
		      (wp  wp  wp  wp  wp  wp  wp  wp)
		      (empty empty empty empty empty empty empty empty)
		      (empty empty empty empty empty empty empty empty)
		      (empty empty empty empty empty empty empty empty)
		      (empty empty empty empty empty empty empty empty)
		      (bp  bp  bp  bp  bp  bp  bp  bp)
		      (br  bn  bb  bq  bk  bb  bn  br)
		      )))
  "Board Setup")

;; play a game
(defun newgame()
  (let ((white 1)
	(black 1)
	(wm (empty-move))
	(bm (empty-move))
	(undolist nil))
    (declare (type small-fixnum white black)
	     (type list bm wm)
	     (type list undolist))
    (do ((done nil))
	(done undolist)
	(declare (type symbol done))
	(loop
	  
	 (printboard *board*)

	 (when (game-over-p *board*)
	   (setq done t)
	   (return))
	 
	 ;;(when (equalp computer-controlled '(t . t))
	 ;;  (format t "press return to continue~%")
	 ;;  (when (equalp (read-line) "exit")
	 ;;    (setq done t)
	 ;;    (return)))

	 (format t "W ~a : " white)
	 (force-output)
	 (setq turn *white*)
	 (setq wm (if (car computer-controlled)
			(compmove *white* *board*)
		    (getmove)))
	 
	 (when (null wm)
	   (return (setq done t)))

	 (if (and (cdr computer-controlled) (equalp wm draw-rep))

	     (format t "draw is denied... play on~%")
	   
	   (when (validp wm *board*)
	     (format t "white moves: ~a~%" (algebraic wm))	 
	     (push (domove wm *board*) undolist)
	     (return)))

	 (format t "invalid move~%"))
	(setq white (1+ white))

	(when done (return undolist))
	
	(loop
	 (printboard *board*)

	 (setq turn *black*)

	 (when (game-over-p *board*)
	   (setq done t)
	   (return))

	 (format t "B ~a : " black)
	 (force-output)
	 (setq bm (if (cdr computer-controlled)
			(compmove *black* *board*)
		    (getmove)))

	 (when (null bm)
	   (return (setq done t)))

	 (if (and (car computer-controlled) (equalp bm draw-rep))

	     (format t "draw is denied... play on~%")
	   
	   (when (validp bm *board*)
	     (format t "black moves: ~a~%" (algebraic bm))
	     (push (domove bm *board*) undolist)
	     (return)))
	 
	 (format t "invalid move~%"))
	(setq black (1+ black))
	)))

;; is the game over and why
(defun game-over-p (board)
  (declare (type chess-board board))
  (let ((done nil))
    (declare (type symbol done))
    (when (= turn *white*)
      (cond
       ((checkmatep *white* board)
	(format t "White checkmated~%")
	(setq done t))
       ((stalematep *white* board)
	(format t "White stalemated~%")
	(setq done t))
       ((incheckp *white* board)
	(format t "White in check~%"))))
   
    (when (= turn *black*)
      (cond
       ((checkmatep *black* board)
	(format t "Black checkmated~%")
	(setq done t))
       ((stalematep *black* board)
	(format t "Black stalemated~%")
	(setq done t))
       ((incheckp *black* board)
	(format t "Black in check~%"))))
    
    done))

;; is the move valid and not into check?
(defun validp (move board)
  (declare (inline) (type chess-move move) (type chess-board board))
  (isvalid move board t))

;; is move valid regardless of check
(defun validp-nocheck (move board)
  (declare (inline) (type chess-move move) (type chess-board board))
  (isvalid move board nil))

;; is the move valid?
(defun isvalid (move board check)
  (declare (type chess-move move)
	   (type chess-board board)
	   (type symbol check))
  (let* ((piece (symbol-value (getpiece (square1 move) board)))
	 (color (getcolor (getpiece (square1 move) board)))
	 (piece3 (third piece))
	 (piece2 (second piece))
	 )
    (declare (type list piece)
	     (type function piece2)
	     (type small-fixnum color piece3))
	     
    (cond
     ;; is it the right color for this turn?
     ;;((< (/ piece3 turn) 0) nil)
     ((and (> piece3 0) (< turn 0)) nil)
     ((and (< piece3 0) (> turn 0)) nil)
     
     ;; is there in fact a 2nd square?
     ((null (square2 move)) nil)
     ;; is it off the board?
     ((offboardp (square2 move)) nil)
     ;; are we taking our own piece?
     ((and (= (getcolor (getpiece (square1 move) board))
	      (getcolor (getpiece (square2 move) board)))) nil)
     ;; does the piece checker say its ok?
     ((not (funcall piece2 move board)) nil)
     ;; are we moving into check?
     ((and check (check-checker move color board)) nil)
     (t t))))

;; will move put color into check?
(defun check-checker (move color board)
  (declare (type chess-move move)
	   (type chess-board board)
	   (type small-fixnum color))
  (let* ((res nil)
	 (undo nil))
    (declare (type symbol res)
	     (type list undo))
    ;; new board
    (setq undo (domove move board))

    (when (incheckp color board)
      (setq res t))

    ;; restore original board
    (undo-move undo board)

    res))

;; update board for move
;; return list to undo move
(defun domove (move board)
  (declare (type chess-move move) (type chess-board board))
  (let* ((sq1 (square1 move))
	 (sq2 (square2 move))
	 (old-movelist nil)
	 (moremoves nil)		;save variables only when they change
	 (old-variables	nil)		;(save-variables)) 
         (piece (getpiece sq1 board))
	 (hor (- (squarex sq2) (squarex sq1)))
	 (ver (- (squarey sq2) (squarey sq1)))
	 (color (getcolor (getpiece sq1 board))))
    (declare (type chess-square sq1 sq2)
	     (type list old-movelist old-variables moremoves)
	     (type symbol piece)
	     (type small-fixnum hor ver color))
    ;;(setq old-variables (save-variables))
	  
    ;; normal move
    ;; save original setup
    (push (cons sq2 (getpiece sq2 board)) old-movelist)
    (push (cons sq1 (getpiece sq1 board)) old-movelist)
    
    (setpiecexy (squarex sq2) (squarey sq2) board
		piece)
    (setpiecexy (squarex sq1) (squarey sq1) board
		'empty)

    (cond
     ;; pawn promotion?
     ((and (equalp piece 'wp)
	   (= (squarey sq2) 7))
      (setpiecexy (squarex sq2) (squarey sq2) board (choosepiece *white*)))
    
     ((and (equalp piece 'bp)
	   (= (squarey sq2) 0))
      (setpiecexy (squarex sq2) (squarey sq2) board (choosepiece *black*)))

     ;; castle?
     ((and (equalp piece 'wk)
	   (equalp move (nth 0 white-castle)))
      (setq moremoves (domove '( (7 . 0) . (5 . 0) ) board))
      (setq old-variables (save-variables))
      (setq wcancastle (cons nil nil)))

     ((and (equalp piece 'wk)
	   (equalp move (nth 1 white-castle)))
      (setq moremoves (domove '( (0 . 0) . (3 . 0) ) board))
      (setq old-variables (save-variables))
      (setq wcancastle (cons nil nil)))

     ((and (equalp piece 'bk)
	   (equalp move (nth 0 black-castle)))
      (setq moremoves (domove '( (7 . 7) . (5 . 7) ) board))
      (setq old-variables (save-variables))
      (setq bcancastle (cons nil nil)))

     ((and (equalp piece 'bk)
	   (equalp move (nth 1 black-castle)))
      (setq moremoves (domove '( (0 . 7) . (3 . 7) ) board))
      (setq old-variables (save-variables))
      (setq bcancastle (cons nil nil)))


     ;; rules of castling
     ((equalp sq1 '(4 . 0))
      (setq old-variables (save-variables))
      (setq wcancastle (cons nil nil)))

     ((equalp sq1 '(7 . 0))
      (setq old-variables (save-variables))
      (setf (car wcancastle) nil))

     ((equalp sq1 '(0 . 0))
      (setq old-variables (save-variables))
      (setf (cdr wcancastle) nil))

     ((equalp sq1 '(4 . 7))
      (setq old-variables (save-variables))
      (setq bcancastle (cons nil nil)))

     ((equalp sq1 '(0 . 7))
      (setq old-variables (save-variables))
      (setf (car bcancastle) nil))

     ((equalp sq1 '(7 . 7))
      (setq old-variables (save-variables))
      (setf (cdr bcancastle) nil))

     ;; can opponent enpassante on next move?
     (benpassant
      (when (and (= -1 ver)
		 (or (= -1 hor) (= 1 hor))
		 (equalp (squarey sq2) 2)
		 (= color *black*)
		 (equalp (squarex sq2) benpassant))
	(push (cons (make-move (squarex sq2) (1- (squarey sq2))) 'wp) old-movelist)
	(setpiecexy (squarex sq2) (1+ (squarey sq2)) board 'empty ))
	
      (setq old-variables (save-variables))
      (setq benpassant nil));; only valid on next move

     (wenpassant
      (when (and (= 1 ver)
		 (or (= -1 hor) (= 1 hor))
		 (equalp (squarey sq2) 5)
		 (= color *white*)
		 (equalp (squarex sq2) wenpassant))
	(push (cons (make-move (squarex sq2) (1+ (squarey sq2))) 'bp) old-movelist)
	(setpiecexy (squarex sq2) (1- (squarey sq2)) board 'empty))
	
      (setq old-variables (save-variables))
      (setq wenpassant nil))
    
     ((and (equalp piece 'wp)
	   (= (- (squarey sq2) (squarey sq1)) 2))
      (setq old-variables (save-variables))
      (setq benpassant (squarex sq1)))

     ((and (equalp piece 'bp)
	   (= (- (squarey sq2) (squarey sq1)) -2))
     (setq old-variables (save-variables))
      (setq wenpassant (squarex sq1))))
    
    ;;(when (cdr moremoves)
    ;;  (restore-variables (cdr moremoves)))
    
    (dolist (item (car moremoves))
	    (declare (type chess-move item))
	    (push item old-movelist))
    
    (cons old-movelist old-variables)))

;; take back a move
(defun undo-move (undolist board)
  (declare (type list undolist)
	   (type chess-board board))
  (when (cdr undolist)
    (restore-variables (cdr undolist)))
  
  (dolist (item (car undolist))
	  (declare (type cons item))
	  (setpiece (car item) board (cdr item))))

;; choose piece for promotion
;; needs to be more robust
(defun choosepiece (color)
  (declare (type small-fixnum color))
  (cond
   ((and (car computer-controlled) (= color *white*)) 'WQ)
   ((and (cdr computer-controlled) (= color *black*)) 'BQ)
   (t
    (let (piece)
      (declare (type symbol piece))
      (format t "Q, R, B, N ? : ")
      (setq piece (read))
      (cond
       ((= color *white*)
	(cond
	 ((equalp piece 'Q) 'WQ)
	 ((equalp piece 'R) 'WR)
	 ((equalp piece 'B) 'WB)
	 ((equalp piece 'N) 'WN)
	 ))
       ((= color *black*)
	(cond
	 ((equalp piece 'Q) 'BQ)
	 ((equalp piece 'R) 'BR)
	 ((equalp piece 'B) 'BB)
	 ((equalp piece 'N) 'BN)
	 ))
       (t (format t  "uhhhh....")))))))
   
;; is color in check?
(defun incheckp (color board)
  (declare (type small-fixnum color)
	   (type chess-board board))
  (let ((king (nil-square))
	(res nil)
	(ksym (if (= color *white*) 'wk 'bk))
	(saved-turn turn))
    (declare (type chess-square king)
	     (type symbol ksym res)
	     (type small-fixnum saved-turn))
    
    (setq turn (- color))
    
    (setq king
	  (catch 'catch-king
	    (loopboard #'(lambda (x y)
			   (when (equalp (getpiecexy x y board) ksym)
			     (throw 'catch-king (make-square x y)))))))

    (catch 'got-em
      (dolist (location (locations (- color) board))
	      (declare (type chess-square location))
	      (when (validp-nocheck (make-move location king) board)
		(throw 'got-em (setq res t)))))
    
    (setq turn saved-turn)
    res))

;; is color in checkmate?
(defun checkmatep (color board)
  (declare (inline) (type small-fixnum color) (type chess-board board))
  (and (incheckp color board)
       (equalp (validmoves color board) nil)))

;; is color stalemated?
(defun stalematep (color board)
  (declare (inline)  (type small-fixnum color) (type chess-board board))
  (and (not (incheckp color board))
       (equalp (validmoves color board) nil)))
	     
;; apply function to all x and y combinations
(defun loopboard (thefunc)
  (declare (inline)
	   (type (function (small-fixnum small-fixnum)) thefunc))
  (do ((x 0 (+ x 1)))
      ((> x 7) nil)
      (declare (type small-fixnum x))
      (do ((y 0 (+ y 1)))
	  ((> y 7) nil)
	  (declare (type small-fixnum y))
	  (funcall thefunc x y))))

;; other way of doing it
(defmacro boardloop (function)
  `(do ((x 0 (+ x 1)))
       ((> x 7) nil)
       (declare (type small-fixnum x))
       (do ((y 0 (+ y 1)))
	   ((> y 7) nil)
	   (declare (type small-fixnum y))
	   ,function)))


;; how is color's material worth
(defun material (color board)
  (declare (inline) (type small-fixnum color) (type chess-board board))
  (reduce #'+ (pieces color board)
	  :key #'(lambda (x) (third (symbol-value x)))))

;; how many moves does color have available
(defun mobility (color board)
  (declare (inline)  (type small-fixnum color) (type chess-board board))
  (let ((thelist (validmoves color board)))
    (declare (type list thelist))
    (if (= color *white*)
	(length thelist)
      (- (length thelist)))))

;; evalute color's advantage 
(defun evalboard (color board)
  (declare  (type small-fixnum color) (type chess-board board))
  (let* ((mat 0)
	 (mob 0)
	 (adv 0)
	 (mw (material *white* board))
	 (mb (material *black* board))
	 (nw (mobility *white* board))
	 (nb (mobility *black* board))
	 (infow (reduce #'+ (pawn-info *white* board)))
	 (infob (reduce #'+ (pawn-info *black* board)))
	 (w5 (* 5 infow))
	 (b5 (* 5 infob))
	 )
    (declare (type small-fixnum mat mob adv mb mw nw nb
		   infow infob w5 b5))

    (setq mat (+ mw mb))
    (setq mob (+ nw nb))
    (setq adv (+ (* 15 mat) mob))
    
    (decf adv w5)
    (incf adv b5)

    
    (when (= color *black*) (setq adv (- adv)))
    
    (cond
     ;; putting other person in check is good
     ;;((incheckp (- color) board) (setq adv (+ adv 10)))

     ;; checkmateing other person is really good
     ((checkmatep (- color) board) (setq adv checkmate))

     ;; stalemate is good if we are behind
     ((and (stalematep color board) (< adv 0)) (setq adv stalemate)))

    adv))

;; computer's move
(defun compmove (color board)
  (declare (type small-fixnum color) (type chess-board board))
  (let ((res (nil-square)))
    (declare (type chess-move res))
    (format t "thinking...~%")

    (if (= color *white*)
	(setq res (player1 color board))
      (setq res (player2 color board)))
    
    (format t "done~%")
    res))
				       
;; how will board evaluate after move?
(defun evaluate-move (move color board)
  (declare  (type small-fixnum color) (type chess-board board)
	    (type chess-move move))
  (let* ((res 0)
	 (undo nil)
	 (piece (getpiece (square1 move) board)))
    (declare (type small-fixnum res)
	     (type list undo)
	     (type symbol piece))
    (setq undo (domove move board))
    (setq res (evalboard color board))
    (undo-move undo board)

    ;; dont move queen before castling
    (when (and (equalp piece 'wq)
	       (not (incheckp color board))
	       (car wcancastle))
      (decf res 50))

    ;; dont move queen before castling
    (when (and (equalp piece 'bq)
	       (not (incheckp color board))
	       (car bcancastle))
      (decf res 50))

    (when (and (= color *white*) (> (squarey (square2 move)) (squarey (square1 move))))
      (incf res 30))

    (when (and (= color *black*) (< (squarey (square2 move)) (squarey (square1 move))))
      (incf res 30))
    
    ;;(when (is-attacked (square2 move) (- color) board)
    ;;  (format t "moving to attacked square~%")
    ;;  (decf res (* 10 (abs (third (symbol-value piece))))))
    
    res))
  
;; convert move to algebraic form (e.g. "d2-d4")
(defun algebraic (move)
  (declare (type chess-move move))
  (let ((res "a0-a0")
	(sq1 (square1 move))
	(sq2 (square2 move)))
    (declare (type string res)
	     (type chess-square sq1 sq2))
    (setf (char res 0)
	  (character (+ (squarex sq1) (char-int #\a))))
    (setf (char res 1)
	  (character (+ (squarey sq1) (char-int #\1))))
    (setf (char res 3)
	  (character (+ (squarex sq2) (char-int #\a))))
    (setf (char res 4)
	  (character (+ (squarey sq2) (char-int #\1))))
    res))

;; let computer play itself
(defun demogame ()
  (initboard)
  (setq computer-controlled (cons t t))
  (newgame))

;; return list of all squares attacked by color
(defun attacked (color board)
  (declare  (type small-fixnum color) (type chess-board board))
  (let ((attacked-squares nil)
	(saved-turn turn)
	(loc (nil-square)))
    (declare (type list attacked-squares)
	     (type small-fixnum saved-turn)
	     (type chess-square loc))
    (setq turn color)

    (loopboard
     #'(lambda (x y)
	 (setq loc (make-square x y))
	 (when (is-attacked loc color board)
	   (push loc attacked-squares))))
    
    (setq turn saved-turn)

    attacked-squares))

;; is location attacked by color
(defun is-attacked (loc color board)
  (declare (type chess-square loc)
	   (type small-fixnum color)
	   (type chess-board board))
  (let ((saved-piece nil)
	(res nil)
	(saved-turn turn)
	(testmove (empty-move)))
    (declare (type small-fixnum saved-turn)
	     (type symbol res)
	     (type symbol saved-piece)
	     (type chess-move testmove))
	      
    (setq turn color)
    (setq saved-piece (getpiece loc board))
    (setpiece loc board (if (= color *white*) 'bp 'wp))

    (catch 'done
      (dolist (location (locations color board))
	      (declare (type chess-square location))
	      (setq testmove (make-move location loc))
	      (when (validp testmove board)
		(throw 'done (setq res t)))))
    
    (setpiece loc board saved-piece)
    (setq turn saved-turn)
    res))



;; return list of all color's pieces
(defun pieces (color board)
 (declare (type small-fixnum color) (type chess-board board))
 (let ((pieces nil)
       (piece nil))
   (declare (type list pieces )
	    (type symbol piece))
   (loopboard
    #'(lambda (x y)
	(setq piece (getpiecexy x y board))
	(when (= (getcolor piece) color)
	  (push piece pieces))))
   pieces))

;; return list of location of all color's pieces
(defun locations (color board)
  (declare (type small-fixnum color)
	   (type chess-board board))
  (let ((locations nil))
    (declare (type list locations))
    (loopboard
     #'(lambda (x y)
	 (when (= (getcolor (getpiecexy x y board)) color)
	   (push (make-square x y) locations))))
    locations))

;; generate moves for pieces
(defun pawn-moves (loc board)
  (declare (type chess-square loc) (type chess-board board))
  (let* ((color (getcolor (getpiece loc board)))
	 (direction color)
	 (x (squarex loc))
	 (y (squarey loc))
	 (movelist nil)
	 (start (if (= color *white*) 1 6)))
    (declare (type small-fixnum color direction x y start)
	     (type list movelist))

    (when (equalp (getpiecexy x (+ y direction) board) 'empty)
      (push (make-move loc (make-square x (+ y direction))) movelist))

    (when (and (equalp (getpiecexy x (+ (* 2 direction) y) board) 'empty)
	       (= y start))
      (push (make-move loc (make-square x (+ y (* 2 direction)))) movelist))

    (push
     (make-move loc (make-square (+ x 1) (+ y direction))) movelist)

    (push
     (make-move loc (make-square (- x 1) (+ y direction))) movelist)

    movelist))
    
(defun knight-moves (loc board)
  (declare (ignore board) (type chess-square loc))
  (let ((x (squarex loc)) (y (squarey loc)))
    (declare (type small-fixnum y x))
    (list
     (make-move loc (make-square (+ x 1) (+ y 2)))
     (make-move loc (make-square (- x 1) (+ y 2)))
     (make-move loc (make-square (+ x 2) (+ y 1)))
     (make-move loc (make-square (- x 2) (+ y 1)))
     (make-move loc (make-square (+ x 1) (- y 2)))
     (make-move loc (make-square (- x 1) (- y 2)))
     (make-move loc (make-square (+ x 2) (- y 1)))
     (make-move loc (make-square (- x 2) (- y 1)))
     )))

    
(defun bishop-moves (loc board)
  (declare (type chess-square loc) (type chess-board board))
  (let ((movelist nil)
	(res nil)
	(x (squarex loc)) (y (squarey loc))
	(color (getcolor (getpiece loc board))))
    (declare (type list res)
	     (type small-fixnum x y color)
	     (type list movelist))
    (catch 'bishop1
      (do* ((x (+ x 1) (+ x 1))
	    (y (+ y 1) (+ y 1))
	    (loc (make-square x y) (make-square x y)))
	   ((offboardp loc) movelist)
	   (declare (type small-fixnum x y)
		    (type chess-square loc))
	   (cond
	    ((=  (getcolor (getpiece loc board)) color)
	     (throw 'bishop1 movelist))
	    ((=  (getcolor (getpiece loc board)) (- color))
	     (push loc movelist)
	     (throw 'bishop1 movelist))
	    ((= (getcolor (getpiece loc board)) 0)
	     (push loc movelist)))))
    
    (catch 'bishop2
      (do* ((x (- x 1) (- x 1))
	    (y (+ y 1) (+ y 1))
	    (loc (make-square x y) (make-square x y)))
	   ((offboardp loc) movelist)
	   (declare (type small-fixnum x y)
		    (type chess-square loc))
	   (cond
	    ((=  (getcolor (getpiece loc board)) color)
	     (throw 'bishop2 movelist))
	    ((=  (getcolor (getpiece loc board)) (- color))
	     (push loc movelist)
	     (throw 'bishop2 movelist))
	    ((= (getcolor (getpiece loc board)) 0)
	     (push loc movelist)))))

    (catch 'bishop3
      (do* ((x (+ x 1) (+ x 1))
	    (y (- y 1) (- y 1))
	    (loc (make-square x y) (make-square x y)))
	   ((offboardp loc) movelist)
	   (declare (type small-fixnum x y)
		    (type chess-square loc))
	   (cond
	    ((=  (getcolor (getpiece loc board)) color)
	     (throw 'bishop3 movelist))
	    ((=  (getcolor (getpiece loc board)) (- color))
	     (push loc movelist)
	     (throw 'bishop3 movelist))
	    ((= (getcolor (getpiece loc board)) 0)
	     (push loc movelist)))))

    (catch 'bishop4
      (do* ((x (- x 1) (- x 1))
	    (y (- y 1) (- y 1))
	    (loc (make-square x y) (make-square x y)))
	   ((offboardp loc) movelist)
	   (declare (type small-fixnum x y)
		    (type chess-square loc))
	   (cond
	    ((=  (getcolor (getpiece loc board)) color)
	     (throw 'bishop4 movelist))
	    ((=  (getcolor (getpiece loc board)) (- color))
	     (push loc movelist)
	     (throw 'bishop4 movelist))
	    ((= (getcolor (getpiece loc board)) 0)
	     (push loc movelist)))))
    
    (dolist (square movelist)
	    (declare (type chess-square square))
	    (push (make-move loc square) res))
    res))

(defun rook-moves (loc board)
  (declare (type chess-square loc) (type chess-board board))
  (let ((movelist nil)
	(res nil)
	(x (squarex loc)) (y (squarey loc))
	(color (getcolor (getpiece loc board))))
    (declare (type list res)
	     (type small-fixnum x y color)
	     (type list movelist))
    
    (catch 'rook1
      (do* ((x (+ x 1) (+ x 1))
	    (y y)
	    (loc (make-square x y) (make-square x y)))
	   ((offboardp loc) movelist)
	   (declare (type small-fixnum x y)
		    (type chess-square loc))
	   (cond
	    ((=  (getcolor (getpiece loc board)) color)
	     (throw 'rook1 movelist))
	    ((=  (getcolor (getpiece loc board)) (- color))
	     (push loc movelist)
	     (throw 'rook1 movelist))
	    ((= (getcolor (getpiece loc board)) 0)
	     (push loc movelist)))))
    
    (catch 'rook2
      (do* ((x (- x 1) (- x 1))
	    (y y)
	    (loc (make-square x y) (make-square x y)))
	   ((offboardp loc) movelist)
	   (declare (type small-fixnum x y)
		    (type chess-square loc))
	   (cond
	    ((=  (getcolor (getpiece loc board)) color)
	     (throw 'rook2 movelist))
	    ((=  (getcolor (getpiece loc board)) (- color))
	     (push loc movelist)
	     (throw 'rook2 movelist))
	    ((= (getcolor (getpiece loc board)) 0)
	     (push loc movelist)))))

    (catch 'rook3
      (do* ((x x)
	    (y (- y 1) (- y 1))
	    (loc (make-square x y) (make-square x y)))
	   ((offboardp loc) movelist)
	   (declare (type small-fixnum x y)
		    (type chess-square loc))
	   (cond
	    ((=  (getcolor (getpiece loc board)) color)
	     (throw 'rook3 movelist))
	    ((=  (getcolor (getpiece loc board)) (- color))
	     (push loc movelist)
	     (throw 'rook3 movelist))
	    ((= (getcolor (getpiece loc board)) 0)
	     (push loc movelist)))))

    (catch 'rook4
      (do* ((x x)
	    (y (+ y 1) (+ y 1))
	    (loc (make-square x y) (make-square x y)))
	   ((offboardp loc) movelist)
	   (declare (type small-fixnum x y)
		    (type chess-square loc))
	   (cond
	    ((=  (getcolor (getpiece loc board)) color)
	     (throw 'rook4 movelist))
	    ((=  (getcolor (getpiece loc board)) (- color))
	     (push loc movelist)
	     (throw 'rook4 movelist))
	    ((= (getcolor (getpiece loc board)) 0)
	     (push loc movelist)))))

    (dolist (square movelist)
	    (declare (type chess-square square))
	    (push (make-move loc square) res))
    res))

(defun queen-moves (loc board)
  (declare (type chess-square loc) (type chess-board board))
  (union (bishop-moves loc board)
	 (rook-moves loc board)))

(defun king-moves (loc board)
  (declare (ignore board) (type chess-square loc))
  (let* ((x (squarex loc))
	 (y (squarey loc))
	 (movelist nil))
    (declare (type small-fixnum x y)
	     (type list movelist))
    (setq movelist
	  (list
	   (make-move loc (make-square (+ x  1) (+ y 1)))
	   (make-move loc (make-square (+ x -1) (+ y 1)))
	   (make-move loc (make-square (+ x  0) (+ y 1)))
	   (make-move loc (make-square (+ x  1) (+ y 0)))
	   (make-move loc (make-square (+ x -1) (+ y 0)))
	   (make-move loc (make-square (+ x  1) (+ y -1)))
	   (make-move loc (make-square (+ x -1) (+ y -1)))
	   (make-move loc (make-square (+ x  0) (+ y -1)))))

    (when (equalp loc (squarex (first white-castle)))
      (setq movelist (union movelist white-castle)))

    (when (equalp loc (squarex (first black-castle)))
      (setq movelist (union movelist black-castle)))
    
    movelist))
  
(defun validmoves (color board)
  (declare (type small-fixnum color) (type chess-board board))

  (let ((movelist nil)
	(piece nil)
	(saved-turn turn))
    (declare (type list movelist)
	     (type list piece)
	     (type small-fixnum saved-turn))
    
    (setq turn color)

    (dolist (loc (locations color board))
	    (declare (type chess-square loc))
	    (setq piece (symbol-value (getpiece loc board)))
	    (dolist (move (funcall (fourth piece) loc board))
		    (declare (type chess-move move))
		    (cond
		     ;; if off board do nothing
		     ((offboardp (square2 move)) nil)
		     ;; run thru validp
		     ((or (equalp piece wk)
			  (equalp piece bk)
			  (equalp piece wp)
			  (equalp piece bp))
		      (when (validp move board)
			(push move movelist)))
		     ;; just make sure not taking own piece
		     ;; and not getting into check
		     (t
		      (when (and (not (check-checker move color board))
				 (not (= color (getcolor
						(getpiece (square2 move) board)))))
			(push move movelist))))))
    
    (setq turn saved-turn)
    movelist))
    
;; relative value of a square   
(defun location-value (x y)
  (declare (type integer x y))
  (let* ((yv (if (<= y 3) (1+ y) (- 8 y)))
	 (xv (if (<= x 3) (1+ x) (- 8 x))))
    (declare (type small-fixnum yv xv))
    (min yv xv)))

;; how many pawns at each x position
(defun pawn-structure (color board)
  (declare (type small-fixnum color) (type chess-board board))
  (let ((struct (list 0 0 0 0 0 0 0 0))
	(pawn (if (= color *white*) 'wp 'bp)))
    (declare (type list struct)
	     (type symbol pawn))
    (loopboard
     #'(lambda (x y)
	 (when (equalp (getpiecexy x y board) pawn)
	   (incf (nth x struct)))))
    struct))

;; how many isolated, doubled, and unmoved pawns 
(defun pawn-info (color board)
  (declare (type small-fixnum color) (type chess-board board))
  (let ((isolated 0)
	(doubled 0)
	(unmoved 0)
	(where -1)
	(struct (pawn-structure color board)))
    (declare (type small-fixnum isolated doubled unmoved where)
	     (type list struct))
    (cond
     ((equalp color *white*)
      (loopboard
       #'(lambda (x y)
	   (when (and
		  (equalp (getpiecexy x y board) 'wp)
		  (= y 1))
	     (incf unmoved)))))
     
     ((equalp color *black*)
      (loopboard
       #'(lambda (x y)
	   (when (and
		  (equalp (getpiecexy x y board) 'bp)
		  (= y 6))
	     (incf unmoved))))))
      
    (dolist (count struct)
	    (declare (type small-fixnum count))
	    (setq where (1+ where))
	    (cond
	     ((= where 0)
	      (when (and (> count 0)
			 (= (nth (1+ where) struct) 0))
		(incf isolated)))
	     ((= where 7)
	      (when (and (> count 0)
			 (= (nth (1- where) struct) 0))
		(incf isolated)))
	     ((and
	       (> count 0)
	       (= (nth (1- where) struct) 0)
	       (= (nth (1+ where) struct) 0))
	      (incf isolated)))
	    
	    (when (> count 1)
	      (incf doubled (- count 1))))
    
    (list isolated doubled unmoved)))

;; return list of saved variables
(defun save-variables ()
  (declare (inline))
  (list
   (copy-list wcancastle)
   (copy-list bcancastle)
   wenpassant 
   benpassant 
   turn
   ))
  
;; restore variables from list
(defun restore-variables (v-list)
  (declare (inline) (type list v-list))
  (setq wcancastle  (nth 0 v-list))
  (setq bcancastle  (nth 1 v-list))
  (setq wenpassant  (nth 2 v-list))
  (setq benpassant  (nth 3 v-list))
  (setq turn        (nth 4 v-list))
  "restored")




;; get a move
(defun player1 (color board)
  (declare (type small-fixnum color) (type chess-board board))
  (let ((move (empty-move)))
    (declare (type chess-move move))
    
;;    (cond
;;     ((> 15 (mobility color board))
    (findbest color board 2 move -20000 20000)
;;     (t 
;;      (findbest color board 2 move -20000 20000)

    (format t "~%move = ~a~%" move)
    ;;(when (equalp move (empty-move))
    ;;  (format t "game over~%")
    ;;  (game-over-p board))
    move))


;; todo weight moves as to how far in the future they are...
(defun findbest (color board depth bestmove alpha beta)
  (declare (type small-fixnum color)
	   (type chess-board board)
	   (type small-fixnum depth alpha beta)
	   (type chess-move bestmove))

  ;;(format t "called with move = ~a~%" bestmove)
  ;;(force-output)
  
  (let ((adv 0)
	(undo nil)
	(opp (- color))
	(reply 0)
	(omove (empty-move))
	(result nil))

    (declare (type small-fixnum adv opp reply)
	     (type list undo)
	     (type (or small-fixnum null) result)
	     (type chess-move omove))
    
    (setq adv (evalboard color board))
    
    (cond
     ((= 0 depth) adv)
     ((> adv 100) adv)
     (t
      (if (= color *white*)
	  (setq adv alpha)
	(setq adv beta))

      (setq result
	    (dolist (move
		     (sort
		      (validmoves color board)
		      #'(lambda (x y)
			  (> (location-value (caar x) (cdar x))
			     (location-value (caar y) (cdar y))))))
		    (declare (type chess-move move))

		    (setq undo (domove move board))

		    (setq reply
			  (findbest opp board (- depth 1) omove alpha beta))
	      
		    (undo-move undo board)
	      
		    (when
			(or (and (= color *white*)
				 (> reply adv))
			    (and (= color *black*)
				 (< reply adv)))
		      (cond
		       ((= color *white*)
			(setq adv reply)
			(setq alpha adv))
		       (t
			(setq adv reply)
			(setq beta adv)))
		
		      (format t ".") (force-output)

		      (setf (square1 bestmove) (square1 move))
		      (setf (square2 bestmove) (square2 move))

		      (when (>= alpha beta)
			(return adv)))))

      (when (null result)
	(setq result adv))
      result))))
		  
		  
		  
		
    

;; get a move
(defun player2 (color board)
  (declare (type small-fixnum color) (type chess-board board))
  (let ((movelist (validmoves color board))
	(best -20000)
	(value 0)
	(bestmove (cons nil nil))
	(piece nil))

    (declare (type list movelist)
	     (type small-fixnum value best)
	     (type chess-move bestmove)
	     (type symbol piece))
	     
    
    (when (equal movelist nil)
      (cond
       ((checkmatep color board)
	(format t "checkmated~%"))
       ((stalematep color board)
	(format t "stalemated~%"))))

    
    
    (catch 'goodmove

      (dolist (move movelist)
	      (declare (type chess-move move))
	      (setq piece (getpiece (square1 move) board))

	      ;; castle as soon as possible
	      (when (and (equalp piece 'wk)
			 (find move white-castle :test #'equalp))
		(throw 'goodmove (setq bestmove move)))

	      ;; castle if possible
	      (when (and (equalp piece 'bk)
			 (find move white-castle :test #'equalp))
		(throw 'goodmove (setq bestmove move)))

	      (setq value
		    (if (= color *white*)
			(evaluate-move move color board)
		      (evaluate-move move color board)))
		    

	      ;(format t "~a = ~a~%" move value)
	      
	      (when (> value best)
		(setq best value)
		(setq bestmove move))))

    bestmove))

(defun showmoves (color board)
  (let (u)
    (declare (type list u))
    (dolist (move (validmoves color board))
	    (setq u (domove move board))
	    (printboard board)
	    (undo-move u board))))

;; new stuff eh...

;(defmacro test (form)
;  `(do ((x 0 (+ x 1)))
;      ((> x 10) nil)
;      ,form
;      ))

;(defun attacked2 (color board)
;  (declare (inline)
;	   (type small-fixnum color)
;	   (type chess-board board))
;  (map 'list #'cdr (validmoves color board)))

     
;(defun test1 ()
;  (do ((z 0 (+ z 1)))
;      ((> z 1000) nil)
;      (attacked 1 *board*)))

;(defun test2 ()
;  (do ((z 0 (+ z 1)))
;      ((> z 1000) nil)
;      (attacked2 1 *board*)))

;;(defun possible ()
;;  (declare (inline))
;;  (let ((res nil))
;;    (do ((x 0 (+ x 1)))
;;	((> x 7) nil)
;;	(do ((y 0 (+ y 1)))
;;	    ((> y 7) nil)
;;	    (push (make-square x y) res)))
;;    res))


;;(defmacro make-move (sq1 sq2)
;;  `(cons ,sq1 ,sq2))

;;(defmacro square1 (move)
;;  `(car ,move))

;;(defmacro square2 (move)
;;  `(cdr ,move))

;;;; functions for dealing with squares
;;(defmacro make-square (x y)
;;  `(cons ,x ,y))

;;(defmacro squarex (square)
;;  `(the small-fixnum (car ,square)))

;;(defmacro squarey (square)
;;  `(the small-fixnum (cdr ,square)))
;;;; functions for dealing with moves
;;(defmacro make-move (sq1 sq2)
;;  `(cons ,sq1 ,sq2))

;;(defmacro square1 (move)
;;  `(car ,move))

;;(defmacro square2 (move)
;;  `(cdr ,move))


;; print the board
;(defun printboard (board)
;  (declare (type chess-board board))
;  (format t "    a b c d e f g h  ~%")
;  (format t "  +-----------------+~%")
;  (do ((x 7 (- x 1)))
;      ((< x 0) nil)
;      (declare (type small-fixnum x))
;      (format t "~a | " (1+ x))
;      (do ((y 0 (+ y 1)))
;	  ((> y 7) nil)
;	  (declare (type small-fixnum y))
;	  (format t "~a "
;		  (car (symbol-value (getpiecexy y x board)))))
;      (format t "| ~a~%" (1+ x)))
;  (format t "  +-----------------+~%")
;  (format t "    a b c d e f g h  ~%"))

;; how will board evaluate after move?
;;(defun evaluate-move2 (move color board)
;;  (declare (type chess-move move) (type small-fixnum color) (type chess-board board))
;;  (let* ((res 0)
;;	 (undo nil)
;;	 (piece (getpiece (square1 move) board)))
;;    (declare (type small-fixnum res)
;;	     (type list undo)
;;	     (type symbol piece))
;;    (setq undo (domove move board))
;;    (setq res (evalboard2 color board))
;;    (undo-move undo board)

;;    ;; dont move queen before castling
;;    (when (and (equalp piece 'wq)
;;	       (car wcancastle))
;;      (decf res 50))

;;    ;; dont move queen before castling
;;    (when (and (equalp piece 'bq)
;;	       (car bcancastle))
;;      (decf res 50))
    
;;    res))

;; evalute color's advantage 
;;(defun evalboard2 (color board)
;;  (declare (type small-fixnum color) (type chess-board board))
;;  (let* ((mat (+ (material *white* board)
;;		 (material *black* board)))
;;	 (mob (+ (mobility *white* board)
;;		 (mobility *black* board)))
;;	 (adv (+ (* 10 mat) mob)))    
;;    (declare (type small-fixnum mat mob adv))

;;    (decf adv (the small-fixnum (* 5 (reduce #'+ (pawn-info *white* board)))))
;;    (incf adv (the small-fixnum (* 5 (reduce #'+ (pawn-info *black* board)))))

;;    (when (= color *black*) (setq adv (- adv)))
    
;;    (cond
;;     ;; putting other person in check is good
;;     ;;((incheckp (- color) board) (setq adv (+ adv 10)))

;;     ;; checkmateing other person is really good
;;     ((checkmatep (- color) board) (setq adv checkmate))

;;     ;; stalemate is good if we are behind
;;     ((and (stalematep color board) (< adv 0)) (setq adv stalemate)))

;;    adv))

