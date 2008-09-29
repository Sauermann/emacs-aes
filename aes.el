;;; aes.el --- Implementation of aes in minlog

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; AES



(defun aes-ds (x)
  "Return the string in its hexadecimal representation."
  (let ((res ""))
    (dotimes (i (length x))
      (setq res (concat res
                        (format "%02x" (aref x i)))))
    res))

(defun aes-mul-pre (a b)
  "Multiplication for bytes in GF2."
  (let ((p 0))
    (dotimes (c 8)
      (if (= 1 (logand b 1)) (setq p (logxor a p)))
      (if (prog1 (= #x80 (logand a #x80))
            (setq a (logand #xff (lsh a 1))))
          (setq a (logxor a #x1b)))
      (setq b (lsh b -1)))
    p))

(defconst aes-Mul-Table
  (let ((l (make-string 256 0))
        (mt (make-vector 256 0)))
    (dotimes (i 256)
      (aset mt i (make-string 256 0)))
    (dotimes (x 256)
      (if (< 0 x)
          (let ((i x))
            (while (< i 256)
              (let ((res (aes-mul-pre i x)))
                (if (= #x01 res)
                    (progn (aset l x i)
                           (aset l i x)))
                (aset (aref mt x) i res)
                (aset (aref mt i) x res))
              (setq i (+ i 1))))))
    (cons l mt))
  "Inverse")

(defconst aes-l2 (aref (cdr aes-Mul-Table) #x02))
(defconst aes-l3 (aref (cdr aes-Mul-Table) #x03))
(defconst aes-le (aref (cdr aes-Mul-Table) #x0e))
(defconst aes-lb (aref (cdr aes-Mul-Table) #x0b))
(defconst aes-ld (aref (cdr aes-Mul-Table) #x0d))
(defconst aes-l9 (aref (cdr aes-Mul-Table) #x09))

(defun aes-Mul-Inv (x)
  "Calculate inverse element of aes-multiplication."
  (aref (car aes-Mul-Table) x))

(defun aes-Mul (x y)
  (aref (aref (cdr aes-Mul-Table) x) y))

(defconst aes-S-boxes
  (let ((l1 (make-string 256 0))
        (l2 (make-string 256 0)))
    (dotimes (x 256)
      (let ((b (aes-Mul-Inv x))
            (g 0)
            (c #x63))
        (dotimes (i 8)
          (setq
           g
           (logxor (lsh (logand (logxor
                                 (lsh (logxor b c) (- i))
                                 (lsh b (- (% (+ i 4) 8)))
                                 (lsh b (- (% (+ i 5) 8)))
                                 (lsh b (- (% (+ i 6) 8)))
                                 (lsh b (- (% (+ i 7) 8))))
                                1)
                        i)
                   g)))
        (aset l1 x g)
        (aset l2 g x)))
    (cons l1 l2))
  "Contains lookup tables S-boxes.
It is a pair where the car-value contains the S-box used for encryption and
the cdr-value contains the S-box used for decryption.
The S-boxes are stored as strings of length 256.")

(defun aes-SubBytes (x)
  "Apply the encryption S-box to each byte of the string X."
  (let ((l (length x)))
    (dotimes (i l) (aset x i (aref (car aes-S-boxes) (aref x i))))))
(defun aes-InvSubBytes (x)
  "Apply the decryption S-box to each byte of the string X."
  (let ((l (length x)))
    (dotimes (i l) (aset x i (aref (cdr aes-S-boxes) (aref x i))))))

;; (let ((s "")) (dotimes (i 256) (setq s (concat s (make-string 1 i)))) (aes-SubBytes s) (aes-InvSubBytes s) s)


(defun aes-ShiftRows (state Nb)
  "Apply the shift rows transformation to state."
  (let ((x (aref state 1)) (c 1))
    (while (< c (lsh (- Nb 1) 2))
      (aset state c (aref state (+ c 4)))  (setq c (+ c 4)))
    (aset state c x))
  (let ((x (aref state 2)) (y (aref state 6)) (c 2))
    (while (< c (lsh (- Nb 2) 2)) (aset state c (aref state (+ c 8)))
           (setq c (+ c 4)))
    (aset state c x) (aset state (+ c 4) y))
  (let ((x (aref state 3)) (y (aref state 7)) (z (aref state 11)) (c 3))
    (while (< c (lsh (- Nb 3) 2)) (aset state c (aref state (+ c 12)))
           (setq c (+ c 4)))
    (aset state c x) (aset state (+ c 4) y) (aset state (+ c 8) z)))

(defun aes-InvShiftRows (state Nb)
  "Apply the inverted shift rows transformation to state."
  (let* ((c (- (lsh Nb 2) 3)) (x (aref state c)))
    (while (< 4 c) (aset state c (aref state (- c 4))) (setq c (- c 4)))
    (aset state c x))
  (let* ((c (- (lsh Nb 2) 2)) (x (aref state c)) (y (aref state (- c 4))))
    (while (< 8 c) (aset state c (aref state (- c 8))) (setq c (- c 4)))
    (aset state c x) (aset state (- c 4) y))
  (let* ((c (- (lsh Nb 2) 1))
         (x (aref state c)) (y (aref state (- c 4))) (z (aref state (- c 8))))
    (while (< 12 c) (aset state c (aref state (- c 12))) (setq c (- c 4)))
    (aset state c x) (aset state (- c 4) y) (aset state (- c 8) z)))

(defun aes-MixColumns (state Nb)
  "Apply the mix columns transformation to state."
  (dotimes (x Nb)
    (let ((s0 (aref state (lsh x 2)))
          (s1 (aref state (+ (lsh x 2) 1)))
          (s2 (aref state (+ (lsh x 2) 2)))
          (s3 (aref state (+ (lsh x 2) 3))))
      (aset state (lsh x 2) (logxor (aref aes-l2 s0) (aref aes-l3 s1) s2 s3))
      (aset state (+ 1 (lsh x 2))
            (logxor s0 (aref aes-l2 s1) (aref aes-l3 s2) s3))
      (aset state (+ 2 (lsh x 2))
            (logxor s0 s1 (aref aes-l2 s2) (aref aes-l3 s3)))
      (aset state (+ 3 (lsh x 2))
            (logxor (aref aes-l3 s0) s1 s2 (aref aes-l2 s3))))))

(defun aes-InvMixColumns (state Nb)
  "Apply the inverse mix columns transformation to state."
  (dotimes (x Nb)
    (let ((s3 (aref state (+ (lsh x 2) 3))) (s2 (aref state (+ (lsh x 2) 2)))
          (s1 (aref state (+ (lsh x 2) 1))) (s0 (aref state (lsh x 2))))
      (aset state (lsh x 2) (logxor (aref aes-le s0) (aref aes-lb s1)
                                    (aref aes-ld s2) (aref aes-l9 s3)))
      (aset state (+ 1 (lsh x 2)) (logxor (aref aes-l9 s0) (aref aes-le s1)
                                          (aref aes-lb s2) (aref aes-ld s3)))
      (aset state (+ 2 (lsh x 2)) (logxor (aref aes-ld s0) (aref aes-l9 s1)
                                          (aref aes-le s2) (aref aes-lb s3)))
      (aset state (+ 3 (lsh x 2)) (logxor (aref aes-lb s0) (aref aes-ld s1)
                                          (aref aes-l9 s2) (aref aes-le s3))))))

(defun aes-SubShiftMix (state Nb)
  "Apply the transformations SubBytes, ShiftRows and mix columns to state."
  (let* ((l (length state))
         (copy (copy-sequence state)))
    (dotimes (x Nb)
      (let ((s0 (aref (car aes-S-boxes) (aref copy (lsh x 2))))
            (s1 (aref (car aes-S-boxes) (aref copy (% (+ (lsh x 2) 1 4) l))))
            (s2 (aref (car aes-S-boxes) (aref copy (% (+ (lsh x 2) 2 8) l))))
            (s3 (aref (car aes-S-boxes) (aref copy (% (+ (lsh x 2) 3 12) l))))
            )
        (aset state (lsh x 2) (logxor (aref aes-l2 s0) (aref aes-l3 s1) s2 s3))
        (aset state (+ 1 (lsh x 2))
              (logxor s0 (aref aes-l2 s1) (aref aes-l3 s2) s3))
        (aset state (+ 2 (lsh x 2))
              (logxor s0 s1 (aref aes-l2 s2) (aref aes-l3 s3)))
        (aset state (+ 3 (lsh x 2))
              (logxor (aref aes-l3 s0) s1 s2 (aref aes-l2 s3)))))))

(defun aes-InvSubShiftMix (state Nb)
  "Apply the 3 inverted transformations to state."
  (let* ((l (length state))
         (copy (copy-sequence state)))
    (dotimes (x Nb)
      (let ((s0 (aref copy (lsh x 2)))
            (s1 (aref copy (+ (lsh x 2) 1)))
            (s2 (aref copy (+ (lsh x 2) 2)))
            (s3 (aref copy (+ (lsh x 2) 3))))
        (aset state (lsh x 2)
              (aref (cdr aes-S-boxes)
                    (logxor (aref aes-le s0) (aref aes-lb s1)
                            (aref aes-ld s2) (aref aes-l9 s3))))
        (aset state (mod (+ 1 4 (lsh x 2)) l)
              (aref (cdr aes-S-boxes)
                    (logxor (aref aes-l9 s0) (aref aes-le s1)
                            (aref aes-lb s2) (aref aes-ld s3))))
        (aset state (mod (+ 2 8 (lsh x 2)) l)
              (aref (cdr aes-S-boxes)
                    (logxor (aref aes-ld s0) (aref aes-l9 s1)
                            (aref aes-le s2) (aref aes-lb s3))))
        (aset state (mod (+ 3 12 (lsh x 2)) l)
              (aref (cdr aes-S-boxes)
                    (logxor (aref aes-lb s0) (aref aes-ld s1)
                            (aref aes-l9 s2) (aref aes-le s3))))))))

;; (let (( s (concat [#x63 #x53 #xe0 #x8c #x09 #x60 #xe1 #x04 #xcd #x70 #xb7 #x51 #xba #xca #xd0 #xe7])))
;;   (aes-MixColumns s Nb)
;;   (aes-InvMixColumns s Nb)
;;   (aes-ds s))

(defun aes-SubWord (x)
  "Apply the encryption S-box to all 4 bytes of the string X."
  (dotimes (i 4) (aset x i (aref (car aes-S-boxes) (aref x i)))))
(defun aes-InvSubWord (x)
  "Apply the decryption S-box to all 4 bytes of the string X."
  (dotimes (i 4) (aset x i (aref (cdr aes-S-boxes) (aref x i)))))

(defun aes-xor (x y)
  "Return X and Y bytewise xored as string."
  (let* ((l (length x)) (res (make-string l 0)))
    (dotimes (i l)
      (aset res i (logxor (aref x i) (aref y i))))
    res))

(defun aes-RotWord (x)
  "Rotate X by one byte.
Append the first byte to the end."
  (store-substring x 0 (concat (substring x 1 4) (substring x 0 1))))

(defun aes-message (x)
  (with-current-buffer "*scratch*"
    (insert x "\n")))

(defun aes-KeyExpansion (key Nb)
  "Return a string, which contains the Key expansion of KEY."
  (let* ((Nk (lsh (length key) -2))
         (Nr (+ Nk 6))
         (w (make-string (* 4 Nb (+ Nr 1)) 0))
         (i (lsh Nk 2))
         (rcon (concat (make-string 1 1) (make-string 3 0)))
         (Nk2 (lsh Nk 2)))
    (store-substring w 0 key)
    (while (< i (lsh (* Nb (+ Nr 1)) 2))
      (let ((temp (substring w (- i 4) i)))
        (if (= 0 (% i Nk2))
            (progn (aes-RotWord temp)
;;                   (aes-message (concat "temp.r=" (aes-ds temp)))
                   (aes-SubWord temp)
;;                   (aes-message (concat "temp.s=" (aes-ds temp)))
;;                   (aes-message (concat "rcon  =" (aes-ds rcon)))
                   (setq temp (aes-xor temp rcon))
;;                   (aes-message (concat "temp.x=" (aes-ds temp)))
                   (aset rcon 0 (aes-Mul (aref rcon 0) 2)))
;;          (aes-message (concat (number-to-string Nk) " "
;;                               (number-to-string (% (lsh i -2) Nk))))
          (if (and (< 6 Nk) (= (% (lsh i -2) Nk) 4))
              (aes-SubWord temp)))
;;        (aes-message (concat "temp.e=" (aes-ds temp)))
        (store-substring
         w i (aes-xor (substring w (- i Nk2) (+ 4 (- i Nk2))) temp)))
      (setq i (+ i 4)))
    w))

;; (aes-ds (aes-KeyExpansion (concat [#x60 #x3d #xeb #x10 #x15 #xca #x71 #xbe #x2b #x73 #xae #xf0 #x85 #x7d #x77 #x81 #x1f #x35 #x2c #x07 #x3b #x61 #x08 #xd7 #x2d #x98 #x10 #xa3 #x09 #x14 #xdf #xf4]) Nb))
;; (aes-ds (aes-KeyExpansion (concat [#x8e #x73 #xb0 #xf7 #xda #x0e #x64 #x52 #xc8 #x10 #xf3 #x2b #x80 #x90 #x79 #xe5 #x62 #xf8 #xea #xd2 #x52 #x2c #x6b #x7b]) Nb))
;; (aes-ds (aes-KeyExpansion (concat [#x2b #x7e #x15 #x16 #x28 #xae #xd2 #xa6 #xab #xf7 #x15 #x88 #x09 #xcf #x4f #x3c]) Nb))


(defun aes-AddRoundKey (state keys r Nb)
  "Add the keys specified  by R and NB of KEYS to STATE."
  (dotimes (i (lsh Nb 2))
    (aset state i (logxor (aref state i)
                          (aref keys (+ (lsh (* r Nb) 2) i))))))

(defun aes-Cipher-reference (input keys Nb)
  "Perform the AES encryption."
  (let* ((Nk (- (/ (lsh (length keys) -2) Nb) 7))
         (state (make-string (lsh Nb 2) 0))
         (Nr (+ Nk 6))
         (r 1))
    (store-substring state 0 input)
    (aes-AddRoundKey state keys 0 Nb)
    (while (< r Nr)
      (aes-SubBytes state)
;;      (insert "round[" (number-to-string r) "].s_box " (aes-ds state) "\n")
      (aes-ShiftRows state Nb)
;;      (insert "round[" (number-to-string r) "].s_row " (aes-ds state) "\n")
      (aes-MixColumns state Nb)
;;      (insert "round[" (number-to-string r) "].m_col " (aes-ds state) "\n")
      (aes-AddRoundKey state keys r Nb)
;;      (insert "round[" (number-to-string r) "].start " (aes-ds state) "\n")
      (setq r (+ r 1)))
    (aes-SubBytes state)
    (aes-ShiftRows state Nb)
    (aes-AddRoundKey state keys Nr Nb)
    state))

(defun aes-Cipher (input keys Nb)
  "Perform the AES encryption.
Assumes that input and keys are of the correct length."
  (let* ((Nk (- (/ (lsh (length keys) -2) Nb) 7))
         (state (make-string (lsh Nb 2) 0))
         (r 1)
         (Nr (+ Nk 6)))
    (store-substring state 0 input)
    (aes-AddRoundKey state keys 0 Nb)
    (while (< r Nr)
      (aes-SubShiftMix state Nb)
      (aes-AddRoundKey state keys r Nb)
      (setq r (1+ r)))
    (aes-SubBytes state)
    (aes-ShiftRows state Nb)
    (aes-AddRoundKey state keys Nr Nb)
    state))

;; (let* ((plain (concat [#x00 #x11 #x22 #x33 #x44 #x55 #x66 #x77 #x88 #x99 #xaa #xbb #xcc #xdd #xee #xff]))
;;        (key (concat [#x00 #x01 #x02 #x03 #x04 #x05 #x06 #x07 #x08 #x09 #x0a #x0b #x0c #x0d #x0e #x0f #x10 #x11 #x12 #x13 #x14 #x15 #x16 #x17 #x18 #x19 #x1a #x1b #x1c #x1d #x1e #x1f]))
;;        (Nb 4)
;;        (Nk 8)
;;        (Nr (+ Nk 6)))
;;   (aes-ds (aes-Cipher plain (aes-KeyExpansion key Nb) Nb)))

(defun aes-InvCipher-reference (input keys Nb)
  "Perform the AES decryption."
  (let* ((Nk (- (/ (lsh (length keys) -2) Nb) 7))
         (Nr (+ Nk 6))
         (state (make-string (lsh Nb 2) 0))
         (r (- Nr 1)))
    (store-substring state 0 input)
    (aes-AddRoundKey state keys Nr Nb)
    (aes-InvShiftRows state Nb)
    (aes-InvSubBytes state)
    (while (< 0 r)
      (aes-AddRoundKey state keys r Nb)
      (aes-InvMixColumns state Nb)
      (aes-InvShiftRows state Nb)
      (aes-InvSubBytes state)
      (setq r (- r 1)))
    (aes-AddRoundKey state keys 0 Nb)
    state))

(defun aes-InvCipher (input keys Nb)
  "Perform the AES decryption."
  (let* ((Nk (- (/ (lsh (length keys) -2) Nb) 7))
         (Nr (+ Nk 6))
         (state (make-string (lsh Nb 2) 0))
         (r (- Nr 1)))
    (store-substring state 0 input)
    (aes-AddRoundKey state keys Nr Nb)
    (aes-InvShiftRows state Nb)
    (aes-InvSubBytes state)
    (while (< 0 r)
      (aes-AddRoundKey state keys r Nb)
      (aes-InvSubShiftMix state Nb)
      (setq r (- r 1)))
    (aes-AddRoundKey state keys 0 Nb)
    state))

(defun aes-functionality-test ()
  (let* ((plain (string #x00 #x11 #x22 #x33 #x44 #x55 #x66 #x77 #x88 #x99 #xaa
                        #xbb #xcc #xdd #xee #xff))
         (Nb 4)
         (li (let ((r ()))
               (dotimes (i 32)
                 (setq r (concat r (string i))))
               r))
         (tests
          (list (list 4 4 (substring li 0 16))
                (list 6 4 (substring li 0 24))
                (list 8 4 (substring li 0 32)))))
    (or
     (catch 'aes-er
       (while tests
         (let* ((test (car tests))
                (key (elt test 2))
                (Nk (car test))
                (Nr (+ Nk 6))
                (keys (aes-KeyExpansion key Nb))
                (c1 (aes-Cipher-reference plain keys Nb))
                (c2 (aes-Cipher plain keys Nb)))
           (if (not (equal c1 c2))
               (throw 'aes-er (concat "Nk=" (number-to-string Nk) "  Encrypt")))
           (if (not (equal (aes-InvCipher-reference c1 keys Nb)
                           (aes-InvCipher c1 keys Nb)))
               (throw 'aes-er (concat "Nk=" (number-to-string Nk) " Decrypt"))))
         (setq tests (cdr tests))))
     "All went fine.")))

;; (aes-functionality-test)

(defun aes-profile (x)
;;  (setq elp-function-list (list'aes-AddRoundKey 'aes-InvMixColumns 'aes-MixColumns 'aes-InvShiftRows 'aes-ShiftRows 'aes-InvSubBytes 'aes-SubBytes 'aes-SubShiftMix 'aes-InvSubShiftMix 'aes-xor))
  (elp-restore-all)
  (setq elp-function-list (list 'aes-InvCipher 'aes-Cipher
                                'aes-InvCipher-reference 'aes-Cipher-reference
;;                                'aes-SubShiftMix 'aes-InvSubShiftMix
                                ))
  (elp-instrument-list)
  (let* ((Nk 8)
         (Nr (+ Nk 6))
         (factor 10)
         (Nb 4)
         (plain (concat [#x00 #x11 #x22 #x33 #x44 #x55 #x66 #x77 #x88 #x99 #xaa #xbb #xcc #xdd #xee #xff]))
         (key (concat [#x00 #x01 #x02 #x03 #x04 #x05 #x06 #x07 #x08 #x09 #x0a #x0b #x0c #x0d #x0e #x0f #x10 #x11 #x12 #x13 #x14 #x15 #x16 #x17 #x18 #x19 #x1a #x1b #x1c #x1d #x1e #x1f]))
;;         (keys2 (aes-set-encrypt-key key))
         (keys (aes-KeyExpansion key Nb)))
    (dotimes (i (/ x factor))
      (garbage-collect)
      (dotimes (j factor)
;;        (aes-encrypt plain keys2)
        (aes-InvCipher plain keys Nb)
        (aes-InvCipher-reference plain keys Nb)
        (aes-Cipher plain keys Nb)
        (aes-Cipher-reference plain keys Nb))))
  (elp-results)
  (elp-restore-all)
  ())

;; (save-selected-window (aes-profile 10000))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; cbc

(defun aes-enlarge-to-multiple (v bs)
  (concat v (make-string (mod (- (string-bytes v)) bs) 0)))

;; (aes-enlarge-to-multiple "12345678123456781" 8)

(defun aes-cbc-encrypt (input iv keys Nb)
  (let* ((Nk (- (/ (lsh (length keys) -2) Nb) 7))
         (Nr (+ Nk 6))
         (blocksize (lsh Nb 2))
         (res (aes-enlarge-to-multiple input blocksize))
         (blocknumber (/ (string-bytes res) blocksize))
         (pointer 0))
    (dotimes (b blocknumber)
      (let ((temp (aes-Cipher
                   (aes-xor iv (substring res (* b blocksize)
                                          (* (1+ b) blocksize)))
                   keys Nb)))
        (store-substring res (* b blocksize) temp)
        (setq iv temp)))
    res))

(defun aes-cbc-decrypt (input iv keys Nb)
  (let* ((Nk (- (/ (lsh (length keys) -2) Nb) 7))
         (Nr (+ Nk 6))
         (blocksize (lsh Nb 2))
         (res (aes-enlarge-to-multiple input blocksize))
         (blocknumber (/ (string-bytes res) blocksize))
         (pointer 0))
    (dotimes (b blocknumber)
      (let ((temp (substring res (* b blocksize) (* (1+ b) blocksize))))
        (store-substring res (* b blocksize)
                         (aes-xor iv (aes-InvCipher temp keys Nb)))
        (setq iv temp)))
      res))

;; (let* ((in "abcdefghijklmnopqrstuvwxyzhhhhhhhhhhhhhhhhhhhhhhhjhhhhhhhhhhhhhjhjhjhjhjhjhjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjhjhjhjhjjjjjZ")
;;        (Nb 4)
;;        (l (length in))
;;        (key "abcd5678efgh1234")
;;        (iv (let ((res ""))
;;              (dotimes (i (lsh Nb -1))
;;                (setq res (concat res "12345678")))
;;              res))
;;        (keys (aes-KeyExpansion key Nb))
;;        (enc (aes-cbc-encrypt in iv keys Nb))
;;        (dec (aes-cbc-decrypt enc iv keys Nb)))
;;   (substring dec 0 l))



(defun aes-encrypt-string (s &optional Nb Nk)
  (unless Nb (setq Nb 4)) ;; default blocksize of 16 byte / 128 bit
  (unless Nk (setq Nk 4)) ;; default keysize of 16 byte / 128 bit
  (let* ((Nr (+ Nk 6))
         (pre-passwd (let ((p ""))
                       (while (equal p "")
                         (setq p (read-passwd "Password for encryption: ")))
                       p))
         (passwd (aes-enlarge-to-multiple pre-passwd (lsh Nk 2)))
         (passwdiv (make-string (lsh Nk 2) 0))
         (passwdkeys (aes-KeyExpansion passwd Nk))
         (passwdcbc (aes-cbc-encrypt passwd passwdiv passwdkeys Nk))
         (key (substring passwdcbc (- (lsh Nk 2))))
         (keys (aes-KeyExpansion passwd Nb))
         (l (length s))
         (iv (let ((x (make-string (lsh Nb 2) 0)))
               (dotimes (i (lsh Nb 2)) (aset x i (random 256)))
               x)))
    (concat (number-to-string Nb) " " (number-to-string Nk) " " (number-to-string l) "\n" iv (aes-cbc-encrypt s iv keys Nb))))

;; (aes-encrypt-string "hallo" 4 4)

(defun aes-decrypt-string (o)
  (if (string-match "\\`\\([0-9]+\\) \\([0-9]+\\) \\([0-9]+\\)\n" o)
      (let* ((me (match-end 0))
             (Nb (string-to-number (match-string 1 o)))
             (Nk (string-to-number (match-string 2 o)))
             (l (string-to-number (match-string 3 o)))
             (wirr (substring o me))
             (blocksize (lsh Nb 2))
             (iv (substring wirr 0 blocksize))
             (s (substring wirr blocksize))
             (Nr (+ Nk 6))
             (pre-passwd (let ((p ""))
                           (while (equal p "")
                             (setq p (read-passwd "Password for decryption: ")))
                           p))
             (passwd (aes-enlarge-to-multiple pre-passwd (lsh Nk 2)))
             (passwdiv (make-string (lsh Nk 2) 0))
             (passwdkeys (aes-KeyExpansion passwd Nk))
             (passwdcbc (aes-cbc-encrypt passwd passwdiv passwdkeys Nk))
             (key (substring passwdcbc (- (lsh Nk 2))))
             (keys (aes-KeyExpansion passwd Nb))
             )
        (substring (aes-cbc-decrypt s iv keys Nb) 0 l))))

(defun aes-encrypt-buffer (n &optional Nb Nk)
  (unless Nb (setq Nb 4)) ;; default blocksize of 16 byte / 128 bit
  (unless Nk (setq Nk 4)) ;; default keysize of 16 byte / 128 bit
  (with-current-buffer n
    (set-buffer-multibyte nil)
    (let* ((s (buffer-substring-no-properties (point-min) (point-max)))
           (enc (aes-encrypt-string s Nb Nk)))
      (erase-buffer)
      (insert enc))))

(defun aes-decrypt-buffer (n)
  (with-current-buffer n
    (let* ((s (buffer-substring-no-properties (point-min) (point-max)))
           (dec (aes-decrypt-string s)))
      (erase-buffer)
      (insert dec)
      (set-buffer-multibyte t))))

;; (aes-encrypt-buffer "maybe.gtd")
;; (aes-decrypt-buffer "maybe.gtd")

;(let* ((str "hallo")
;       (l (length str))
;       (Nb 4)
;       (Nk 4)
;       (r1 (aes-encrypt-string str Nb Nk))
;       )
;  (aes-decrypt-string r1))


(provide 'aes)
