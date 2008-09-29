;;; aes.el --- Implementation of AES in elisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; AES impementation

(defun aes-ds (x)
  "Return the string in its hexadecimal representation."
  (let ((res ""))
    (dotimes (i (length x)) (setq res (concat res (format "%02x" (aref x i)))))
    res))

(defun aes-mul-pre (a b)
  "Multiplication for bytes in GF2."
  (let ((p 0))
    (dotimes (c 8)
      (if (= 1 (logand b 1)) (setq p (logxor a p)))
      (if (prog1 (= #x80 (logand a #x80)) (setq a (logand #xff (lsh a 1))))
          (setq a (logxor a #x1b)))
      (setq b (lsh b -1)))
    p))

(defconst aes-Mul-Table
  (let ((l (make-string 256 0))
        (mt (make-vector 256 0)))
    (dotimes (i 256) (aset mt i (make-string 256 0)))
    (dotimes (x 256)
      (if (< 0 x)
          (let ((i x))
            (while (< i 256)
              (let ((res (aes-mul-pre i x)))
                (if (= #x01 res) (progn (aset l x i) (aset l i x)))
                (aset (aref mt x) i res)
                (aset (aref mt i) x res))
              (setq i (1+ i))))))
    (cons l mt))
  "Inverse and multiplication table.")

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
  "Multiply x and y in GF2."
  (aref (aref (cdr aes-Mul-Table) x) y))

(defconst aes-S-boxes
  (let ((l1 (make-string 256 0))
        (l2 (make-string 256 0)))
    (dotimes (x 256)
      (let ((b (aes-Mul-Inv x))
            (g 0)
            (c #x63))
        (dotimes (i 8) (setq g (logxor (lsh (logand (logxor
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
          (s1 (aref state (1+ (lsh x 2))))
          (s2 (aref state (+ (lsh x 2) 2)))
          (s3 (aref state (+ (lsh x 2) 3))))
      (aset state (lsh x 2) (logxor (aref aes-l2 s0) (aref aes-l3 s1) s2 s3))
      (aset state (1+ (lsh x 2))
            (logxor s0 (aref aes-l2 s1) (aref aes-l3 s2) s3))
      (aset state (+ 2 (lsh x 2))
            (logxor s0 s1 (aref aes-l2 s2) (aref aes-l3 s3)))
      (aset state (+ 3 (lsh x 2))
            (logxor (aref aes-l3 s0) s1 s2 (aref aes-l2 s3))))))

(defun aes-InvMixColumns (state Nb)
  "Apply the inverse mix columns transformation to state."
  (dotimes (x Nb)
    (let ((s3 (aref state (+ (lsh x 2) 3))) (s2 (aref state (+ (lsh x 2) 2)))
          (s1 (aref state (1+ (lsh x 2)))) (s0 (aref state (lsh x 2))))
      (aset state (lsh x 2) (logxor (aref aes-le s0) (aref aes-lb s1)
                                    (aref aes-ld s2) (aref aes-l9 s3)))
      (aset state (1+ (lsh x 2)) (logxor (aref aes-l9 s0) (aref aes-le s1)
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
            (s3 (aref (car aes-S-boxes) (aref copy (% (+ (lsh x 2) 3 12) l)))))
        (aset state (lsh x 2) (logxor (aref aes-l2 s0) (aref aes-l3 s1) s2 s3))
        (aset state (1+ (lsh x 2))
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
            (s1 (aref copy (1+ (lsh x 2))))
            (s2 (aref copy (+ 2 (lsh x 2))))
            (s3 (aref copy (+ 3 (lsh x 2)))))
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

(defun aes-KeyExpansion (key Nb &optional Nr)
  "Return a string, which contains the Key expansion of KEY."
  (let* ((Nk (lsh (length key) -2))
         (w (progn (unless Nr (setq Nr (+ (max Nb Nk) 6)))
                   (make-string (* 4 Nb (1+ Nr)) 0)))
         (i (lsh Nk 2))
         (rcon (concat (make-string 1 1) (make-string 3 0)))
         (Nk2 (lsh Nk 2)))
    (store-substring w 0 key)
    (while (< i (lsh (* Nb (1+ Nr)) 2))
      (let ((temp (substring w (- i 4) i)))
        (if (= 0 (% i Nk2))
            (progn (aes-RotWord temp)
                   (aes-SubWord temp)
                   (setq temp (aes-xor temp rcon))
                   (aset rcon 0 (aes-Mul (aref rcon 0) 2)))
          (if (and (< 6 Nk) (= (% (lsh i -2) Nk) 4))
              (aes-SubWord temp)))
        (store-substring
         w i (aes-xor (substring w (- i Nk2) (+ 4 (- i Nk2))) temp)))
      (setq i (+ i 4)))
    w))

(defun aes-AddRoundKey (state keys r Nb)
  "Add the keys specified  by R and NB of KEYS to STATE."
  (dotimes (i (lsh Nb 2))
    (aset state i (logxor (aref state i) (aref keys (+ (lsh (* r Nb) 2) i))))))

(defun aes-Cipher-reference (input keys Nb &optional Nr)
  "Perform the AES encryption."
  (let* ((Nk (- (/ (lsh (length keys) -2) Nb) 7))
         (state (make-string (lsh Nb 2) 0))
         (r 1))
    (unless Nr (setq Nr (+ (max Nb Nk) 6)))
    (store-substring state 0 input)
    (aes-AddRoundKey state keys 0 Nb)
    (while (< r Nr)
      (aes-SubBytes state)
      (aes-ShiftRows state Nb)
      (aes-MixColumns state Nb)
      (aes-AddRoundKey state keys r Nb)
      (setq r (1+ r)))
    (aes-SubBytes state)
    (aes-ShiftRows state Nb)
    (aes-AddRoundKey state keys Nr Nb)
    state))

(defun aes-Cipher (input keys Nb &optional Nr)
  "Perform the AES encryption.
Assumes that input and keys are of the correct length."
  (let* ((Nk (- (/ (lsh (length keys) -2) Nb) 7))
         (state (make-string (lsh Nb 2) 0))
         (r 1))
    (unless Nr (setq Nr (+ (max Nb Nk) 6)))
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

(defun aes-InvCipher-reference (input keys Nb &optional Nr)
  "Perform the AES decryption."
  (let* ((Nk (- (/ (lsh (length keys) -2) Nb) 7))
         (state (make-string (lsh Nb 2) 0))
         (r (progn (unless Nr (setq Nr (+ (max Nb Nk) 6)))
                   (- Nr 1))))
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

(defun aes-InvCipher (input keys Nb &optional Nr)
  "Perform the AES decryption."
  (let* ((Nk (- (/ (lsh (length keys) -2) Nb) 7))
         (state (make-string (lsh Nb 2) 0))
         (r (progn (unless Nr (setq Nr (+ (max Nb Nk) 6)))
                   (- Nr 1))))
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

;; (defun aes-profile (x)
;;   "Function for profiling the AES implementation."
;;   (setq elp-function-list
;;         (list 'aes-AddRoundKey 'aes-InvMixColumns 'aes-MixColumns
;;               'aes-InvShiftRows 'aes-ShiftRows 'aes-InvSubBytes
;;               'aes-SubBytes 'aes-SubShiftMix 'aes-InvSubShiftMix 'aes-xor))
;;   (elp-restore-all)
;;   (setq elp-function-list
;;         (list 'aes-InvCipher 'aes-Cipher
;;               'aes-InvCipher-reference 'aes-Cipher-reference
;; ;;              'aes-SubShiftMix 'aes-InvSubShiftMix
;;               ))
;;   (elp-instrument-list)
;;   (let* ((Nk 8)
;;          (Nr (+ Nk 6))
;;          (factor 10)
;;          (Nb 4)
;;          (plain (concat [#x00 #x11 #x22 #x33 #x44 #x55 #x66 #x77 #x88 #x99
;;                               #xaa #xbb #xcc #xdd #xee #xff]))
;;          (key (concat [#x00 #x01 #x02 #x03 #x04 #x05 #x06 #x07 #x08 #x09
;;                             #x0a #x0b #x0c #x0d #x0e #x0f #x10 #x11 #x12
;;                             #x13 #x14 #x15 #x16 #x17 #x18 #x19 #x1a #x1b
;;                             #x1c #x1d #x1e #x1f]))
;; ;;         (keys2 (aes-set-encrypt-key key))
;;          (keys (aes-KeyExpansion key Nb)))
;;     (dotimes (i (/ x factor))
;;       (garbage-collect)
;;       (dotimes (j factor)
;; ;;        (aes-encrypt plain keys2)
;;         (aes-InvCipher plain keys Nb)
;;         (aes-InvCipher-reference plain keys Nb)
;;         (aes-Cipher plain keys Nb)
;;         (aes-Cipher-reference plain keys Nb))))
;;   (elp-results)
;;   (elp-restore-all)
;;   ())
;; ;; (save-selected-window (aes-profile 10000))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ocb 2.0 implementation

(defun aes-128-double (x)
  "Double X in 128 bif field."
  (let ((c (lsh (aref x 0) -7))
        (res (make-string 16 0)))
    (dotimes (i 15)
      (aset res i (logand #xff (logxor (lsh (aref x i) 1)
                                       (lsh (aref x (+ i 1)) -7)))))
    (aset res 15 (logand #xff (logxor (lsh (aref x 15) 1) (* c #x87))))
    res))

(defun aes-128-triple (x)
  "Triple X in 128 bif field."
  (let ((te (aes-128-double x)))
    (aes-xor te x)))

(defun aes-num2str (x n)
  "Calculate the n-bit representation of x."
  (let ((res (make-string n 0))
        (offset (- n 1)))
    (while (< 0 x)
      (aset res offset (logand x #xff))
      (setq x (lsh x -8))
      (setq offset (- offset 1)))
    res))

(defun aes-pmac (header keys Nb)
  "Calculate aes-PMAC of header using keys."
  (let* ((l (length header))
         (blocksize (lsh Nb 2))
         (whole-blocks (/ l blocksize))
         (total-blocks (max 1 (+ whole-blocks (if (= 0 (% l blocksize)) 0 1))))
         (b (if (= whole-blocks total-blocks) blocksize (% l blocksize)))
         (D (aes-128-triple
             (aes-128-triple (aes-Cipher (make-string blocksize 0) keys Nb))))
         (checksum (make-string blocksize 0))
         )
    (dotimes (i (- total-blocks 1))
      (setq D (aes-128-double D))
      (setq checksum
            (aes-xor checksum
                     (aes-Cipher (aes-xor D (substring header (* i blocksize)
                                                       (* (+ i 1) blocksize)))
                                 keys Nb))))
    (setq D  (aes-128-double D))
    (if (= b blocksize)
        (progn (setq D (aes-128-triple D))
               (setq checksum
                     (aes-xor checksum
                              (substring header
                                         (* blocksize (- total-blocks 1))))))
      (setq D (aes-128-triple (aes-128-triple D)))
      (setq checksum
            (aes-xor checksum
                     (concat (substring header
                                        (* blocksize (- total-blocks 1)))
                             (make-string 1 #x80)
                             (make-string (- blocksize
                                             (+ 1 b)) 0)))))
    (aes-Cipher (aes-xor D checksum) keys Nb)))

(defun aes-ocb-encrypt (header input iv keys Nb)
  "OCB encrypt input and calculate auth of header and input."
  (let* ((D (aes-Cipher iv keys Nb))
         (C "")
         (T "")
         (checksum (make-string (lsh Nb 2) 0))
         (l (length input))
         (blocksize (lsh Nb 2))
         (whole-blocks (/ l blocksize))
         (total-blocks (max 1 (+ whole-blocks (if (= 0 (% l blocksize)) 0 1))))
         (b (if (= whole-blocks total-blocks) blocksize (% l blocksize)))
         )
;;    (list whole-blocks last-bytes total-blocks)))
    (dotimes (i (- total-blocks 1))
      (setq D (aes-128-double D))
      (setq checksum (aes-xor checksum (substring input (* i blocksize)
                                                  (* (+ i 1) blocksize))))
      (setq C (concat C (aes-xor D (aes-Cipher
                                    (aes-xor D (substring
                                                input (* i blocksize)
                                                (* (+ i 1) blocksize)))
                                    keys Nb)))))
    (setq D (aes-128-double D))
    (let ((pad (aes-Cipher (aes-xor (aes-num2str (* 8 b) blocksize)
                                    D)
                           keys
                           Nb))
          (Mm (substring input (* blocksize (- total-blocks 1)))))
      (setq C (concat C (aes-xor Mm (substring pad 0 b))))
      (setq checksum (aes-xor checksum (concat Mm (substring pad b)))))
    (setq D (aes-128-triple D))
    (setq T (aes-Cipher (aes-xor checksum D) keys Nb))
    (if (< 0 (length header)) (setq T (aes-xor T (aes-pmac header keys Nb))))
    (cons C T)))

(defun aes-ocb-decrypt (header input tag iv keys Nb)
  "OCB decrypt input and verify authentication tag of header and input."
  (let* ((D (aes-Cipher iv keys Nb))
         (M "")
         (l (length input))
         (blocksize (lsh Nb 2))
         (checksum (make-string blocksize 0))
         (whole-blocks (/ l blocksize))
         (total-blocks (max 1 (+ whole-blocks (if (= 0 (% l blocksize)) 0 1))))
         (b (if (= whole-blocks total-blocks) blocksize (% l blocksize)))
         )
    (dotimes (i (- total-blocks 1))
      (setq D (aes-128-double D))
      (let ((Mi (aes-xor D (aes-InvCipher
                            (aes-xor D (substring input (* i blocksize)
                                                  (* (+ i 1) blocksize)))
                            keys Nb))))
        (setq M (concat M Mi))
        (setq checksum (aes-xor checksum Mi))))
    (setq D (aes-128-double D))
    (let* ((pad (aes-Cipher (aes-xor (aes-num2str (* 8 b) blocksize)
                                     D)
                            keys
                            Nb))
           (Mm (aes-xor (substring
                         input (* blocksize (- total-blocks 1)))
                        (substring pad 0 b))))
      (setq M (concat M Mm))
      (setq checksum
            (aes-xor checksum
                     (concat Mm (substring pad b)))))
    (setq D (aes-128-triple D))
    (let ((T (aes-Cipher (aes-xor D checksum) keys Nb)))
      (if (< 0 (length header))
          (setq T (aes-xor T (aes-pmac header keys Nb))))
      (if (equal tag
                 (substring T 0 (length tag)))
          (cons t M)
        (cons nil "")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cbc implementation

(defun aes-enlarge-to-multiple (v bs)
  "Enlarge string V to a multiple of BS."
  (concat v (make-string (mod (- (string-bytes v)) bs) 0)))

(defun aes-cbc-encrypt (input iv keys Nb)
  "Encrypt INPUT by the CBC method using AES for encryption.
Use IV as initialization vector, KEYS as the key expansion and Nb as
blocksize."
  (let* ((Nk (- (/ (lsh (length keys) -2) Nb) 7))
         (Nr (+ (max Nb Nk) 6))
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
  "Decrypt INPUT by the CBC method using AES for decryption.
Use IV as initialization vector, KEYS as the key expansion and Nb as
blocksize."
  (let* ((Nk (- (/ (lsh (length keys) -2) Nb) 7))
         (Nr (+ (max Nb Nk) 6))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Password handling and key generation from passwords

(defgroup aes nil
  "Advanced Encryption Standard implementation"
  :group 'applications)

(defcustom aes-always-ask-for-passwords t
  "Always ask for passwords, if non-nil.
Set this to nil, if you are risky.
If this variable is set to a non-nil value, then no passwords are stored in
aes-plaintext-passwords."
  :type 'boolean
  :group 'aes)

(defcustom aes-enable-plaintext-password-storage nil
  "Store passwords in emacs-memory in plaintext, if non-nil.
Set this to a non-nil value, if you are risky.
Enabling this feature allows someone to read the passwords in plaintext by
accessing the variable aes-plaintext-passwords.
If changing the value from non-nil to nil, then the passwords stored in
aes-plaintext-passwords are not deleted automatically."
  :type 'boolean
  :group 'aes)

(defvar aes-plaintext-passwords ()
  "Association list of plaintext passwords.
Warning: passwords are stored in plaintext and can be read by anyone with
access to the current emacs session.")
;; (setq aes-plaintext-passwords)

(defun aes-clear-plaintext-keys ()
  "Remove all stored passwords."
  (interactive)
  (setq aes-plaintext-passwords))

(defun aes-idle-clear-plaintext-keys ()
  "Remove all stored passwords."
  (setq aes-plaintext-passwords)
  (setq aes-idle-timer-value nil)
  (with-current-buffer "*Messages*"
    (erase-buffer))
  (message "AES Passwords cleared."))

(defcustom aes-delete-passwords-after-idle 1
  "Delete the stored passwords after the given time.
This is disabled, if the value is 0. Otherwise the number is
interpreted as seconds for emacs to be idle before the deletion
happens."
  :type 'integer
  :group 'aes)

(defvar aes-idle-timer-value nil
  "Reference to idle timer.")

(defvar aes-path-passwd-hook ()
  "Hook for testing paths.
Functions, appended to this hook, get one argument: a path of a file to be
en- or decrypted.
According to the path the function should return a string, providing
information about the location, or NIL otherwise.
Using this method it is possible to store the same password, used for multiple
files.
See gtd-mode.el for an example.")

(defun aes-exec-passws-hooks (path)
  "Run the functions in the hook aes-path-passwd-hook.
Return a string resulting from one of the hook functions or NIL otherwise."
  (let ((res (run-hook-with-args-until-success 'aes-path-passwd-hook path)))
    res))

(defun aes-key-from-passwd (Nk &optional type)
  "Return a key, generated from a password.
If aes-use-plaintext-keys is nil and aes-disable-global-plaintext-keys is
non-nil, then use aes-plaintext-passwords for storing and reading passwords.
Query the password from the user if it is not available via
aes-plaintext-passwords."
  (unless type (setq type "usage"))
  (let* ((pre-passwd
          (if (and (not aes-always-ask-for-passwords)
                   aes-enable-plaintext-password-storage
                   (assoc type aes-plaintext-passwords))
              (cdr (assoc type aes-plaintext-passwords))
            (let ((p ""))
              (while (equal p "")
                (setq p (read-passwd (concat "Password for "
                                             type ": "))))
              (if (and (not aes-always-ask-for-passwords)
                       aes-enable-plaintext-password-storage
                       (not
                        (string-match "^usage$\\|^encryption$\\|^decryption$"
                                      type)))
                  (progn
                    (setq aes-plaintext-passwords
                          (cons (cons type p) aes-plaintext-passwords))
                    ;; reset idle timer
                    (if aes-idle-timer-value
                        (progn (cancel-timer aes-idle-timer-value)
                               (setq aes-idle-timer-value nil)))
                    ;; set new idle timer
                    (if (< 0 aes-delete-passwords-after-idle)
                        (setq aes-idle-timer-value
                              (run-with-idle-timer
                               aes-delete-passwords-after-idle
                               nil
                               'aes-idle-clear-plaintext-keys)))))
              p)))
         (passwd (aes-enlarge-to-multiple pre-passwd (lsh Nk 2)))
         (passwdiv (make-string (lsh Nk 2) 0))
         (passwdkeys (aes-KeyExpansion passwd Nk))
         (passwdcbc (aes-cbc-encrypt passwd passwdiv passwdkeys Nk))
         (key (substring passwdcbc (- (lsh Nk 2)))))
    key))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; buffer and string en-/decryption

(defun aes-toggle-representation (s)
  "Toggles string S between unibyte and multibyte.
Return a new string containing the other representation."
  (let ((mb (multibyte-string-p s)))
    (with-temp-buffer
      (if (not mb) (set-buffer-multibyte nil))
      (insert s)
      (set-buffer-multibyte (not mb))
      (buffer-substring-no-properties (point-min) (point-max)))))

(defcustom aes-discard-undo-after-encryption t
  "Delete undo information after encryption, if non-nil."
 :type 'boolean
  :group 'aes)

(defun aes-encrypt-buffer-or-string (bos &optional type Nk Nb non-b64)
  "Encrypt buffer or string bos by the AES-method.
If BOS is a string matching the name of a buffer, then this buffer is used.
Use method TYPE. (OCB or CBC with OCB as default)
Use Nk as keysize (defaults to 4).
Use Nb as blocksite (defaults to 4 and is always 4 for OCB).
Use base64-encoding if non-b64 is NIL, and binary representation otherwise
\(defaults to NIL).
Use a weak-random initialization vector.
Get the key for encryption by the function aes-key-from-passwd."
  (unless type (setq type "OCB")) ;; default to OCB
  (unless Nk (setq Nk 4)) ;; default keysize of 16 byte / 128 bit
  (unless Nb (setq Nb 4)) ;; default blocksize of 16 byte / 128 bit
  (if (and (equal type "OCB") (not (= Nb 4)))
      (setq Nb 4)) ;; blocksize for OCB is 16 byte / 128 bit
  (if (not (member type '("OCB" "CBC")))
      (message "Wrong type.")
    (let* ((Nr (+ (max Nb Nk) 6))
           (bs (or (get-buffer bos) (bufferp bos))) ; t: buffer nil: string
           (passtype (or (if bs (aes-exec-passws-hooks (buffer-file-name bs)))
                         "encryption"))
           (key (aes-key-from-passwd Nk passtype))
           (keys (aes-KeyExpansion key Nb))
           (iv (let ((x (make-string (lsh Nb 2) 0)))
                 (dotimes (i (lsh Nb 2)) (aset x i (random 256)))
                 x))
           (ums (if bs (with-current-buffer bos
                         (cons (if enable-multibyte-characters
                                   (progn (set-buffer-multibyte nil) "M")
                                 "U")
                               (buffer-substring-no-properties
                                (point-min) (point-max))))
                  (if (multibyte-string-p bos)
                      (cons "M" (aes-toggle-representation bos))
                    (cons "U" bos))))
           (header (format "aes-encrypted V 1.2-%s-%s-%d-%d-%s\n"
                           type (if non-b64 "N" "B") Nb Nk (car ums)))
           (l (length (cdr ums)))
           (plain (cond ((equal type "OCB") (cdr ums))
                        ((equal type "CBC")
                         (concat (number-to-string l) "\n" (cdr ums)))))
           (enc (cond ((equal type "OCB")
                       (let ((res (aes-ocb-encrypt header plain iv keys Nb)))
                         (concat iv (cdr res) (car res))))
                      ((equal type "CBC")
                       (concat iv (aes-cbc-encrypt plain iv keys Nb)))))
           (res1 (if non-b64 enc (base64-encode-string enc)))
           (res (concat header res1)))
      (if bs (with-current-buffer bos
               (erase-buffer)
               (insert res)
               (if aes-discard-undo-after-encryption
                   (setq buffer-undo-list))
               t)
        res))))

(defun aes-decrypt-buffer-or-string-1-0 (bos)
  "Old Version 1.0 of decrypt BOS.
Kept for compatibility reasons.
BOS is a buffer, a buffer name or a string."
  (let* ((bs (or (bufferp bos) (get-buffer bos))) ; t: buffer nil: string
         (sp (if bs (with-current-buffer bos
                      (buffer-substring-no-properties (point-min) (point-max)))
               bos)))
    (if (not (string-match "aes-encrypted V 1.0-\\([BN]\\)\n" sp))
        (message (concat "buffer or string '" bos
                         "' is not properly encrypted."))
      (let* ((b64 (equal "B" (match-string 1 sp)))
             (res1 (substring sp (match-end 0)))
             (res2 (if b64 (base64-decode-string res1) res1)))
        (if (not (string-match
                  "\\`\\([0-9]+\\) \\([0-9]+\\)\n"
                  res2))
            (message (concat "buffer or string '" bos
                             "' is of wrong format."))
          (let* ((Nb (string-to-number (match-string 1 res2)))
                 (blocksize (lsh Nb 2))
                 (Nk (string-to-number (match-string 2 res2)))
                 (iv (substring res2 (match-end 0)
                                (+ (match-end 0) blocksize)))
                 (enc (substring res2 (+ (match-end 0) blocksize)))
                 (passtype (or (if bs (aes-exec-passws-hooks
                                       (buffer-file-name bos)))
                       "decryption"))
                 (key (aes-key-from-passwd Nk passtype))
                 (keys (aes-KeyExpansion key Nb))
                 (res3 (aes-cbc-decrypt enc iv keys Nb)))
            (if (not (string-match
                      "\\`\\([UM]\\) \\([0-9]+\\)\n"
                      res3))
                (message (concat "buffer or string '" bos
                                 "' could not be decrypted."))
              (let* ((um (equal (match-string 1 res3) "M"))
                     (l (string-to-number (match-string 2 res3)))
                     (res (substring res3 (match-end 0) (+ (match-end 0) l))))
                (if bs (with-current-buffer bos
                         (erase-buffer) (set-buffer-multibyte nil)
                         (insert res) (set-buffer-multibyte um)
                         t)
                  (if um (aes-toggle-representation res) res))))))))))

(defun aes-decrypt-buffer-or-string-1-1 (bos)
  "Old Version 1.1 of decrypt BOS.
Kept for compatibility reasons.
BOS is a buffer, a buffer name or a string.
If BOS is a string matching the name of a buffer, then this buffer is used.
Get the key for encryption by the function aes-key-from-passwd."
  (let* ((bs (or (bufferp bos) (get-buffer bos))) ; t: buffer nil: string
         (sp (if bs (with-current-buffer bos
                      (buffer-substring-no-properties (point-min) (point-max)))
               bos)))
    (if (not (string-match
              "aes-encrypted V 1.1-\\([BN]\\)-\\([0-9]+\\)-\\([0-9]+\\)\n" sp))
        (aes-decrypt-buffer-or-string-1-0 bos)
      (let* ((b64 (equal "B" (match-string 1 sp)))
             (Nb (string-to-number (match-string 2 sp)))
             (blocksize (lsh Nb 2))
             (Nk (string-to-number (match-string 3 sp)))
             (res1 (substring sp (match-end 0)))
             (res2 (if b64 (base64-decode-string res1) res1))
             (iv (substring res2 0 blocksize))
             (enc (substring res2 blocksize))
             (passtype (or (if bs
                               (aes-exec-passws-hooks (buffer-file-name bos)))
                           "decryption"))
             (key (aes-key-from-passwd Nk passtype))
             (keys (aes-KeyExpansion key Nb))
             (res3 (aes-cbc-decrypt enc iv keys Nb)))
        (if (not (string-match
                  "\\`\\([UM]\\) \\([0-9]+\\)\n"
                  res3))
            (message (concat "buffer or string '" bos
                             "' could not be decrypted."))
          (let* ((um (equal (match-string 1 res3) "M"))
                 (l (string-to-number (match-string 2 res3)))
                 (res (substring res3 (match-end 0) (+ (match-end 0) l))))
            (if bs (with-current-buffer bos
                     (erase-buffer) (set-buffer-multibyte nil)
                     (insert res) (set-buffer-multibyte um)
                     (setq buffer-file-coding-system
                           (car (find-coding-systems-region
                                 (point-min) (point-max))))
                     t)
              (if um (aes-toggle-representation res) res))))))))

(defun aes-decrypt-buffer-or-string (bos)
  "Decrypt BOS V 1.2.
BOS is a buffer, a buffer name or a string.
If BOS is a string matching the name of a buffer, then this buffer is used.
Get the key for encryption by the function aes-key-from-passwd."
  (let* ((bs (or (bufferp bos) (get-buffer bos))) ; t: buffer nil: string
         (sp (if bs (with-current-buffer bos
                      (buffer-substring-no-properties (point-min) (point-max)))
               bos)))
    (if (not (string-match
              (concat "aes-encrypted V 1.2-\\(CBC\\|OCB\\)-"
                      "\\([BN]\\)-\\([0-9]+\\)-\\([0-9]+\\)-\\([MU]\\)\n") sp))
        (aes-decrypt-buffer-or-string-1-1 bos)
      (let* ((type (match-string 1 sp))
             (b64 (equal "B" (match-string 2 sp)))
             (Nb (string-to-number (match-string 3 sp)))
             (blocksize (lsh Nb 2))
             (Nk (string-to-number (match-string 4 sp)))
             (Nr (+ (max Nk Nb) 6))
             (um (match-string 5 sp))
             (header (match-string 0 sp))
             (res1 (substring sp (match-end 0)))
             (res2 (if b64 (base64-decode-string res1) res1))
             (iv (substring res2 0 blocksize))
             (enc-offset (cond ((equal type "CBC") blocksize)
                               ((equal type "OCB") (lsh blocksize 1))))
             (tag (substring res2 blocksize enc-offset))
             (enc (substring res2 enc-offset))
             (passtype (or (if bs
                               (aes-exec-passws-hooks (buffer-file-name bos)))
                           "decryption"))
             (key (aes-key-from-passwd Nk passtype))
             (keys (aes-KeyExpansion key Nb))
             (res1 (cond ((equal type "CBC") (aes-cbc-decrypt enc iv keys Nb))
                         ((equal type "OCB")
                          (aes-ocb-decrypt header enc tag iv keys Nb)))))
        (if (or (and (equal type "CBC")
                     (not (string-match "\\`\\([0-9]+\\)\n" res1)))
                (and (equal type "OCB") (not (car res1))))
            (message (concat "buffer or string '"
                             (if (bufferp bos) (buffer-name bos) bos)
                             "' could not be decrypted."))
          (let* ((len (and (equal type "CBC")
                         (string-to-number (match-string 1 res1))))
                 (res (cond ((equal type "CBC")
                             (substring res1 (match-end 0)
                                        (+ (match-end 0) len)))
                            ((equal type "OCB") (cdr res1)))))
            (if bs (with-current-buffer bos
                     (erase-buffer) (set-buffer-multibyte nil)
                     (insert res) (set-buffer-multibyte um)
                     (setq buffer-file-coding-system
                           (car (find-coding-systems-region
                                 (point-min) (point-max))))
                     t)
              (if um (aes-toggle-representation res) res))))))))

(defun aes-encrypt-and-dont-save ()
  "Encrypt and dont save current buffer.
Return NIL."
  (goto-char (point-min))
  (if (not (looking-at "aes-encrypted V [0-9]+.[0-9]+-.+\n"))
      (progn
        (aes-encrypt-buffer-or-string (current-buffer))
        (goto-char (point-min))
        nil)))

(defun aes-encrypt-current-buffer ()
  "Encrypt current buffer."
  (interactive)
  (aes-encrypt-buffer-or-string (current-buffer)))

(defun aes-decrypt-current-buffer ()
  "Decrypt current buffer."
  (interactive)
  (aes-decrypt-buffer-or-string (current-buffer)))

(defun aes-toggle-encryption ()
  "Encrypt or decrypt current buffer. Set according saving hook.
Preserve modification status of buffer during decryption."
  (interactive)
  (goto-char (point-min))
  (if (looking-at "aes-encrypted V [0-9]+.[0-9]+-.+\n")
      (let ((mod-flag (buffer-modified-p)))
        (aes-decrypt-buffer-or-string (current-buffer))
        (set-buffer-modified-p mod-flag)
        (add-hook (if (<= emacs-major-version 21)
                      'local-write-file-hooks
                    'write-file-functions)
                  'aes-encrypt-and-dont-save nil t))
    (aes-encrypt-buffer-or-string (current-buffer)))
  (goto-char (point-min)))

(defun aes-remove-encryption-hook ()
  "Remove saving-hook from current buffer.
This allows saving a previously encrypted buffer in plaintext."
  (interactive)
  (remove-hook (if (<= emacs-major-version 21)
                   'local-write-file-hooks
                 'write-file-functions)
               'aes-encrypt-and-dont-save t)
  (message "Encryption Hook removed."))

(defun aes-auto-decrypt (&rest x)
  "Function for auto decryption used in format-alist.
WARNING: not compliant to format-alist in the sense that the function
decrypts the whole file and not just the indicated region."
  (goto-char (point-min))
  (if (looking-at "aes-encrypted V [0-9]+.[0-9]+-.+\n")
      (let ((mod-flag (buffer-modified-p)))
        (aes-decrypt-buffer-or-string (current-buffer))
        (set-buffer-modified-p mod-flag)
        (if (<= emacs-major-version 21)
            (add-hook 'local-write-file-hooks 'aes-encrypt-and-dont-save nil t)
          (add-hook 'write-file-functions 'aes-encrypt-and-dont-save nil t))
        ))
  (goto-char (point-min)))

(setq format-alist
      (cons (list 'aes
                  "AES-encrypted format"
                  "aes-encrypted V [0-9]+.[0-9]+-.+\n"
                  'aes-auto-decrypt
                  nil
                  t
                  nil)
            format-alist))
;; (setq format-alist (cdr format-alist))

(provide 'aes)
