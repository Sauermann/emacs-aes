;;; aes-test.el --- Test of implementation of AES

;; Copyright (C) 2013 Markus Sauermann

;; Author: Markus Sauermann <mhoram@gmx.de>
;; Maintainer: Markus Sauermann <mhoram@gmx.de>
;; Created: 10 Oct 2013
;; Version: 0.1
;; Keywords: data
;; URL: https://github.com/gaddhi/aes

;; This file is not part of GNU Emacs.

;;; Commentary:

;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of the
;; License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see
;; <http://www.gnu.org/licenses/>.

;;; Code:

(require 'testcover)
(require 'ert)

(testcover-start "h:/HOME/_elisp/aes/aes.el" t)

(ert-deftest aes-ert-xor ()
  "test aes-xor"
  (should (equal (aes-xor "ab" "AB") "  "))
  (should (equal (aes-xor "abc" "AB ") "  C")))

(ert-deftest aes-ert-xor-de ()
  "test aes-xor-de"
  (let ((s1 "ab")
        (s2 "abc"))
    (should (eq (aes-xor-de s1 "AB") s1))
    (should (equal s1 "  "))
    (should (eq (aes-xor-de s2 "AB ") s2))
    (should (equal s2 "  C"))))

;;;; Provide

(provide 'aes-test)

;;;; Footer

;; Local Variables:
;; comment-column:0
;; End:

;;; aes.el ends here
