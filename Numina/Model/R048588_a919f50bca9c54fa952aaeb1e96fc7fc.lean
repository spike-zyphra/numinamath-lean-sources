import Mathlib

theorem number_theory_139002 (a b c d e : ℕ) (ha : a ≠ 0) (h : a ≤ 9) (h' : b ≤ 9)
    (h'' : c ≤ 9) (h''' : d ≤ 9) (h'''' : e ≤ 9) (h1 : 10 * a + b = 33) (h2 : 10 * a + c = 37)
    (h3 : 10 * a + d = 37) (h4 : 10 * a + e = 37) (h5 : 10 * b + c = 38) (h6 : 10 * b + d = 73)
    (h7 : 10 * b + e = 77) (h8 : 10 * c + d = 78) (h9 : 10 * c + e = 83) (h10 : 10 * d + e = 87) :
    10000 * a + 1000 * b + 100 * c + 10 * d + e = 37837 := by 
  omega