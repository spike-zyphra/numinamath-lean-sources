import Mathlib

theorem number_theory_54915 (a b c : ℕ) (ha : a < 10) (hb : b < 10) (hc : c < 10)
    (h : Nat.factorial 21 = 51090942171000440000 + 10^6 * (100 * a + 10 * b + c)) :
    100 * a + 10 * b + c = 709 := by 
  norm_num [Nat.factorial] at h
  norm_num [mul_add, add_mul, Nat.add_assoc] at h ⊢
  omega