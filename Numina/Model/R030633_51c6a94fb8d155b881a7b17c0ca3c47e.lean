import Mathlib

theorem number_theory_6811
(a b q r : ℕ)
(hpos : (0 < a ∧ 0 < b ∧ 0 < q ∧ 0 < r))
(ha : a > b)
(h1 : a = b * q + r)
(h2 : r < b)
: Nat.gcd a b = Nat.gcd b r := by 
  rw [show a = b * q + r by linarith]
  simp [Nat.gcd_add_mul_left_right, Nat.gcd_comm]