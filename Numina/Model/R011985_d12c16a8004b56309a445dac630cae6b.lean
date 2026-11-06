import Mathlib

theorem algebra_97920
    (x : ℝ) (hx : 0 < x)
    (hne : x ≠ 1 / 3 ∧ x ≠ 1 / 2)
    (h : Real.logb (3 * x) 4 = Real.logb (2 * x) 8) :
    ∃ (p q : ℕ),
      0 < p ∧ 0 < q ∧ Nat.gcd p q = 1 ∧ p + q = 31 := by
  have h1 : 0 < x := hx
  have h2 : x ≠ 1 / 3 := hne.1
  have h3 : x ≠ 1 / 2 := hne.2
  use 4, 27
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num