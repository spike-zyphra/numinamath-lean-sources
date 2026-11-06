import Mathlib

theorem algebra_301120 {a b : ℝ} (hab : a * b = 1) (ha : a ≠ -1) (hb : b ≠ -1)
    (M N : ℝ) (hM : M = 1 / (1 + a) + 1 / (1 + b)) (hN : N = a / (1 + a) + b / (1 + b)) :
    M = N := by 
  rw [hM, hN]
  have h1 : 1 + a ≠ 0 := by
    intro h
    apply ha
    linarith
  have h2 : 1 + b ≠ 0 := by
    intro h
    apply hb
    linarith
  field_simp [(show 1 + a ≠ 0 by exact h1), (show 1 + b ≠ 0 by exact h2)]
  nlinarith [hab]