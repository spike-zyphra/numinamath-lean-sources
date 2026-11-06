import Mathlib

theorem number_theory_176739 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h : (10 * a + b) ^ 2 ≡ 10 * a + b [MOD 100]) :
    (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (2, 5) ∨ (a, b) = (7, 6) := by
  norm_num [Nat.ModEq] at h
  interval_cases a <;> interval_cases b <;> norm_num at h ⊢ <;> tauto