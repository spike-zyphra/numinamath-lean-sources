import Mathlib

theorem number_theory_85095 (a : ℝ) (ha : a ≠ 0) (n : ℕ) :
    (a % 1 + 1 / a % 1 = 1) → (a ^ n % 1 + 1 / a ^ n % 1 = 1) := by
  intro h
  norm_num [Int.floor_eq_iff] at h ⊢
  <;> linarith