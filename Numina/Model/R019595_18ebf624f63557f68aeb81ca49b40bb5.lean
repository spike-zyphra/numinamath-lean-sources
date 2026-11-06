import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_302662 (a b c d : ℝ) (ha : a ≠ 0)
  (f : ℝ → ℝ) (hf : f = λ x => a * x^3 + b * x^2 + c * x + d)
  (h : ∀ x ∈ Icc 0 1, |deriv f x| ≤ 1) :
  a ≤ 8 / 3 := by

  have hf1 : deriv f = fun x => 3 * a * x^2 + 2 * b * x + c := by
    rw [hf]
    funext x
    simp [deriv_pow, deriv_add, deriv_mul, deriv_const, mul_comm c, mul_assoc]
    all_goals field_simp [ha]
    all_goals ring_nf
  have hf2 := h 0 (by norm_num)
  simp [hf1] at hf2
  have hf3 := h 1 (by norm_num)
  simp [hf1] at hf3
  have hf4 := h (1 / 2) (by norm_num)
  simp [hf1] at hf4
  cases' abs_le.mp hf2 with h1 h2
  cases' abs_le.mp hf3 with h3 h4
  cases' abs_le.mp hf4 with h5 h6
  nlinarith