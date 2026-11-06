import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_48814 {f : ℝ → ℝ} (hf : ∀ x ∈ Icc 0 1, |f x| ≤ 1)
  (h : ∃ a b c, ∀ x, f x = a*x^2 + b*x + c) :
  |deriv f 0| ≤ 8 := by
    rcases h with ⟨a, b, c, heq⟩
    have h1 : deriv f 0 = b := by
      have eq1 : f = fun x => a * x^2 + b * x + c := by
        funext x
        exact heq x
      rw [eq1]
      simp [deriv_const, deriv_id', deriv_pow, deriv_add, deriv_mul, mul_comm b, mul_assoc, add_left_comm]
      all_goals norm_num
      all_goals linarith
    rw [h1]
    have h2 := hf 0 (by norm_num)
    have h3 := hf 1 (by norm_num)
    have h4 := hf (1 / 2) (by norm_num)
    have eq1 : f 0 = c := by
      simp [heq]
    have eq2 : f 1 = a + b + c := by
      simp [heq]
      <;> ring
    have eq3 : f (1 / 2) = a * (1 / 2) ^ 2 + b * (1 / 2) + c := by
      simp [heq]
    rw [eq1] at h2
    rw [eq2] at h3
    rw [eq3] at h4
    have h21 : -1 ≤ c := by linarith [abs_le.mp h2]
    have h22 : c ≤ 1 := by linarith [abs_le.mp h2]
    have h31 : -1 ≤ a + b + c := by linarith [abs_le.mp h3]
    have h32 : a + b + c ≤ 1 := by linarith [abs_le.mp h3]
    have h41 : -1 ≤ a * (1 / 2) ^ 2 + b * (1 / 2) + c := by linarith [abs_le.mp h4]
    have h42 : a * (1 / 2) ^ 2 + b * (1 / 2) + c ≤ 1 := by linarith [abs_le.mp h4]
    have h51 : -4 ≤ a + 2 * b + 4 * c := by
      nlinarith
    have h52 : a + 2 * b + 4 * c ≤ 4 := by
      nlinarith
    apply abs_le.mpr
    constructor
    · linarith
    · linarith