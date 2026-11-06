import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_292231 {f : ℝ → ℝ} (hf : f = λ x => (x + 1)^2 / (x^2 + 1)) :
    StrictMonoOn f (Icc (-1) 1) := by
  intro x hx y hy hxy
  have h1 : -1 ≤ x := hx.1
  have h2 : x ≤ 1 := hx.2
  have h3 : -1 ≤ y := hy.1
  have h4 : y ≤ 1 := hy.2
  have h5 : x < y := hxy
  have h6 : x * y < 1 := by 
    nlinarith [mul_self_nonneg (x - 1), mul_self_nonneg (y - 1), 
      mul_self_nonneg (x + 1), mul_self_nonneg (y + 1),
      mul_self_nonneg (x - y)]
  have h7 : f x < f y := by
    rw [hf]
    have h8 : (x + 1) ^ 2 / (x ^ 2 + 1) < (y + 1) ^ 2 / (y ^ 2 + 1) := by 
      have h9 : (x + 1) ^ 2 * (y ^ 2 + 1) - (y + 1) ^ 2 * (x ^ 2 + 1) < 0 := by 
        nlinarith [mul_pos (show 0 < (1 : ℝ) by norm_num) (show 0 < (1 : ℝ) by norm_num), 
          mul_self_nonneg (x - y), mul_self_nonneg (x * y - 1), 
          mul_self_nonneg (x + 1), mul_self_nonneg (y - 1), 
          mul_pos (show 0 < y - x by linarith) (show 0 < (1 - x * y) by nlinarith), 
          h1, h2, h3, h4]
      have h10 : 0 < (x ^ 2 + 1 : ℝ) := by
        nlinarith
      have h11 : 0 < (y ^ 2 + 1 : ℝ) := by
        nlinarith
      have h14 : (x + 1) ^ 2 / (x ^ 2 + 1) - (y + 1) ^ 2 / (y ^ 2 + 1) < 0 := by 
        have h15 : (x + 1) ^ 2 / (x ^ 2 + 1) - (y + 1) ^ 2 / (y ^ 2 + 1) = 
            ((x + 1) ^ 2 * (y ^ 2 + 1) - (y + 1) ^ 2 * (x ^ 2 + 1)) / ((x ^ 2 + 1) * (y ^ 2 + 1)) := by 
          field_simp
          <;> ring
        rw [h15]
        apply div_neg_of_neg_of_pos
        · linarith
        · positivity
      linarith
    simpa using h8
  exact h7