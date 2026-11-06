import Mathlib

open Finset List

theorem algebra_11449 (a b c d : ℤ) (h : [a, b, c, d] ~ [1, 2, 3, 4] ):
    (a * b + b * c + c * d + d * a ≤   25) ∧ 
    ([a, b, c, d] = [1, 2, 4, 3] → (a * b + b * c + c * d + d * a = 25)) := by 
  constructor 
  · -- First part: Show that the value is ≤ 25
    have h1 : a + b + c + d = 10 := by
      have h2 : [a, b, c, d].sum = [1, 2, 3, 4].sum := by 
        exact h.sum_eq
      simp [Finset.sum] at h2
      linarith
    nlinarith [sq_nonneg (a + c - 5), sq_nonneg (b + d - 5), h1]
  · -- Second part: Equality condition
    -- Now, we need to check equality.
    intro h_eq
    have h7 : a = 1 := by 
      have h_eq1 : (a : ℤ) = 1 := by
        simp [Prod.ext_iff] at h_eq
        omega
      linarith
    have h8 : b = 2 := by 
      have h_eq1 : (b : ℤ) = 2 := by
        simp [Prod.ext_iff] at h_eq
        omega
      linarith
    have h9 : c = 4 := by 
      have h_eq1 : (c : ℤ) = 4 := by
        simp [Prod.ext_iff] at h_eq
        omega
      linarith
    have h10 : d = 3 := by 
      have h_eq1 : (d : ℤ) = 3 := by
        simp [Prod.ext_iff] at h_eq
        omega
      linarith
    rw [h7, h8, h9, h10]
    all_goals norm_num