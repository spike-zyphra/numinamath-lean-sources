import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_270143 (α : ℝ) (n : ℕ) (h : sin α ≠ 0) :
  ∏ k ∈ Finset.range (n + 1), cos (2 ^ k * α) = sin (2 ^ (n + 1) * α) / (2 ^ (n + 1) * sin α) := by
  have eq1 : ∀ (n : ℕ), ∏ k ∈ Finset.range (n + 1), cos (2 ^ k * α) = sin (2 ^ (n + 1) * α) / (2 ^ (n + 1) * sin α) := by
    intro n 
    induction n with 
    | zero =>
      simp [Finset.prod_range_succ]
      have h1 : sin (2 * α) = 2 * sin α * cos α := by
        rw [show 2 * α = 2 * α by rfl]
        rw [sin_two_mul]
      field_simp [h]
      <;> 
      simp [h1]
      <;> 
      nlinarith [Real.cos_sq_add_sin_sq α]
    | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have eq2 : sin (2 ^ (n + 2) * α) = 2 * sin (2 ^ (n + 1) * α) * cos (2 ^ (n + 1) * α) := by 
        have h1 : 2 ^ (n + 2) * α = 2 * (2 ^ (n + 1) * α) := by 
          ring 
        rw [h1]
        rw [sin_two_mul]
        <;> ring 
      field_simp at *
      rw [eq2]
      ring 
  exact eq1 n