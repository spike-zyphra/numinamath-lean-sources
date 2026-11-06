import Mathlib
open Finset
theorem algebra_895 {x : ℝ}
    (hx : ∑ i ∈ range 1003, x / ((2 * i + 1) * (2 * i + 3) : ℝ) = 1) :
    x = 2007 / 1003 := by
  
  have h1 : ∀ (n : ℕ), ∑ i ∈ range n, x / ((2 * i + 1) * (2 * i + 3) : ℝ) = x / 2 * (1 - 1 / (2 * (n : ℝ) + 1)) := by 
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      field_simp at *
      ring
  
  have h2 := h1 1003
  rw [h2] at hx
  norm_num at hx
  linarith