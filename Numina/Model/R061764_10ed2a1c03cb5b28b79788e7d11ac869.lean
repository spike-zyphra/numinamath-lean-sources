import Mathlib

theorem algebra_326805 {f : ℝ → ℝ} (hf : ∀ x, f x = -x * Real.sin (Real.pi / 2) + x * Real.cos (Real.pi / 2)) :
    ∃! x, f x = x := by
  have h1 : Real.sin (Real.pi / 2) = 1 := by 
    rw [Real.sin_pi_div_two]
  have h2 : Real.cos (Real.pi / 2) = 0 := by 
    rw [Real.cos_pi_div_two]
  have h_eq : ∀ (x : ℝ), f x = -x := by
    intro x
    rw [hf x, h1, h2]
    ring
  use 0
  constructor
  · -- Show that 0 is a solution: f(0) = 0
    have h_zero : f 0 = 0 := by
      specialize h_eq 0
      linarith
    simpa using h_zero
  · -- Show that 0 is the only solution
    intro x h_eq_x
    have h_zero : f x = x := h_eq_x
    rw [h_eq x] at h_zero
    linarith
  all_goals try { linarith }
  all_goals try { try linarith }
  all_goals try { try linarith }
  all_goals try { try linarith }