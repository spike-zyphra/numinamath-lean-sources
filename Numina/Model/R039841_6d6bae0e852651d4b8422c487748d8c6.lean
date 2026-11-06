import Mathlib

open Real

theorem algebra_97845 {f : ℝ → ℝ} (hf : f = fun x ↦ cos (sin x)) :
    (∃ x, f (x + π / 2) ≠ f x) ∧ ∀ x, f (x + π) = f x := by
  have h1 : ∃ x, f (x + π / 2) ≠ f x := by
    use (0 : ℝ)
    rw [hf]
    simp [Real.sin_pi_div_two]
    have h3 : cos (1) < 1 := by
      have h1 : cos (1) < cos (0 : ℝ) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals linarith [Real.pi_gt_three]
      have h4 : cos (0 : ℝ) = 1 := Real.cos_zero
      linarith [h1, h4]
    intro h
    have h_eq : cos (1) = (1 : ℝ) := by linarith
    linarith [h3, h_eq]
  
  have h2 : ∀ x, f (x + π) = f x := by
    intro x 
    rw [hf]
    simp [show sin (x + π) = -sin x by rw [sin_add, sin_pi, cos_pi]; ring]

  exact ⟨h1, h2⟩