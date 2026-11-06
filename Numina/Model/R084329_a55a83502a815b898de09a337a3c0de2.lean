import Mathlib

open Real

theorem algebra_158787 {F : ℝ → ℝ} (hF : F ≤ 1 ∧ F ≥ 0)
    (G : ℝ → ℝ) (hG : G = fun y => F ((y - 2) / 3)) :
    ∀ y, G y ∈ Set.Icc 0 1 := by
  have h5 : ∀ x : ℝ, 0 ≤ F x ∧ F x ≤ 1 := by
    intro x
    have h1 : F x ≤ 1 := by 
      apply (hF.left)
      all_goals simp [Function.comp_apply]
    have h2 : 0 ≤ F x := by 
      apply (hF.right)
      all_goals simp [Function.comp_apply]
    exact ⟨h2, h1⟩
  intro y 
  have h1 : G y = F ((y - 2) / 3) := by 
    rw [hG]
  rw [h1]
  have h2 := h5 ((y - 2) / 3)
  exact ⟨h2.1, h2.2⟩