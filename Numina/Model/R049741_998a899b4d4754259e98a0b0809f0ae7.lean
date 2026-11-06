import Mathlib

theorem algebra_171363 (α β γ δ : ℝ) (h₀ : α < β) (h₁ : γ ∈ Set.Icc α β) (h₂ : δ ∈ Set.Icc α β)
    (h₃ : γ < δ) :
    (δ - γ) / (β - α) = (MeasureTheory.volume {x | γ < x ∧ x < δ}).toReal / (MeasureTheory.volume {x | α ≤ x ∧ x ≤ β}).toReal := by

  have h4 : (MeasureTheory.volume {x | γ < x ∧ x < δ}).toReal = δ - γ := by
    have h5 : {x | γ < x ∧ x < δ} = Set.Ioo γ δ := by
      ext x
      simp [Set.mem_setOf_eq, Set.mem_Ioo]
    rw [h5]
    simp
    <;> linarith

  have h6 : (MeasureTheory.volume {x | α ≤ x ∧ x ≤ β}).toReal = β - α := by
    have h7 : {x | α ≤ x ∧ x ≤ β} = Set.Icc α β := by
      ext x
      simp [Set.mem_setOf_eq, Set.mem_Icc]
    rw [h7]
    simp
    <;> linarith
  
  rw [h4, h6]
  all_goals linarith