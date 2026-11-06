import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_22754 (f : ℝ → ℝ) (hf : f = λ θ => cos θ + 1 / 2)
  (x : ℝ → ℝ) (hx : x = λ θ => f θ * cos θ) :
  IsLeast {x θ | θ ∈ Ioo 0 (2 * π)} (-1 / 16) := by

  have h1 : ∀ θ, x θ = (cos θ + 1 / 2) * cos θ := by
    intro θ
    rw [hx, hf]

  have h2 : -1 / 16 ∈ {x θ | θ ∈ Ioo 0 (2 * π)} := by
    use Real.arccos (-1 / 4)
    constructor
    · -- Show that arccos(-1/4) is in (0, 2π)
      have h3 : 0 < Real.arccos (-1 / 4) := by 
        apply Real.arccos_pos.mpr
        all_goals norm_num
      have h6 : Real.arccos (-1 / 4) < 2 * Real.pi := by 
        have h5 : Real.arccos (-1 / 4) ≤ Real.pi := Real.arccos_le_pi (-1 / 4)
        linarith [Real.pi_pos]
      exact ⟨h3, h6⟩
    · -- Calculate x at arccos(-1/4)
      rw [h1]
      have h7 : cos (Real.arccos (-1 / 4)) = -1 / 4 := by 
        rw [Real.cos_arccos]
        all_goals norm_num
      rw [h7]
      norm_num
      <;> nlinarith

  have h3 : ∀ y, y ∈ {x θ | θ ∈ Ioo 0 (2 * π)} → -1 / 16 ≤ y := by
    intro y hy
    rcases hy with ⟨θ, hθ, rfl⟩
    rw [h1]
    rcases hθ with ⟨hθ1, hθ2⟩
    have h4 : 0 < θ := by linarith
    have h5 : θ < 2 * Real.pi := by linarith
    have h6 : (cos θ + 1 / 2) * cos θ ≥ -1 / 16 := by
      nlinarith [sq_nonneg (cos θ + 1 / 4), Real.cos_le_one θ, Real.neg_one_le_cos θ]
    linarith

  constructor
  · exact h2
  · -- Show that -1/16 is a lower bound
    intro y h
    apply h3 y h