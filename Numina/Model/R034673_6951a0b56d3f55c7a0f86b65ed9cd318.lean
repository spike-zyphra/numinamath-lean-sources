import Mathlib

open BigOperators Real Set

theorem algebra_12822 :
  let f : ℝ → ℝ := fun x ↦ 3^(x + 1)
  let s : Set ℝ := {x | -1 ≤ x ∧ x < 0}
  let t : Set ℝ := {x | 1 ≤ x ∧ x < 3}
  ∃ g : ℝ → ℝ, InvOn g f s t ∧ ∀ x ∈ t, g x = -1 + logb 3 x := by 
  use fun x => -1 + logb 3 x
  constructor
  · -- First, show that g is an inverse of f on s and t
    unfold InvOn 
    constructor 
    · -- Show left inverse property: ∀ x ∈ s, g (f x) = x
      intro x hx
      rcases hx with ⟨hx1, hx2⟩ 
      have h1 : -1 ≤ x := hx1
      have h2 : x < (0 : ℝ) := hx2
      have h5 : 0 ≤ x + 1 := by linarith
      have h6 : x + 1 < 1 := by linarith
      have h3 : (3 : ℝ) ^ (x + 1 : ℝ) ≥ 1 := by
        have h13 : (3 : ℝ) ^ (0 : ℝ) = 1 := by
          norm_num
        have h14 : (3 : ℝ) ^ (x + 1 : ℝ) ≥ (3 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals
            linarith
        nlinarith
      have h7 : (3 : ℝ) ^ (x + 1 : ℝ) < (3 : ℝ) := by
        have h17 : (3 : ℝ) ^ (1 : ℝ) = (3 : ℝ) := by
          norm_num
        have h18 : (3 : ℝ) ^ (x + 1 : ℝ) < (3 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals
            linarith
        linarith [h17, h18]
      have h11 : -1 + logb (3 : ℝ) ((3 : ℝ) ^ (x + 1 : ℝ)) = x := by 
        have h12 : logb (3 : ℝ) ((3 : ℝ) ^ (x + 1 : ℝ)) = x + 1 := by 
          rw [logb_rpow]
          all_goals
            linarith
        linarith [h12]
      simpa using h11
    · -- Show right inverse property: ∀ x ∈ t, f (g x) = x
      intro y hy 
      rcases hy with ⟨hy1, hy2⟩ 
      have h1 : 1 ≤ y := hy1
      have h2 : y < (3 : ℝ) := hy2
      have h9 : -1 + logb (3 : ℝ) y ≥ -1 := by
        have h11 : logb (3 : ℝ) y ≥ 0 := by
          apply logb_nonneg
          all_goals
            linarith
        linarith
      have h15 : (3 : ℝ) ^ ((-1 + logb (3 : ℝ) y + 1 : ℝ) ) = y := by
        have h16 : -1 + logb (3 : ℝ) y + 1 = logb (3 : ℝ) y := by
          linarith
        rw [h16]
        have h17 : (3 : ℝ) ^ (logb (3 : ℝ) y : ℝ) = y := by
          rw [Real.rpow_logb]
          all_goals
            linarith
        linarith
      simpa using h15 
  · -- Show that ∀ x ∈ t, g x = -1 + logb 3 x.
    intro x hx
    simp at hx ⊢
    all_goals
      linarith