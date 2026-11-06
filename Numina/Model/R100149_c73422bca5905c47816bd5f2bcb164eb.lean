import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_264209 {v u : ℝ} (hv : v > 0) (hu : u > 0)
  (h : v = u) :
  IsLeast {x | ∃ t, x = sqrt (v^2 - u^2) / v ∧ t > 0} (sqrt (v^2 - u^2) / v) := by
  constructor
  · -- Show sqrt (v^2 - u^2) / v is in the set
    use 1
    constructor
    · -- Show x equals sqrt (v^2 - u^2) / v 
      rfl
    · -- Show 1 > 0 
      linarith
  · -- Show that sqrt (v^2 - u^2) / v is the least
    intro x hx
    rcases hx with ⟨t, ht₁, ht₂⟩
    have h1 : sqrt (v^2 - u^2) = 0 := by
      have h2 : v^2 - u^2 = 0 := by
        rw [show v = u by linarith]
        nlinarith
      rw [h2]
      simp
    have h3 : sqrt (v^2 - u^2) / v = 0 := by
      rw [h1]
      norm_num
    linarith [ht₁, h3]