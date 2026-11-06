import Mathlib

open Real Set
open scoped Real

theorem calculus_178381 (x : ℝ) (hx : x ∈ Icc (-1) 1) :
    arcsin x + arccos x = π / 2 := by
  rcases hx with ⟨hx1, hx2⟩
  have h3 : arcsin x + arccos x = π / 2 := by
    have h4 : arccos x = π / 2 - arcsin x := by
      rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    linarith [h4]
  exact h3