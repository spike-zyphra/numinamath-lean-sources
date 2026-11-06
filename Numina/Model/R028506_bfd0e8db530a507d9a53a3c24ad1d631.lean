import Mathlib

open Real Set

theorem algebra_225510 {x : ℝ} (hx : x ∈ Icc (-1) 1) :
  arcsin (cos (arcsin x)) = π / 2 - arccos (sin (arccos x)) := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : cos (arcsin x) = Real.sqrt (1 - x^2) := by
    rw [cos_arcsin]
  
  have h2 : sin (arccos x) = Real.sqrt (1 - x^2) := by
    rw [sin_arccos]

  rw [h1, h2]
  have h3 : arcsin (Real.sqrt (1 - x^2)) + arccos (Real.sqrt (1 - x^2)) = π / 2 := by 
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    ring

  linarith