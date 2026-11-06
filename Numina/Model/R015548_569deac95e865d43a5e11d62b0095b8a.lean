import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_16754 {r θ : ℝ} (hr : r = sqrt (10^2 + 3^2)) (hθ : θ = arctan (3 / 10)) :
    (r^2 * cos (2 * θ), r^2 * sin (2 * θ)) = (91, 60) := by
  have hr2 : r^2 = 109 := by
    rw [hr]
    rw [Real.sq_sqrt]
    norm_num
    all_goals norm_num
  have hcos : cos (2 * θ) = 91 / 109 := by
    rw [hθ]
    have h : cos (2 * (arctan (3 / 10))) = 91 / 109 := by
      rw [cos_two_mul, cos_arctan]
      field_simp
      <;> ring_nf
      <;> norm_num
    exact h
  have hsin : sin (2 * θ) = 60 / 109 := by
    rw [hθ]
    have h : sin (2 * (arctan (3 / 10))) = 60 / 109 := by
      rw [sin_two_mul]
      rw [sin_arctan, cos_arctan]
      field_simp
      <;> ring_nf
      <;> norm_num
    exact h
  simp [hr2, hcos, hsin]
  all_goals norm_num