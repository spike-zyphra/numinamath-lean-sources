import Mathlib

open Real Set
open scoped Real

theorem inequalities_156722 (x y : ℝ) (hx : x ∈ Icc 0 (π/2)) (hy : y ∈ Icc 0 (π/2))
    (hxy : x ≤ y) :
    sin (x/2) ^ 2 * cos y ≤ 1/8 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h1 : 0 ≤ x := hx1
  have h2 : x ≤ π / 2 := hx2
  have h3 : 0 ≤ y := hy1
  have h4 : y ≤ π / 2 := hy2
  have h5 : cos y ≤ cos x := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    all_goals linarith [Real.pi_pos, h1, h2, h3, h4, hxy]
  have h12 : sin (x / 2) ^ 2 = (1 - cos x) / 2 := by
    have h11 : cos x = 1 - 2 * sin (x / 2) ^ 2 := by
      have h13 : cos x = cos (2 * (x / 2)) := by ring_nf
      rw [h13]
      rw [cos_two_mul]
      have h14 : sin (x / 2) ^ 2 = sin (x / 2) ^ 2 := by rfl
      rw [sin_sq]
      <;> ring_nf <;> field_simp <;> ring
    linarith 
  have h7 : sin (x / 2) ^ 2 * cos y ≤ sin (x / 2) ^ 2 * cos x := by 
    apply mul_le_mul_of_nonneg_left 
    linarith 
    have h10 : sin (x / 2) ≥ 0 := by 
      apply sin_nonneg_of_nonneg_of_le_pi 
      linarith [Real.pi_pos, h1] 
      linarith [Real.pi_pos, h2] 
    nlinarith [sin_nonneg_of_nonneg_of_le_pi (show (0 : ℝ) ≤ x / 2 by linarith [h1, Real.pi_pos] ) (show x / 2 ≤ Real.pi by nlinarith [Real.pi_pos, h2]), Real.sin_sq_add_cos_sq (x / 2)]
  have h8 : sin (x / 2) ^ 2 * cos x = (cos x - cos x ^ 2) / 2 := by
    rw [h12]
    linarith 
  have h9 : (cos x - cos x ^ 2) / 2 ≤ 1 / 8 := by 
    nlinarith [sq_nonneg (2 * cos x - 1), Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq (x / 2), Real.sin_nonneg_of_nonneg_of_le_pi (show (0 : ℝ) ≤ x / 2 by linarith [h1, Real.pi_pos] ) (show x / 2 ≤ Real.pi by nlinarith [Real.pi_pos, h2]), sq_nonneg (cos x - 1 / 2)]
  linarith [h7, h8, h9]