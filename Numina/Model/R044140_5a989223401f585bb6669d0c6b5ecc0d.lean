import Mathlib

open Real Set
open scoped Real

theorem inequalities_122490 (x y : ℝ) (hx : x ∈ Ioo 0 (π/2)) (hy : y ∈ Ioo 0 (π/2)) :
    1/2 * cos (2*x) + 1/2 * cos (2*y) ≤
    cos x * cos y * (1/sin x/sin y - 2) := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have hsinx : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hx1, Real.pi_pos]
    linarith [hx2, Real.pi_pos]

  have hsin_y : sin y > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hy1, Real.pi_pos]
    linarith [hy2, Real.pi_pos]

  have hcosx : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [hx1, Real.pi_pos]
    linarith [hx2, Real.pi_pos]

  have hcosy : cos y > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [hy1, Real.pi_pos]
    linarith [hy2, Real.pi_pos]

  have h1 : 1/2 * cos (2*x) + 1/2 * cos (2*y) ≤ cos x * cos y * (1/sin x/sin y - 2) := by
    have h6 : cos x * cos y * (1/sin x/sin y - 2) = cos x*cos y*(1 - 2*sin x*sin y) / (sin x*sin y) := by
      field_simp [hsinx.ne.symm, hsin_y.ne.symm]
      <;> ring_nf
      <;> field_simp
      <;> ring_nf
    have h7 : sin x*sin y > 0 := mul_pos hsinx hsin_y
    have h8 : (1/2 * cos (2*x) + 1/2 * cos (2*y)) * sin x*sin y ≤ cos x*cos y*(1 - 2*sin x*sin y) := by
      have h9 : cos (2*x) = 2*cos x^2 - 1 := by
        rw [cos_two_mul]
      have h10 : cos (2*y) = 2*cos y^2 - 1 := by
        rw [cos_two_mul]
      rw [h9, h10]
      nlinarith [sq_nonneg (cos x - cos y), sq_nonneg (cos x - sin y), sq_nonneg (sin x - cos y), sq_nonneg (sin x - sin y), sq_nonneg (cos x - sin x), sq_nonneg (cos y - sin y), 
            Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, 
            mul_pos hsinx hsin_y, mul_pos hsinx hcosx, mul_pos hsinx hcosy, 
            mul_pos hsin_y hcosx, mul_pos hsin_y hcosy, 
            mul_pos hcosx hcosy]

    have h15 : (1/2 * cos (2*x) + 1/2 * cos (2*y)) ≤ (cos x*cos y*(1 - 2*sin x*sin y)) / (sin x*sin y) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith

    rw [h6]
    linarith
  linarith