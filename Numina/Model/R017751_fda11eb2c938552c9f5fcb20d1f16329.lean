import Mathlib

open Real Set
open scoped Real

theorem algebra_312753 (A : Real) (hA : A ∈ Ioo 0 π) (h : sin A + cos A = -1/3) :
    cos (2*A) = sqrt 17 / 9 := by
  rcases hA with ⟨hA1, hA2⟩
  have h1 : sin A > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith
  have h2 : sin A ^ 2 + cos A ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq A
  -- Square both sides of h
  have h3 : sin A ^ 2 + 2 * sin A * cos A + cos A ^ 2 = 1 / 9 := by
    have h_eq : sin A + cos A = -1 / 3 := h
    have h_sq : (sin A + cos A) ^ 2 = (-1 / 3) ^ 2 := by
      rw [h_eq]
    -- Expand the square
    have h_exp : (sin A + cos A) ^ 2 = sin A ^ 2 + 2 * sin A * cos A + cos A ^ 2 := by ring
    rw [h_exp] at h_sq
    linarith
  -- sin A * cos A
  have h4 : sin A * cos A = -4 / 9 := by
    nlinarith [h2]
  -- Solve for sin A in terms of cos A
  have h5 : sin A = -1 / 3 - cos A := by
    nlinarith
  -- Substitute sin A in h2
  rw [h5] at h2
  -- This will be a quadratic in cos A. Solve quadratic and take the negative roots
  have h7 : cos A = (-1 - sqrt 17) / 6 := by
    nlinarith [Real.sqrt_pos.mpr (show 0 < (17 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), sq_pos_of_pos h1]
  -- Compute cos 2A
  have h8 : cos (2 * A) = 2 * cos A ^ 2 - 1 := by
    rw [cos_two_mul]
    all_goals norm_num
    <;> nlinarith [Real.sin_sq_add_cos_sq A]
  rw [h8, h7]
  have h9 : 0 < (17 : ℝ) := by norm_num
  have h10 : Real.sqrt 17 > 0 := by positivity
  have h11 : Real.sqrt 17 ^ 2 = (17 : ℝ) := by
    exact Real.sq_sqrt (by linarith)
  field_simp
  nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]