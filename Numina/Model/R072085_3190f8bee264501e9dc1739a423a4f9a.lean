import Mathlib

theorem algebra_286718 (A : Real) (h : Real.cos (2 * A) = -Real.sqrt 5 / 3) :
    6 * Real.sin A ^ 6 + 6 * Real.cos A ^ 6 = 4 := by
  have h1 : Real.cos (2 * A) = 2 * (Real.cos A)^2 - 1 := by
    rw [Real.cos_two_mul]
  rw [h1] at h
  have h2 : (Real.cos A)^2 = (1 - Real.sqrt 5 / 3) / 2 := by
    nlinarith
  have h3 : (Real.sin A)^2 = 1 - (Real.cos A)^2 := by
    have h4 : (Real.sin A)^2 + (Real.cos A)^2 = 1 := by
      exact Real.sin_sq_add_cos_sq A
    nlinarith
  have h4 : (Real.sin A)^2 = (3 + Real.sqrt 5) / 6 := by
    rw [h3, h2]
    field_simp
    <;> nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 5]

  have h5 : (Real.sin A)^6 + (Real.cos A)^6 = (2 / 3 : ℝ) := by
    have h6 : (Real.sin A)^6 + (Real.cos A)^6 = ((Real.sin A)^2)^3 + ((Real.cos A)^2)^3 := by
      ring_nf
    -- We need an algebraic identity here for sum of two cubes
    rw [h6]
    have h7 : ((Real.sin A)^2)^3 + ((Real.cos A)^2)^3 =
      ((Real.sin A)^2 + (Real.cos A)^2) *
      (((Real.sin A)^2)^2 + ((Real.cos A)^2)^2 - ((Real.sin A)^2)*((Real.cos A)^2)) := by
      ring_nf
    rw [h7]
    have h8 : (Real.sin A)^2 + (Real.cos A)^2 = 1 := by
      exact Real.sin_sq_add_cos_sq A
    have h9 : ((Real.sin A)^2)^2 + ((Real.cos A)^2)^2 = ((Real.sin A)^2 + (Real.cos A)^2)^2 - 2 * ((Real.sin A)^2 * (Real.cos A)^2) := by
      ring_nf
    rw [h8] at h9
    rw [h9]
    have h10 : ((Real.sin A)^2)*((Real.cos A)^2) = (1 / 9 : ℝ) := by
      rw [h4, h2]
      have h5_sq : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)
      have h5_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
      field_simp [h5_sq]
      <;> nlinarith [h5_sq, Real.sqrt_nonneg 5, h5_nonneg]
    rw [h8, h10]
    <;> nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 5]

  have eq : 6 * (Real.sin A)^6 + 6 * (Real.cos A)^6 = 4 := by
    nlinarith [h5, Real.sin_sq_add_cos_sq A]

  exact eq
  <;> try { nlinarith }
  <;> try { nlinarith }