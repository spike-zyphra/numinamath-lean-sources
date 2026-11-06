import Mathlib

theorem algebra_127436 :
    {(x, y, z) : ℝ × ℝ × ℝ | Real.sqrt (2 * x ^ 2 + 2) = y + 1 ∧ Real.sqrt (2 * y ^ 2 + 2) = z + 1 ∧ Real.sqrt (2 * z ^ 2 + 2) = x + 1} = {(1, 1, 1)} := by 
  ext ⟨x, y, z⟩
  simp [-one_div]
  constructor
  · -- Assume (x, y, z) satisfies the system, prove (x,y,z) = (1,1,1)
    rintro ⟨h1, h2, h3⟩
    have h4 : y + 1 ≥ 0 := by
      by_contra h
      push_neg at h
      have h5 : Real.sqrt (2 * x^2 + 2) < (0 : ℝ) := by
        linarith
      have h6 : Real.sqrt (2 * x^2 + 2) ≥ 0 := by
        apply Real.sqrt_nonneg
      linarith
    have h5 : z + 1 ≥ 0 := by
      by_contra h
      push_neg at h
      have h6 : Real.sqrt (2 * y^2 + 2) < (0 : ℝ) := by
        linarith
      have h7 : Real.sqrt (2 * y^2 + 2) ≥ 0 := by
        apply Real.sqrt_nonneg
      linarith
    have h6 : x + 1 ≥ 0 := by
      by_contra h
      push_neg at h
      have h7 : Real.sqrt (2 * z^2 + 2) < (0 : ℝ) := by
        linarith
      have h8 : Real.sqrt (2 * z^2 + 2) ≥ 0 := by
        apply Real.sqrt_nonneg
      linarith
    have eq1 : 2 * x^2 + 2 = (y + 1) ^ 2 := by
      calc
        2 * x^2 + 2 = (Real.sqrt (2 * x^2 + 2)) ^ 2 := by
          rw [Real.sq_sqrt]
          nlinarith
        _ = (y + 1) ^ 2 := by
          rw [show Real.sqrt (2 * x^2 + 2) = y + 1 by linarith]
    have eq2 : 2 * y^2 + 2 = (z + 1) ^ 2 := by
      calc
        2 * y^2 + 2 = (Real.sqrt (2 * y^2 + 2)) ^ 2 := by
          rw [Real.sq_sqrt]
          nlinarith
        _ = (z + 1) ^ 2 := by
          rw [show Real.sqrt (2 * y^2 + 2) = z + 1 by linarith]
    have eq3 : 2 * z^2 + 2 = (x + 1) ^ 2 := by
      calc
        2 * z^2 + 2 = (Real.sqrt (2 * z^2 + 2)) ^ 2 := by
          rw [Real.sq_sqrt]
          nlinarith
        _ = (x + 1) ^ 2 := by
          rw [show Real.sqrt (2 * z^2 + 2) = x + 1 by linarith]
    have eq5 : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (x + 1 - 2), sq_nonneg (y + 1 - 2), sq_nonneg (z + 1 - 2)]
    have hx1 : (x - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have hy1 : (y - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (z - 1)]
    have hz1 : (z - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
    have hx2 : x - 1 = 0 := by
      nlinarith
    have hy2 : y - 1 = 0 := by
      nlinarith
    have hz2 : z - 1 = 0 := by
      nlinarith
    have hx3 : x = 1 := by nlinarith
    have hy3 : y = 1 := by nlinarith
    have hz3 : z = 1 := by nlinarith
    simp [hx3, hy3, hz3]
  · -- Show that (1,1,1) is a solution
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- Check the first equation
      have h1 : Real.sqrt (2 * (1 : ℝ) ^ 2 + 2) = (1 : ℝ) + 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith
    constructor
    · -- Check the second equation
      have h2 : Real.sqrt (2 * (1 : ℝ) ^ 2 + 2) = (1 : ℝ) + 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith
    · -- Check the third equation
      have h3 : Real.sqrt (2 * (1 : ℝ) ^ 2 + 2) = (1 : ℝ) + 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith