import Mathlib
theorem algebra_604875 (x y z : ℝ) : (x = √(2 * y + 3) ∧ y = √(2 * z + 3) ∧ z = √(2 * x + 3)) ↔ x = 3 ∧ y = 3 ∧ z = 3 := by
  constructor
  · -- Assume (x, y, z) satisfy the three equations, prove x = 3 ∧ y = 3 ∧ z = 3
    rintro ⟨hx, hy, hz⟩
    have h1 : x ≥ 0 := by
      have h1 : x = √(2 * y + 3) := hx
      have h2 : √(2 * y + 3) ≥ 0 := by positivity
      linarith [h1, h2]
    have h2 : y ≥ 0 := by
      have h2 : y = √(2 * z + 3) := hy
      have h3 : √(2 * z + 3) ≥ 0 := by positivity
      linarith [h2, h3]
    have h3 : z ≥ 0 := by
      have h3 : z = √(2 * x + 3) := hz
      have h4 : √(2 * x + 3) ≥ 0 := by positivity
      linarith [h3, h4]
    have eq1 : x ^ 2 = 2 * y + 3 := by
      calc
        x ^ 2 = (√(2 * y + 3)) ^ 2 := by rw [show √(2 * y + 3) = x by linarith [hx]]
        _ = 2 * y + 3 := by
          apply Real.sq_sqrt
          nlinarith
    have eq2 : y ^ 2 = 2 * z + 3 := by
      calc
        y ^ 2 = (√(2 * z + 3)) ^ 2 := by rw [show √(2 * z + 3) = y by linarith [hy]]
        _ = 2 * z + 3 := by
          apply Real.sq_sqrt
          nlinarith
    have eq3 : z ^ 2 = 2 * x + 3 := by
      calc
        z ^ 2 = (√(2 * x + 3)) ^ 2 := by rw [show √(2 * x + 3) = z by linarith [hz]]
        _ = 2 * x + 3 := by
          apply Real.sq_sqrt
          nlinarith
    have h4 : x = 3 := by
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3)]
    have h5 : y = 3 := by
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3)]
    have h6 : z = 3 := by
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3)]
    exact ⟨h4, h5, h6⟩
  · -- Assume x = 3 ∧ y = 3 ∧ z = 3, prove they satisfy the three equations.
    rintro ⟨hx, hy, hz⟩
    constructor
    · -- Show x = √(2 * y + 3)
      rw [hx, hy]
      have h1 : √(2 * (3 : ℝ) + 3) = (3 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h1]
    constructor
    · -- Show y = √(2 * z + 3)
      rw [hy, hz]
      have h2 : √(2 * (3 : ℝ) + 3) = (3 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h2]
    · -- Show z = √(2 * x + 3)
      rw [hz, hx]
      have h3 : √(2 * (3 : ℝ) + 3) = (3 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h3]