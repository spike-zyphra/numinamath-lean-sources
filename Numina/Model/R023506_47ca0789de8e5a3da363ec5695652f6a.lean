import Mathlib

open Real Set

theorem inequalities_239260 :
    IsLeast {s | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 1 ∧ s = y * z / x + z * x / y + x * y / z} (Real.sqrt 3) := by
  constructor
  · -- Show that $\sqrt{3}$ is in the set.
    use Real.sqrt (1 / 3), Real.sqrt (1 / 3), Real.sqrt (1 / 3)
    constructor
    · -- Show that x > 0
      positivity
    constructor
    · -- Show that y > 0
      positivity
    constructor
    · -- Show that z > 0
      positivity
    constructor
    · -- Show that x ^ 2 + y ^ 2 + z ^ 2 = 1
      have h1 : (Real.sqrt (1 / 3) : ℝ) ^ 2 = 1 / 3 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      nlinarith [h1]
    · -- Show that s = sqrt 3
      have h1 : (Real.sqrt (1 / 3) : ℝ) ^ 2 = 1 / 3 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      field_simp [h1]
      have h2 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (1 / 3), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (1 / 3))]
  · -- Show that $\sqrt{3}$ is the least element in the set
    intro s hs
    rcases hs with ⟨x, y, z, hx, hy, hz, h1, heq⟩
    have h2 : (y * z / x + z * x / y + x * y / z) ^ 2 ≥ 3 := by
      have h3 : (y * z / x + z * x / y + x * y / z) ^ 2 = (y * z / x) ^ 2 + (z * x / y) ^ 2 + (x * y / z) ^ 2 + 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
        have h4 : (y * z / x + z * x / y + x * y / z) ^ 2 = (y * z / x) ^ 2 + (z * x / y) ^ 2 + (x * y / z) ^ 2 + 2 * ( (y * z / x) * (z * x / y) + (y * z / x) * (x * y / z) + (z * x / y) * (x * y / z) ) := by ring
        have h5 : (y * z / x) * (z * x / y) = z^2 := by
          field_simp
          <;> ring
        have h6 : (y * z / x) * (x * y / z) = y^2 := by
          field_simp
          <;> ring
        have h7 : (z * x / y) * (x * y / z) = x^2 := by
          field_simp
          <;> ring
        rw [h4, h5, h6, h7]
        <;> nlinarith
      have h8 : (y * z / x) ^ 2 + (z * x / y) ^ 2 + (x * y / z) ^ 2 ≥ 1 := by
        nlinarith [sq_nonneg (y * z / x - z * x / y), sq_nonneg (y * z / x - x * y / z), sq_nonneg (z * x / y - x * y / z), 
                  sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (z ^ 2 - x ^ 2), 
                  sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
                  mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
                ]
      nlinarith [h1, h3, h8]
    have h3 : (y * z / x + z * x / y + x * y / z) ≥ 0 := by
      positivity
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), heq, h2, h3
    ]