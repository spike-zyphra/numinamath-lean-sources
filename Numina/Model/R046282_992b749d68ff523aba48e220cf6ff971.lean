import Mathlib

theorem algebra_198800 :
    { (x, y, z) : ℝ×ℝ×ℝ | 
        2 * x ^ 2 + 3 * y + 5 = 2 * Real.sqrt (2 * z + 5) ∧ 
        2 * y ^ 2 + 3 * z + 5 = 2 * Real.sqrt (2 * x + 5) ∧ 
        2 * z ^ 2 + 3 * x + 5 = 2 * Real.sqrt (2 * y + 5) ∧ 
          2 * x + 5 ≥ 0 ∧ 2 * y + 5 ≥ 0 ∧ 2 * z + 5 ≥ 0 
    } = {(-0.5, -0.5, -0.5)}:= by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- First, prove that (-0.5, -0.5, -0.5) is the only solution.
    rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
    have h8 : (2 * x ^ 2 + 3 * y + 5) ^ 2 = 4 * (2 * z + 5):= by
      have h9 : 2 * x ^ 2 + 3 * y + 5 ≥ 0 := by
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (z + 1 / 2),
          Real.sqrt_nonneg (2 * z + 5)]
      have h10 : Real.sqrt (2 * z + 5) ≥ 0 := Real.sqrt_nonneg (2 * z + 5)
      calc
        (2 * x ^ 2 + 3 * y + 5) ^ 2 = (2 * Real.sqrt (2 * z + 5)) ^ 2 := by
          rw [show 2 * x ^ 2 + 3 * y + 5 = 2 * Real.sqrt (2 * z + 5) by linarith [h₁]]
        _ = 4 * (Real.sqrt (2 * z + 5) ^ 2) := by ring
        _ = 4 * (2 * z + 5) := by
          rw [Real.sq_sqrt]
          linarith
    have h9 : (2 * y ^ 2 + 3 * z + 5) ^ 2 = 4 * (2 * x + 5):= by
      have h10 : 2 * y ^ 2 + 3 * z + 5 ≥ 0 := by
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (z + 1 / 2),
          Real.sqrt_nonneg (2 * x + 5)]
      have h11 : Real.sqrt (2 * x + 5) ≥ 0 := Real.sqrt_nonneg (2 * x + 5)
      calc
        (2 * y ^ 2 + 3 * z + 5) ^ 2 = (2 * Real.sqrt (2 * x + 5)) ^ 2 := by
          rw [show 2 * y ^ 2 + 3 * z + 5 = 2 * Real.sqrt (2 * x + 5) by linarith [h₂]]
        _ = 4 * (Real.sqrt (2 * x + 5) ^ 2) := by ring
        _ = 4 * (2 * x + 5) := by
          rw [Real.sq_sqrt]
          linarith
    have h10 : (2 * z ^ 2 + 3 * x + 5) ^ 2 = 4 * (2 * y + 5):= by
      have h11 : 2 * z ^ 2 + 3 * x + 5 ≥ 0 := by
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (z + 1 / 2),
          Real.sqrt_nonneg (2 * y + 5)]
      have h12 : Real.sqrt (2 * y + 5) ≥ 0 := Real.sqrt_nonneg (2 * y + 5)
      calc
        (2 * z ^ 2 + 3 * x + 5) ^ 2 = (2 * Real.sqrt (2 * y + 5)) ^ 2 := by
          rw [show 2 * z ^ 2 + 3 * x + 5 = 2 * Real.sqrt (2 * y + 5) by linarith [h₃]]
        _ = 4 * (Real.sqrt (2 * y + 5) ^ 2) := by ring
        _ = 4 * (2 * y + 5) := by
          rw [Real.sq_sqrt]
          linarith
    have h12 : (x + 0.5) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 0.5), sq_nonneg (y + 0.5), sq_nonneg (z + 0.5),
        sq_nonneg (2 * x ^ 2 + 3 * y + 5 - 4), sq_nonneg (2 * y ^ 2 + 3 * z + 5 - 4), sq_nonneg (2 * z ^ 2 + 3 * x + 5 - 4),
        Real.sqrt_nonneg (2 * z + 5), Real.sqrt_nonneg (2 * x + 5), Real.sqrt_nonneg (2 * y + 5),
          mul_nonneg (show (0 : ℝ) ≤ 2 * z + 5 by linarith) (show (0 : ℝ) ≤ 2 * x + 5 by linarith),
            mul_nonneg (show (0 : ℝ) ≤ 2 * x + 5 by linarith) (show (0 : ℝ) ≤ 2 * y + 5 by linarith),
              mul_nonneg (show (0 : ℝ) ≤ 2 * y + 5 by linarith) (show (0 : ℝ) ≤ 2 * z + 5 by linarith)]
    have hx1 : x + 0.5 = 0 := by
      rw [sq_eq_zero_iff] at h12
      exact h12
    have hx2 : x = -0.5 := by
      have h13 : x + 0.5 = 0 := hx1
      linarith
    have h14 : (y + 0.5) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 0.5), sq_nonneg (y + 0.5), sq_nonneg (z + 0.5),
        sq_nonneg (2 * x ^ 2 + 3 * y + 5 - 4), sq_nonneg (2 * y ^ 2 + 3 * z + 5 - 4), sq_nonneg (2 * z ^ 2 + 3 * x + 5 - 4),
        Real.sqrt_nonneg (2 * z + 5), Real.sqrt_nonneg (2 * x + 5), Real.sqrt_nonneg (2 * y + 5),
          mul_nonneg (show (0 : ℝ) ≤ 2 * z + 5 by linarith) (show (0 : ℝ) ≤ 2 * x + 5 by linarith),
            mul_nonneg (show (0 : ℝ) ≤ 2 * x + 5 by linarith) (show (0 : ℝ) ≤ 2 * y + 5 by linarith),
              mul_nonneg (show (0 : ℝ) ≤ 2 * y + 5 by linarith) (show (0 : ℝ) ≤ 2 * z + 5 by linarith)]
    have hy1 : y + 0.5 = 0 := by
      rw [sq_eq_zero_iff] at h14
      exact h14
    have hy2 : y = -0.5 := by
      have h15 : y + 0.5 = 0 := hy1
      linarith
    have h16 : (z + 0.5) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 0.5), sq_nonneg (y + 0.5), sq_nonneg (z + 0.5),
        sq_nonneg (2 * x ^ 2 + 3 * y + 5 - 4), sq_nonneg (2 * y ^ 2 + 3 * z + 5 - 4), sq_nonneg (2 * z ^ 2 + 3 * x + 5 - 4),
        Real.sqrt_nonneg (2 * z + 5), Real.sqrt_nonneg (2 * x + 5), Real.sqrt_nonneg (2 * y + 5),
          mul_nonneg (show (0 : ℝ) ≤ 2 * z + 5 by linarith) (show (0 : ℝ) ≤ 2 * x + 5 by linarith),
            mul_nonneg (show (0 : ℝ) ≤ 2 * x + 5 by linarith) (show (0 : ℝ) ≤ 2 * y + 5 by linarith),
              mul_nonneg (show (0 : ℝ) ≤ 2 * y + 5 by linarith) (show (0 : ℝ) ≤ 2 * z + 5 by linarith)]
    have hz1 : z + 0.5 = 0 := by
      rw [sq_eq_zero_iff] at h16
      exact h16
    have hz2 : z = -0.5 := by
      have h17 : z + 0.5 = 0 := hz1
      linarith
    simp [hx2, hy2, hz2]
  · -- Now prove the converse.
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- First equation: 2*(-0.5)^2 + 3*(-0.5) + 5 = 2*sqrt(2*(-0.5) + 5)
      have h8 : Real.sqrt (2 * (-0.5 : ℝ) + 5) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h8]
      norm_num
    constructor
    · -- Second equation: 2*(-0.5)^2 + 3*(-0.5) + 5 = 2*sqrt(2*(-0.5) + 5)
      have h8 : Real.sqrt (2 * (-0.5 : ℝ) + 5) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h8]
      norm_num
    constructor
    · -- Third equation: 2*(-0.5)^2 + 3*(-0.5) + 5 = 2*sqrt(2*(-0.5) + 5)
      have h8 : Real.sqrt (2 * (-0.5 : ℝ) + 5) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h8]
      norm_num
    constructor
    · -- 2 * (-0.5) + 5 ≥ 0
      norm_num
    constructor
    · -- 2 * (-0.5) + 5 ≥ 0
      norm_num
    · -- 2 * (-0.5) + 5 ≥ 0
      norm_num