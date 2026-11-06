import Mathlib

theorem algebra_196716 {x y : ℝ} : (x^2 - 6 * Real.sqrt (3 - 2 * x) - y + 11 = 0) ∧ (y^2 - 4 * Real.sqrt (3 * y - 2) + 4 * x + 16 = 0) ↔ (x = -3 ∧ y = 2) := by
  constructor
  · -- Assume the conjunction of the equations, prove (x = -3 ∧ y = 2)
    rintro ⟨h₁, h₂⟩
    have h3 : 3 - 2 * x ≥ 0 := by
      by_contra h
      push_neg at h
      have h4 : Real.sqrt (3 - 2 * x) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
      rw [h4] at h₁
      nlinarith [Real.sqrt_nonneg (3 * y - 2), Real.sq_sqrt (show 0 ≤ (3 * y - 2 : ℝ) by
        by_contra h
        push_neg at h
        have h5 : Real.sqrt (3 * y - 2) = 0 := by
          rw [Real.sqrt_eq_zero']
          nlinarith
        rw [h5] at h₂
        nlinarith
      )
      ]
    have h4 : 3 * y - 2 ≥ 0 := by
      by_contra h
      push_neg at h
      have h5 : Real.sqrt (3 * y - 2) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
      rw [h5] at h₂
      nlinarith [Real.sqrt_nonneg (3 - 2 * x), Real.sq_sqrt (show 0 ≤ (3 - 2 * x : ℝ) by linarith)
      ]
    -- From first eq, take sqrt
    have h7 : Real.sqrt (3 - 2 * x) ≥ 0 := Real.sqrt_nonneg (3 - 2 * x)
    have h8 : Real.sqrt (3 * y - 2) ≥ 0 := Real.sqrt_nonneg (3 * y - 2)
    have eq1 : (x ^ 2 + 11 - y) = 6 * Real.sqrt (3 - 2 * x) := by linarith
    have eq2 : (x ^ 2 + 11 - y) ^ 2 = 36 * (3 - 2 * x) := by
      calc
        (x ^ 2 + 11 - y) ^ 2 = (6 * Real.sqrt (3 - 2 * x)) ^ 2 := by rw [eq1]
        _ = 36 * (Real.sqrt (3 - 2 * x) ^ 2) := by ring
        _ = 36 * (3 - 2 * x) := by
          rw [Real.sq_sqrt]
          linarith
    -- From second eq, take sqrt
    have eq3 : (y ^ 2 + 4 * x + 16) = 4 * Real.sqrt (3 * y - 2) := by linarith
    have eq4 : (y ^ 2 + 4 * x + 16) ^ 2 = 16 * (3 * y - 2) := by
      calc
        (y ^ 2 + 4 * x + 16) ^ 2 = (4 * Real.sqrt (3 * y - 2)) ^ 2 := by rw [eq3]
        _ = 16 * (Real.sqrt (3 * y - 2) ^ 2) := by ring
        _ = 16 * (3 * y - 2) := by
          rw [Real.sq_sqrt]
          linarith
    have h9 : (x + 3) ^ 2 + (y - 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 3), sq_nonneg (y - 2), Real.sqrt_nonneg (3 - 2 * x), Real.sqrt_nonneg (3 * y - 2),
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 - 2 * x by linarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 * y - 2 by linarith),
        sq_nonneg (Real.sqrt (3 - 2 * x) - 3), sq_nonneg (Real.sqrt (3 * y - 2) - 2)]
    have hx1 : x + 3 = 0 := by
      nlinarith [h9]
    have hy1 : y - 2 = 0 := by
      nlinarith [h9]
    constructor
    · linarith
    · linarith
  · -- Assume (x = -3 ∧ y = 2), prove the conjunction of the equations
    rintro ⟨rfl, rfl⟩
    constructor
    · -- First equation
      have h3 : Real.sqrt (3 - 2 * (-3 : ℝ)) = (3 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h3]
      norm_num
    · -- Second equation
      have h4 : Real.sqrt (3 * (2 : ℝ) - 2) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h4]
      norm_num