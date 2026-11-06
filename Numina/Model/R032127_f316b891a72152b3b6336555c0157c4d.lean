import Mathlib

open Real

theorem algebra_162584 {x y : ℝ} (hx : 0 ≤ 3 * x - y) :
    3 * x + sqrt (3 * x - y) + y = 6 ∧  9 * x ^ 2 + 3 * x - y - y ^ 2 = 36 ↔
    (x = 2 ∧ y = -3) ∨ (x = 6 ∧ y = -18) := by 
  constructor
  · -- Assume the system of equations holds, prove the solutions
    rintro ⟨h1, h2⟩
    have h3 : 0 ≤ 3 * x - y := hx
    have h4 : sqrt (3 * x - y) ≥ 0 := by positivity
    have h5 : sqrt (3 * x - y) ^ 2 = 3 * x - y := by
      rw [Real.sq_sqrt]
      linarith
    have h6 : 6 * x + sqrt (3 * x - y) - (sqrt (3 * x - y) ) ^ 2 = 6 := by 
      nlinarith [h1, h5]
    have h7 : 9 * x ^ 2 + (sqrt (3 * x - y)) ^ 2 - (3 * x - (sqrt (3 * x - y) ) ^ 2) ^ 2 = 36 := by 
      nlinarith [h2, h5]
    have h8 : (sqrt (3 * x - y) - 3) * (sqrt (3 * x - y) - 6) = 0 := by
      nlinarith [sq_nonneg (sqrt (3 * x - y) - 3), sq_nonneg (x - 2), sq_nonneg (x - 6), sq_nonneg (sqrt (3 * x - y) - 6)]
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case sqrt(3 * x - y) - 3 = 0
      have h11 : sqrt (3 * x - y) = 3 := by linarith
      have h12 : 3 * x - y = 9 := by 
        calc
          3 * x - y = (sqrt (3 * x - y)) ^ 2 := by
            rw [Real.sq_sqrt]
            linarith
          _ = 3 ^ 2 := by 
            rw [h11]
          _ = 9 := by norm_num
      have h13 : x = 2 := by 
        nlinarith [h11, h6]
      have h14 : y = -3 := by 
        nlinarith [h12, h13]
      left 
      exact ⟨h13, h14⟩
    · -- Case sqrt(3 * x - y) - 6 = 0
      have h11 : sqrt (3 * x - y) = 6 := by linarith
      have h12 : 3 * x - y = 36 := by 
        calc
          3 * x - y = (sqrt (3 * x - y)) ^ 2 := by
            rw [Real.sq_sqrt]
            linarith
          _ = 6 ^ 2 := by 
            rw [h11]
          _ = 36 := by norm_num
      have h13 : x = 6 := by 
        nlinarith [h11, h6]
      have h14 : y = -18 := by 
        nlinarith [h12, h13]
      right 
      exact ⟨h13, h14⟩
  · -- Assume the pairs, prove that they satisfy the system
    rintro (h | h)
    · -- First pair (2, -3)
      rcases h with ⟨hx1, hy1⟩
      constructor
      · -- Check the first equation
        rw [hx1, hy1]
        have h1 : sqrt (3 * (2 : ℝ) - (-3 : ℝ)) = 3 := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> linarith
        nlinarith [h1]
      · -- Check the second equation
        rw [hx1, hy1]
        norm_num
    · -- Second pair (6, -18)
      rcases h with ⟨hx2, hy2⟩
      constructor
      · -- Check the first equation
        rw [hx2, hy2]
        have h1 : sqrt (3 * (6 : ℝ) - (-18 : ℝ)) = 6 := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> linarith
        nlinarith [h1]
      · -- Check the second equation
        rw [hx2, hy2]
        norm_num