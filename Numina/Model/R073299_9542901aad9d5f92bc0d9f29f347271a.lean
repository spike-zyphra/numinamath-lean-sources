import Mathlib

theorem algebra_314117 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.sqrt a * (Real.sqrt a + 4 * Real.sqrt b) = 3 * Real.sqrt b * (Real.sqrt a + 2 * Real.sqrt b)) :
    (a + 6 * Real.sqrt (a * b) - 8 * b) / (2 * a - 3 * Real.sqrt (a * b) + 2 * b) = 2 := by
  have h1 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  have h2 : Real.sqrt a ^ 2 = a := by
    rw [Real.sq_sqrt]
    linarith
  have h3 : Real.sqrt b ^ 2 = b := by
    rw [Real.sq_sqrt]
    linarith
  have eq1 : Real.sqrt a * (Real.sqrt a + 4 * Real.sqrt b) =
    Real.sqrt a ^ 2 + 4 * Real.sqrt a * Real.sqrt b := by ring
  have eq2 : 3 * Real.sqrt b * (Real.sqrt a + 2 * Real.sqrt b) =
    3 * Real.sqrt a * Real.sqrt b + 6 * Real.sqrt b ^ 2 := by ring
  rw [eq1, eq2] at h
  have eq3 : a + 4 * Real.sqrt a * Real.sqrt b = 3 * Real.sqrt a * Real.sqrt b + 6 * b := by 
    rw [h2, h3] at h
    nlinarith
  have eq5 : Real.sqrt a = 2 * Real.sqrt b := by
    nlinarith [sq_nonneg (Real.sqrt a - 2 * Real.sqrt b), sq_nonneg (Real.sqrt b), Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have h6 : a = 4 * b := by
    have h7 : Real.sqrt a = 2 * Real.sqrt b := eq5
    have h8 : a = (2 * Real.sqrt b) ^ 2 := by
      calc
        a = Real.sqrt a ^ 2 := by rw [h2]
        _ = (2 * Real.sqrt b) ^ 2 := by rw [h7]
    rw [h8]
    have h9 : (2 * Real.sqrt b) ^ 2 = 4 * b := by
      have h11 : Real.sqrt b ^ 2 = b := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith [Real.sqrt_nonneg b]
    linarith [h9]
  have eq6 : Real.sqrt (a * b) = 2 * b := by
    rw [h1]
    have h10 : Real.sqrt a = 2 * Real.sqrt b := eq5
    rw [h10]
    have h11 : (2 * Real.sqrt b) * Real.sqrt b = 2 * (Real.sqrt b ^ 2) := by ring
    rw [h11]
    have h12 : Real.sqrt b ^ 2 = b := by 
      rw [Real.sq_sqrt]
      linarith
    nlinarith [Real.sqrt_nonneg b]
  have num_eq : a + 6 * Real.sqrt (a * b) - 8 * b = 8 * b := by
    rw [eq6]
    have h7 : a = 4 * b := h6
    linarith [h7, hb]
  have denom_eq : 2 * a - 3 * Real.sqrt (a * b) + 2 * b = 4 * b := by
    rw [eq6]
    have h7 : a = 4 * b := h6
    linarith [h7, hb]
  rw [num_eq, denom_eq]
  field_simp [hb.ne.symm]
  <;> nlinarith