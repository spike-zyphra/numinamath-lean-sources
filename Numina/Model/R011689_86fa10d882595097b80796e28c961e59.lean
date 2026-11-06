import Mathlib

open Real

theorem algebra_160158 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) :
    (1 - a ^ 2) / (((1 - a * sqrt a) / (1 - sqrt a) + sqrt a) * ((1 + a * sqrt a) / (1 + sqrt a) - sqrt a)) - 1 = 2 * a / (1 - a) := by
  rcases ha with ⟨ha, ha1⟩
  have h1 : 0 < a := by linarith
  have h2 : sqrt a > 0 := by 
    apply Real.sqrt_pos.mpr 
    linarith
  have h4 : (sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
  have h6 : 1 - sqrt a ≠ 0 := by
    by_contra h7
    have h8 : sqrt a = 1 := by linarith 
    have h9 : a = 1 := by
      calc
        a = (sqrt a) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = 1 ^ 2 := by
          rw [h8]
        _ = 1 := by 
          norm_num 
    contradiction 
  have h7 : 1 + sqrt a ≠ 0 := by
    have h7 : sqrt a > 0 := h2
    nlinarith 
  have eq1 : (1 - a * sqrt a) / (1 - sqrt a) + sqrt a = 1 + 2 * sqrt a + a := by
    have h8 : 1 - sqrt a ≠ 0 := h6
    field_simp [h8, h4]
    <;> nlinarith [sq_nonneg (sqrt a - 1), sq_nonneg (a - 1), Real.sqrt_nonneg a, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg a)]
  have eq2 : (1 + a * sqrt a) / (1 + sqrt a) - sqrt a = 1 - 2 * sqrt a + a := by
    have h8 : 1 + sqrt a ≠ 0 := h7 
    field_simp [h8, h4]
    <;> nlinarith [sq_nonneg (sqrt a + 1), sq_nonneg (a - 1), Real.sqrt_nonneg a, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg a)]
  have eq3 : ((1 - a * sqrt a) / (1 - sqrt a) + sqrt a) * ((1 + a * sqrt a) / (1 + sqrt a) - sqrt a) = (1 - a) ^ 2 := by
    rw [eq1, eq2]
    nlinarith [sq_nonneg (sqrt a), Real.sqrt_nonneg a, h4, sq_nonneg (sqrt a - 1)]
  rw [eq3]
  have h8 : (1 - a) ≠ 0 := by
    intro h9
    apply ha1
    linarith
  field_simp [h8]
  <;> nlinarith [sq_nonneg (1 - a), sq_nonneg (a - 1), Real.sqrt_nonneg a, sq_nonneg (sqrt a - 1), h4]