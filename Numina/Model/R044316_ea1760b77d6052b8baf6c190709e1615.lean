import Mathlib
open Real

theorem algebra_608928 (A C x: ℝ) (ha: A > 0) (hc: C> 0) (hx: x> 0) (hp: A*C - 2 + 2*A*x ≥ 0) (h: sqrt (2 + A*C + 2*C*x) + sqrt (A*C - 2 + 2*A*x)  = sqrt (2*(A+C)*x + 2*A*C)) : x = (2-A*C)/(2*A):= by 
  have h1 : (sqrt (2 + A*C + 2*C*x) + sqrt (A*C - 2 + 2*A*x)) ^ 2 = (sqrt (2*(A+C)*x + 2*A*C)) ^ 2 := by 
    rw [h]
  have h2 : (sqrt (2 + A*C + 2*C*x) + sqrt (A*C - 2 + 2*A*x)) ^ 2 =
      (sqrt (2 + A*C + 2*C*x)) ^ 2 + (sqrt (A*C - 2 + 2*A*x)) ^ 2 + 2 * (sqrt (2 + A*C + 2*C*x) * sqrt (A*C - 2 + 2*A*x)) := by ring
  have h3 : (sqrt (2*(A+C)*x + 2*A*C)) ^ 2 = 2*(A+C)*x + 2*A*C := by 
    apply Real.sq_sqrt
    positivity 
  rw [h2, h3] at h1 
  have h11 : (sqrt (2 + A*C + 2*C*x)) ^ 2 = 2 + A*C + 2*C*x := by 
    apply Real.sq_sqrt 
    positivity 
  have h12 : (sqrt (A*C - 2 + 2*A*x)) ^ 2 = A*C - 2 + 2*A*x := by 
    apply Real.sq_sqrt 
    linarith 
  rw [h11, h12] at h1 
  have eq1 : sqrt (2 + A*C + 2*C*x) * sqrt (A*C - 2 + 2*A*x) = 0 := by 
    nlinarith [sq_nonneg (sqrt (2 + A*C + 2*C*x) - sqrt (A*C - 2 + 2*A*x))]
  have h41 : sqrt (2 + A*C + 2*C*x) * sqrt (A*C - 2 + 2*A*x) = 0 := eq1 
  cases' (mul_eq_zero.1 h41) with h42 h43 
  · -- h42 : sqrt (2 + A*C + 2*C*x) = 0
    -- lead to contradiction by 2+ AC +2 C x=0 is 2+pos term=0
    have h421 : sqrt (2 + A*C + 2*C*x) = 0 := h42 
    have h422 : 2 + A*C + 2*C*x = 0 := by 
      calc 
        2 + A*C + 2*C*x = (sqrt (2 + A*C + 2*C*x)) ^ 2 := by 
          rw [Real.sq_sqrt] 
          positivity 
        _ = 0 ^ 2 := by 
          rw [h421]
        _ = (0 : ℝ) := by 
          norm_num
    nlinarith 
  · -- h43 : sqrt (A*C - 2 + 2*A*x) = 0.
    have h431 : sqrt (A*C - 2 + 2*A*x) = 0 := h43 
    have h432 : A*C - 2 + 2*A*x = 0 := by 
      calc 
        A*C - 2 + 2*A*x = (sqrt (A*C - 2 + 2*A*x)) ^ 2 := by 
          rw [Real.sq_sqrt] 
          linarith 
        _ = 0 ^ 2 := by 
          rw [h431] 
        _ = (0 : ℝ) := by 
          norm_num 
    have h5 : x = (2 - A*C)/(2*A) := by 
      have : A*C + 2*A*x = (2 : ℝ) := by linarith 
      have : A*(C + 2*x) = (2 : ℝ) := by 
        linarith 
      have h5 : x = (2 - A*C)/(2*A) := by 
        field_simp at this ⊢
        nlinarith 
      linarith 
    field_simp at h5 ⊢ 
    <;> nlinarith