import Mathlib

open Real

/- For what value of x does log(√2) √x + log₂ x + log₄ x² + log₈ x³ + log₁₆ x⁴ =40?
(A) 8
(B) 16
(C) 32
(D) 256
(E) 1024 -/
theorem algebra_94227 {x : ℝ} (hx : 0 < x) :
logb (sqrt 2) (sqrt x) + logb 2 x + logb 4 (x ^ 2) + logb 8 (x ^ 3) + logb 16 (x ^ 4) = 40 ↔ x = 256 := by
  constructor
  --we prove that given the equation, then x=256 is a solution
  · intro h
    --reduce everything to the natural logarithm using logb_a (b)= log (b) / log (a)
    rw[← log_div_log, ← log_div_log, ← log_div_log, ← log_div_log, ← log_div_log] at h
    --find every log in terms of log 2 or log x and substitute in the equation
    have k2 : log √2 = (1/2: ℝ) * log 2 := by 
      calc
        log √2 = log (2^((1/2 :ℝ))) := by rw[← sqrt_eq_rpow]
        _ = 1/2 * log 2 := by 
          rw[log_rpow] 
          norm_num
    rw[k2] at h
    field_simp at h
    ring_nf at h
    have k0 : log √x = (1/2 : ℝ) * log x := by
      calc
        log √x = log (x^((1/2 :ℝ))) := by rw[← sqrt_eq_rpow]
        _ = 1/2 * log x := by 
          rw[log_rpow]
          exact hx
    have k3 : log 4 = 2 * log 2 := by
      calc 
        log 4 = log (2 ^ 2) := by norm_num
        _ = 2 * log 2 := by simp
    have k4 : log 8 = 3 * log 2 := by 
      calc 
        log 8 = log (2 ^ 3) := by norm_num
        _ = 3 * log 2 := by simp
    have k5 : log 16 = 4 * log 2 := by 
      calc 
        log 16 = log (2 ^ 4) := by norm_num
        _ = 4 * log 2 := by simp
    rw[k0, k3, k4, k5] at h
    field_simp at h
    ring_nf at h
    --solve the resulting equation algebaically until you gey log x = log 2 ^ something
    have hk := congrFun (congrArg HMul.hMul h) (1 / (120 * log 2 ^ 3))
    ring_nf at hk
    rw[mul_assoc, ← mul_pow] at hk
    norm_num at hk
    have jj : log 2 ^ 4 = log 2 * log 2 ^ 3 := by exact pow_succ' (log 2) 3
    rw[jj] at hk
    have hhk := congrFun (congrArg HMul.hMul hk) (1 / log 2)
    norm_num at hhk
    --exponentiate everithing and simplify via exp (log a) = a
    rw[← exp_eq_exp, exp_mul] at hhk
    rw[exp_log , exp_log] at hhk
    --solve the calculations left
    norm_num at hhk
    exact hhk
    norm_num
    exact hx
  --we prove that x=256 is a solution of the given equation
  · intro h
    --substitute 256
    rw[h]
    --reduce everything to the natural logarithm using logb_a (b)= log (b) / log (a)
    rw[← log_div_log, ← log_div_log, ← log_div_log, ← log_div_log, ← log_div_log]
    --find every log in terms of log 2 and substitute in the equation
    have k2 : log √2 = (1/2: ℝ) * log 2 := by 
      calc
        log √2 = log (2^((1/2 :ℝ))) := by rw[← sqrt_eq_rpow]
        _ = 1/2 * log 2 := by 
          rw[log_rpow] 
          norm_num
    rw[k2]
    field_simp
    ring_nf
    have k0 : log √256 = (1/2 : ℝ) * log 256 := by
      calc
        log √256 = log (256^((1/2 :ℝ))) := by rw[← sqrt_eq_rpow]
        _ = 1/2 * log 256 := by 
          rw[log_rpow] 
          norm_num
    have k1 : log 256 = 8 * log 2 := by
      calc
        log 256 = log (2 ^ 8) := by norm_num
        _ = 8 * log 2 := by simp
    have k3 : log 4 = 2 * log 2 := by
      calc 
        log 4 = log (2 ^ 2) := by norm_num
        _ = 2 * log 2 := by simp
    have k4 : log 8 = 3 * log 2 := by 
      calc 
        log 8 = log (2 ^ 3) := by norm_num
        _ = 3 * log 2 := by simp
    have k5 : log 16 = 4 * log 2 := by 
      calc 
        log 16 = log (2 ^ 4) := by norm_num
        _ = 4 * log 2 := by simp
    rw[k0, k1, k3, k4, k5]
    --finalize by solving the calculations by linear arithmetic
    ring_nf