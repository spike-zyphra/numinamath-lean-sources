import Mathlib

open Real Set

lemma lemma_1 {x : ℝ} (hx : 1 < x) :
    logb x (x + 1) > logb (x + 1) (x + 2) := by
  have h1 : logb x (x + 1) = (log (x + 1) ) / (log x) := by
    field_simp [logb]
  have h2 : logb (x + 1) (x + 2) = (log (x + 2) ) / (log (x + 1) ) := by
    field_simp [logb]
  rw [h1, h2]
  have hx2 : x + 1 > 1 := by linarith
  have hx3 : x + 2 > 1 := by nlinarith
  have h3 : log x > 0 := by
    apply log_pos
    linarith
  have h4 : log (x + 1) > 0 := by
    apply log_pos
    linarith
  have h5 : log (x + 2) > 0 := by
    apply log_pos
    linarith
  have h6 : (log (x + 1) ) ^ 2 > (log x) * (log (x + 2) ) := by
    have h7 : (log (x + 1) ) ^ 2 > (log x) * (log (x + 2) ) := by
      have h9 : (x + 1: ℝ) ^ 2 > (x : ℝ) * (x + 2 : ℝ) := by
        nlinarith
      have h10 : log ((x + 1 : ℝ) ^ 2) > log ((x : ℝ) * (x + 2 : ℝ) ) := by
        have h9' : (x + 1 : ℝ) ^ 2 > (x : ℝ) * (x + 2 : ℝ) := h9
        have h11 : (x : ℝ) * (x + 2 : ℝ) > 0 := by
          nlinarith
        have h12 : (x + 1 : ℝ) ^ 2 > 0 := by
          nlinarith
        have h13 : log ((x : ℝ) * (x + 2 : ℝ)) = log (x : ℝ) + log (x + 2 : ℝ) := by
          rw [log_mul (by positivity) (by positivity)]
        have h14 : log ((x + 1 : ℝ) ^ 2) = 2 * log (x + 1 : ℝ) := by
          simp [log_pow]
        -- We know that (x+1)^2 > x(x+2), so we can apply strict monotonicity of logarithm
        -- It's a bit complicated to use log_lt_log_iff here because of the direction
        have h15 : (x : ℝ) * (x + 2 : ℝ) < (x + 1 : ℝ) ^ 2 := by nlinarith
        have h16 : log ((x : ℝ) * (x + 2 : ℝ)) < log ((x + 1 : ℝ) ^ 2) := by
          apply Real.log_lt_log
          all_goals
            nlinarith
        linarith [h16, h13, h14]
      have h11 : log ((x + 1 : ℝ) ^ 2) = 2 * log (x + 1 : ℝ) := by
        simp [log_pow]
        all_goals linarith
      have h12 : log ((x : ℝ) * (x + 2 : ℝ) ) = log (x : ℝ) + log (x + 2 : ℝ) := by
        rw [log_mul (by linarith) (by linarith)]
      have h13 : 2 * log (x + 1 : ℝ) > log (x : ℝ) + log (x + 2 : ℝ) := by
        nlinarith [h10, h11, h12]
      nlinarith [mul_pos h3 h4, mul_pos h4 h5, mul_pos h3 h5, sq_nonneg (log (x + 1) - log x), sq_nonneg (log (x + 1) - log (x + 2)), sq_nonneg (log (x + 1) - (log x + log (x + 2)) / 2)]
    linarith
  have h7 : (log (x + 1) ) / (log x) > (log (x + 2) ) / (log (x + 1) ) := by
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  linarith


theorem algebra_608518 :
  logb 2008 2009 > logb 2009 2010 := by
  have h1 : 1 < (2008 : ℝ) := by norm_num 
  have h4 := lemma_1 h1
  norm_num at h4 ⊢
  all_goals try linarith