import Mathlib

open Real

theorem algebra_13493 {x : ℝ} (hx : x > 0) : logb 2 x + logb 4 x = 6 ↔ x = 16 := by
  constructor
  · -- Assume $\log_2 x + \log_4 x = 6$, prove $x = 16$
    intro h
    -- $\log_4 x = \log_2 x / 2$ because $\log_4 x = \frac{\ln x}{\ln 4} = \frac{\ln x}{2 \ln 2} = \frac{1}{2} \cdot \log_2 x$
    have h1 : logb 4 x = logb 2 x / 2 := by
      have h2 : logb 4 x = (Real.log x) / (Real.log 4) := by field_simp [logb]
      have h3 : logb 2 x = (Real.log x) / (Real.log 2) := by field_simp [logb]
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        calc
          Real.log 4 = Real.log (2^2) := by norm_num
          _ = 2 * Real.log 2 := by simp [Real.log_pow]
      rw [h2, h4, h3]
      <;> ring_nf <;> field_simp <;> try linarith
    rw [h1] at h
    have h5 : logb 2 x = 4 := by
      -- solve the equation $\frac{3}{2} \cdot \log_2 x = 6 \to \log_2 x = 4$
      linarith
    have h6 : x = 16 := by
      have h55 : logb 2 x = 4 := h5
      -- $\log_2 x = 4 \implies x = 2^4 = 16$
      have h7 : x = (2 : ℝ) ^ (logb 2 x : ℝ) := by
        rw [Real.rpow_logb]
        all_goals
          try { linarith }
          all_goals { norm_num }
      rw [h55] at h7
      norm_num at h7 ⊢
      all_goals linarith
    linarith
  · -- Assume $x = 16$, prove $\log_2 x + \log_4 x = 6$
    intro h
    rw [h]
    -- $\log_2 16 = 4$ because $2^4 = 16$
    have h1 : logb 2 (16 : ℝ) = 4 := by
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    -- $\log_4 16 = 2$ because $4^2 = 16$
    have h2 : logb 4 (16 : ℝ) = 2 := by
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    -- $4 + 2 = 6$
    rw [h1, h2]
    all_goals norm_num
    <;> try { linarith }