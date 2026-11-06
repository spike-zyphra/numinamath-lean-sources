import Mathlib

open Real

theorem inequalities_190303 (x : ℝ) (hx : x > -1) : logb 4 (x + 7) > logb 2 (x + 1) ↔ x ∈ Set.Ioo (-1) 2 := by
  constructor
  · -- Prove the forward direction: if $\log_{4}(x+7) > \log_{2}(x+1)$, then $x \in (-1, 2)$
    intro h
    have h1 : logb 4 (x + 7) = (logb 2 (x + 7)) / 2 := by
      have h2 : logb 4 (x + 7) = logb 2 (x + 7) / logb 2 (4 : ℝ) := by 
        field_simp [logb]
        all_goals linarith
      have h3 : logb 2 (4 : ℝ) = 2 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
      rw [h2, h3]
    rw [h1] at h
    have h2 : logb 2 (x + 7) > 2 * logb 2 (x + 1) := by 
      linarith 
    -- Now convert $\log_2(x + 7) > 2 \cdot \log_2(x + 1)$ to the original form:
    have h3 : logb 2 (x + 7) > logb 2 ((x + 1) ^ 2) := by 
      have h4 : logb 2 ((x + 1) ^ 2) = 2 * logb 2 (x + 1) := by 
        simp [logb_pow]
      rw [h4] 
      linarith 
    -- Since logarithm base 2 is strictly increasing, this implies $x + 7 > (x + 1) ^2$.
    have h4 : x + 7 > (x + 1) ^ 2 := by
      by_contra h7
      push_neg at h7 
      have h8 : (x + 1) ^ 2 ≥ x + 7 := by linarith 
      have h9 : logb 2 ((x + 1) ^ 2) ≥ logb 2 (x + 7) := by 
        apply Real.logb_le_logb_of_le 
        all_goals 
          nlinarith 
      linarith 
    have h5 : (x + 1) ^ 2 < x + 7 := by linarith 
    -- Solving $x^2 + x - 6 < 0$ gives $-3 < x < 2$. Combined with the domain $x > -1$ we get $-1 < x < 2$
    have h6 : x ^ 2 + x - 6 < 0 := by 
      nlinarith 
    have h7 : x < 2 := by 
      nlinarith 
    exact ⟨hx, h7⟩ 
  · -- Prove the reverse direction: if $x \in (-1, 2)$, then $\log_{4}(x+7) > \log_{2}(x+1)$
    rintro ⟨h1, h2⟩ 
    have h1' : logb 4 (x + 7) = (logb 2 (x + 7)) / 2 := by
      have h2 : logb 4 (x + 7) = logb 2 (x + 7) / logb 2 (4 : ℝ) := by 
        field_simp [logb]
        all_goals linarith 
      have h3 : logb 2 (4 : ℝ) = 2 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      rw [h2, h3]
    have h2 : logb 2 (x + 7) > 2 * logb 2 (x + 1) := by 
      have h3 : x + 7 > (x + 1) ^ 2 := by 
        nlinarith 
      have h4 : logb 2 (x + 7) > logb 2 ((x + 1) ^ 2) := by 
        apply Real.logb_lt_logb 
        all_goals 
          nlinarith
      have h5 : logb 2 ((x + 1) ^ 2) = 2 * logb 2 (x + 1) := by 
        simp [logb_pow]
      linarith [h4, h5]
    have h3 : logb 4 (x + 7) > logb 2 (x + 1) := by 
      rw [h1']
      linarith 
    linarith