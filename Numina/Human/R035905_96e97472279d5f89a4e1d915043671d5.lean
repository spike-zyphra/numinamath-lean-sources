import Mathlib
open Real
/- 9.181. $\log _{0.3} \log _{6} \frac{x^{2}+x}{x+4}<0$. -/
theorem inequalities_171051 (x : ℝ) (hx : x ≠ -4) (hx1 : logb 6 ((x ^ 2 + x) / (x + 4)) > 0) (hx2 : (x ^ 2 + x) / (x + 4) > 0) : logb 0.3 (logb 6 ((x^2 + x) / (x + 4))) < 0 ↔
x ∈ Set.Ioo (-4) (-3) ∪ Set.Ioi 8:= by
  constructor
  -- Forward direction: proving that if the inequality holds, then x is in the specified set
  .
    intro h
    -- Rewrite using the logarithm division property
    rw [←Real.log_div_log] at h
    norm_num at h
    -- Prove that log(3/10) < 0
    have h1 : log (3 / 10) < 0:= by
      have h1 : 0 < (3 : ℝ) / 10:= by linarith
      have h2 : (3 : ℝ) / 10 < 1:= by norm_num
      exact log_neg h1 h2
    -- Rewrite the inequality using field simplification
    rw [show log (logb 6 ((x ^ 2 + x) / (x + 4))) / log (3 / 10) = log (logb 6 ((x ^ 2 + x) / (x + 4))) * (1 / log (3 / 10)) by field_simp] at h
    -- Since 1/log(3/10) < 0, we can deduce that log(logb 6 ((x^2+x)/(x+4))) > 0
    replace h1 : 1 / log (3 / 10) < 0:= by exact one_div_neg.mpr h1
    replace h : log (logb 6 ((x ^ 2 + x) / (x + 4))) > 0:= by exact (pos_iff_neg_of_mul_neg h).mpr h1
    -- This implies that logb 6 ((x^2+x)/(x+4)) > 1
    replace h : logb 6 ((x ^ 2 + x) / (x + 4)) > 1:= by exact (Real.log_pos_iff hx1).1 h
    -- Rewrite using logarithm properties
    rw [←Real.log_div_log] at h
    -- Prove that log 6 > 0
    replace h1 : log 6 > 0:= by
      have h2 : (6 : ℝ) > 1:= by norm_num
      exact log_pos h2
    -- Deduce that log((x^2+x)/(x+4)) > log 6
    replace h : log ((x ^ 2 + x) / (x + 4)) > log 6:= by exact (one_lt_div h1).mp h
    -- This implies (x^2+x)/(x+4) > 6
    replace h : (x ^ 2 + x) / (x + 4) > 6:= by
      have h2 : (6 : ℝ) > 0:= by norm_num
      exact (log_lt_log_iff h2 hx2).mp h
    -- Simplify to (x^2+x)/(x+4) - 6 > 0
    replace h : (x ^ 2 + x) / (x + 4) - 6 > 0:= by linarith
    -- Prove that x+4 ≠ 0
    have gx : x + 4 ≠ 0:= by
      by_contra H
      replace H : x = -4:= by linarith
      trivial
    -- Rewrite the inequality in factored form
    rw [show (x ^ 2 + x) / (x + 4) - 6 = ((x + 3) * (x - 8)) / (x + 4) by field_simp ; linarith] at h
    clear gx hx1 hx2
    -- Case analysis: either x < -4 or x > -4
    replace hx : x < -4 ∨ x > -4:= by exact lt_or_gt_of_ne hx
    rcases hx with hx | hx
    -- Case 1: x < -4
    .
      have g1 : x + 4 < 0:= by linarith
      have g2 : x + 3 < 0:= by linarith
      have g3 : x - 8 < 0:= by linarith
      replace g2 : (x + 3) * (x - 8) > 0:= by exact mul_pos_of_neg_of_neg g2 g3
      replace g2 : (x + 3) * (x - 8) / (x + 4) < 0:= by exact div_neg_of_pos_of_neg g2 g1
      linarith
    -- Case 2: x > -4
    .
      -- Subcase: x < -3
      by_cases hx1 : x < -3
      .
        simp
        left
        exact ⟨hx, hx1⟩
      -- Subcase: x ≥ -3
      .
        simp at hx1
        -- Further subcase: x > 8
        by_cases hx2 : x > 8
        .
          simp
          right
          exact hx2
        -- Final subcase: -3 ≤ x ≤ 8
        .
          simp at hx2
          clear hx
          have g1 : x - 8 ≤ 0:= by linarith
          have g2 : x + 3 ≥ 0:= by linarith
          have g3 : x + 4 > 0:= by linarith
          replace g2 : (x + 3) * (x - 8) ≤ 0:= by exact mul_nonpos_of_nonneg_of_nonpos g2 g1
          -- Show that the fraction is non-positive
          replace g2 : (x + 3) * (x - 8) / (x + 4) ≤ 0:= by
            rw [show (x + 3) * (x - 8) / (x + 4) = (x + 3) * (x - 8) * (1 / (x + 4)) by field_simp]
            replace g3 : 1 / (x + 4) ≥ 0:= by positivity
            exact mul_nonpos_of_nonpos_of_nonneg g2 g3
          linarith
  -- Reverse direction: proving that if x is in the specified set, then the inequality holds
  .
    intro h
    simp at h
    rcases h with h | h
    -- Case 1: x ∈ (-4,-3)
    .
      rcases h with ⟨h1, h2⟩
      replace h1 : x + 4 > 0:= by linarith
      replace h2 : x + 3 < 0:= by linarith
      -- Prove that (x^2+x)/(x+4) > 6
      have h3 : (x ^ 2 + x) / (x + 4) > 6:= by
        suffices x ^ 2 + x > 6 * (x + 4) by exact (lt_div_iff₀ h1).mpr this
        suffices (x + 3) * (x - 8) > 0 by linarith
        have h3 : x - 8 < 0:= by linarith
        exact mul_pos_of_neg_of_neg h2 h3
      -- This implies logb 6 ((x^2+x)/(x+4)) > 1
      replace h3 : logb 6 ((x ^ 2 + x) / (x + 4)) > 1:= by
        have h4:= Real.logb_lt_logb (show 1 < 6 by norm_num) (show 0 < 6 by norm_num) h3
        rw [show logb 6 6 = 1 by norm_num] at h4
        exact h4
      set t:= logb 6 ((x ^ 2 + x) / (x + 4))
      clear_value t
      -- Rewrite the target inequality using logarithm properties
      rw [←Real.log_div_log]
      norm_num
      -- Prove that log(3/10) < 0
      have h4 : log (3 / 10) < 0:= by
        have h1 : 0 < (3 : ℝ) / 10:= by linarith
        have h2 : (3 : ℝ) / 10 < 1:= by norm_num
        exact log_neg h1 h2
      -- Prove that log t > 0
      have h5 : log t > 0:= by exact (log_pos_iff hx1).mpr h3
      -- Conclude that log t / log(3/10) < 0
      exact div_neg_of_pos_of_neg h5 h4
    -- Case 2: x > 8
    .
      have h1 : x + 4 > 0:= by linarith
      -- Prove that (x^2+x)/(x+4) > 6
      have h3 : (x ^ 2 + x) / (x + 4) > 6:= by
        suffices x ^ 2 + x > 6 * (x + 4) by exact (lt_div_iff₀ h1).mpr this
        suffices (x + 3) * (x - 8) > 0 by linarith
        have h3 : x - 8 > 0:= by linarith
        positivity
      -- This implies logb 6 ((x^2+x)/(x+4)) > 1
      replace h3 : logb 6 ((x ^ 2 + x) / (x + 4)) > 1:= by
        have h4:= Real.logb_lt_logb (show 1 < 6 by norm_num) (show 0 < 6 by norm_num) h3
        rw [show logb 6 6 = 1 by norm_num] at h4
        exact h4
      set t:= logb 6 ((x ^ 2 + x) / (x + 4))
      clear_value t
      -- Rewrite the target inequality using logarithm properties
      rw [←Real.log_div_log]
      norm_num
      -- Prove that log(3/10) < 0
      have h4 : log (3 / 10) < 0:= by
        have h1 : 0 < (3 : ℝ) / 10:= by linarith
        have h2 : (3 : ℝ) / 10 < 1:= by norm_num
        exact log_neg h1 h2
      -- Prove that log t > 0
      have h5 : log t > 0:= by exact (log_pos_iff hx1).mpr h3
      -- Conclude that log t / log(3/10) < 0
      exact div_neg_of_pos_of_neg h5 h4
