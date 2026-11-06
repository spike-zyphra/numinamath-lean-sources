import Mathlib
set_option maxRecDepth 200000
set_option exponentiation.threshold 200000

open Real

/- Task 1. Prove the inequality


$$

\log _{2016} 2018>\frac{\log _{2016} 1+\log _{2016} 2+\ldots+\log _{2016} 2017}{2017}

$$
 -/


theorem inequalities_242589 : logb 2016 2018 > ∑ i ∈ Finset.range 2017, logb 2016 (i + 1) / 2017 := by
  --We first show 2018^2017 > 1 * 2 * ⋯ * 2017.
  have H0 : (∏ i ∈ Finset.range 2017, (i + 1) : ℝ) < ((2018 : ℝ)^(2017 : ℕ))  := by
    norm_cast

  --Therefore we get the following inequality of logarithms in base 2016.
  have H1 : logb 2016 (2018^2017) > logb 2016 (∏ i ∈ Finset.range 2017, (i + 1)) := by
    have H10 : (1 : ℝ) < (2016 : ℝ) := by norm_num
    have H11 : (0 : ℝ) < (∏ i ∈ Finset.range 2017, (i + 1) : ℝ) := by norm_num
    exact Real.logb_lt_logb H10 H11 H0

  --We now expand the RHS of H1 as follows.
  have H2 : logb 2016 (∏ i ∈ Finset.range 2017, (i + 1)) = ∑ i ∈ Finset.range 2017, logb 2016 (i + 1) := by
    refine logb_prod (Finset.range 2017) (fun i ↦ ↑i + 1) ?_
    intro x
    intro h
    positivity

  --We use log-power-rule for the LHS of H1.
  have H3 : logb 2016 (2018^2017) = 2017 * logb 2016 (2018) := by
     have h2016 : 0 < 2016 := by norm_num
     have h2018 : 0 < 2018 := by norm_num
     rw [Real.logb_pow]
     norm_cast

  --Thus we get the following.
  have H4 : 2017 * logb 2016 (2018) >  ∑ i ∈ Finset.range 2017, logb 2016 (i + 1) := by
    linarith

  --Now we divide both sides by 2017 and as 2017>0 the inequality retains.
  have H5 : logb 2016 (2018) >  ∑ i ∈ Finset.range 2017, logb 2016 (i + 1) / 2017 := by
    have h2017_pos : (2017 : ℝ) > 0 := by norm_num
    have h6 : ∑ i in Finset.range 2017, logb 2016 (i + 1 : ℝ) / 2017 =
      (∑ i in Finset.range 2017, logb 2016 (i + 1 : ℝ)) / 2017 := by
      rw [Finset.sum_div]
    rw [h6]
    have h7 : (2017 : ℝ) > 0 := by norm_num
    have h8 : logb 2016 (2018 : ℝ) > (∑ i in Finset.range 2017, logb 2016 (i + 1 : ℝ)) / (2017 : ℝ) := by
      linarith
    linarith

  exact H5