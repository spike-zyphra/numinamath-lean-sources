import Mathlib
set_option exponentiation.threshold 10000
open Real

/- Task 1. Prove the inequality


$$

\log _{2017} 2019>\frac{\log _{2017} 1+\log _{2017} 2+\ldots+\log _{2017} 2018}{2018}

$$
 -/
theorem inequalities_242496 : logb 2017 2019 > ∑ i ∈ Finset.range 2018, logb 2017 (i + 1) / 2018 := by
  -- multiply both sides by 2018
  suffices 2018 * logb 2017 2019 > ∑ i ∈ Finset.range 2018, logb 2017 (i + 1) by rw [← Finset.sum_div]; linarith
  rw [← Real.logb_prod (hf:=by intro x hx; simp at hx; linarith)];
  conv_lhs =>
    calc 2018 * logb 2017 2019
    _ = (2018:ℕ) * logb 2017 (2019:ℝ) := by norm_cast
    _ = logb 2017 (2019 ^ 2018) := by rw [← Real.logb_pow]
  -- remove logs
  apply Real.logb_lt_logb (by norm_num) (by
    apply Finset.prod_pos; intro i hi; linarith
  )
  -- trivial if we consider that 2019^2018 is just a product of 2018 terms
  conv_rhs =>
    calc (2019:ℝ) ^ 2018
    _ = 2019 ^ 2018 := by norm_cast
    _ = ∏ i in Finset.range 2018, 2019 := by rw [Finset.prod_const]; simp;
  apply Finset.prod_lt_prod
  · intro i hi; linarith
  · intro i hi; simp at hi;
    norm_cast; linarith
  · use 0; simp