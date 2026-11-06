import Mathlib

open Real

theorem inequalities_242402 :
    logb 2015 2017 > (∑ i in Finset.range 2016, logb 2015 (i + 1)) / 2016 := by

  have h4 : ∀ i : ℕ, i ∈ Finset.range 2016 → logb 2015 (i + 1) ≤ logb 2015 2016 := by
    intro i hi
    have h5 : i < 2016 := by
      simpa using hi
    have h7 : i + 1 ≤ 2016 := by
      omega
    have h8 : (i + 1 : ℝ) ≤ (2016 : ℝ) := by
      exact_mod_cast h7
    have h9 : logb 2015 (i + 1) ≤ logb 2015 2016 := by
      apply logb_le_logb_of_le
      all_goals
        have h4 : (i + 1 : ℝ) > 0 := by
          nlinarith
        have h5 : (2016 : ℝ) > 0 := by
          nlinarith
        all_goals
          nlinarith
        all_goals
          nlinarith
    simpa using h9

  have h10 : (∑ i in Finset.range 2016, logb 2015 (i + 1)) ≤ 2016 * (logb 2015 2016) := by
    calc
      (∑ i in Finset.range 2016, logb 2015 (i + 1))
          ≤ ∑ i in Finset.range 2016, (logb 2015 2016) := by
            apply Finset.sum_le_sum
            intro i hi
            have h4' : logb 2015 (i + 1) ≤ logb 2015 2016 := h4 i hi
            linarith
      _ = 2016 * (logb 2015 2016) := by
        simp [Finset.sum_const, Finset.card_range]
        <;> ring_nf <;> linarith

  have h11 : logb 2015 2017 > logb 2015 2016 := by
    apply logb_lt_logb
    all_goals
      norm_num

  have h14 : (logb 2015 2017 : ℝ) * (2016 : ℝ) > (logb 2015 2016 : ℝ) * (2016 : ℝ) := by
    nlinarith [h11]

  have h15 : (logb 2015 2017 : ℝ) * (2016 : ℝ) > (∑ i in Finset.range 2016, logb 2015 (i + 1)) := by
    nlinarith [h14, h10]

  have h16 : (logb 2015 2017 : ℝ) > (∑ i in Finset.range 2016, logb 2015 (i + 1)) / 2016 := by
    linarith
  exact_mod_cast h16