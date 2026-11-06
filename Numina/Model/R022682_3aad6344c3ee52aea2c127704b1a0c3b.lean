import Mathlib

theorem inequalities_103493 (x : ℝ) (hx : 0 ≤ x) :
    1 + x^2018 ≥ 4 * x^2017 / (1 + x^2016) := by
  have h1 : 0 < 1 + x ^ 2016 := by positivity
  have h3 : (1 + x ^ 2016) * (1 + x ^ 2018) ≥ 4 * x ^ 2017 := by
    have h5 : x ^ 2016 + x ^ 2018 ≥ 2 * x ^ 2017 := by
      have h6 : x ^ 2018 + x ^ 2016 - 2 * x ^ 2017 ≥ 0 := by
        have h7 : x ^ 2018 + x ^ 2016 - 2 * x ^ 2017 = x ^ 2016 * (x ^ 2 - 2 * x + 1) := by
          ring_nf
        rw [h7] at *
        have h12 : x ^ 2 - 2 * x + 1 ≥ 0 := by
          have h13 : x ^ 2 - 2 * x + 1 = (x - 1) ^ 2 := by
            ring
          rw [h13] at *
          positivity
        have h14 : x ^ 2016 ≥ 0 := by
          have h_nonneg : 0 ≤ x := hx
          have h2016_nonneg : x ^ 2016 ≥ 0 := by
            apply pow_nonneg
            exact h_nonneg
          exact h2016_nonneg
        have h15 : x ^ 2016 * (x ^ 2 - 2 * x + 1) ≥ 0 := by
          apply mul_nonneg
          exact h14
          all_goals nlinarith
        linarith
      linarith
    have h7 : 1 + x ^ 4034 ≥ 2 * x ^ 2017 := by
      have h8 : 1 + x ^ 4034 - 2 * x ^ 2017 ≥ 0 := by
        have h9 : 1 + x ^ 4034 - 2 * x ^ 2017 = (x ^ 2017 - 1) ^ 2 := by
          ring
        rw [h9] at *
        have h4670 : (x ^ 2017 - 1) ^ 2 ≥ 0 := by
          exact sq_nonneg (x ^ 2017 - 1)
        linarith
      linarith
    have h8 : 1 + x ^ 2016 + x ^ 2018 + x ^ 4034 ≥ 4 * x ^ 2017 := by
      nlinarith [sq_nonneg (x ^ 1008 * (x ^ 2 - 1)), sq_nonneg (x ^ 1008 * (x ^ 2)), sq_nonneg (x ^ 2016 * (x ^ 2 - 1)), sq_nonneg (x ^ 2017 - x ^ 1008)]
    have h13 : (1 + x ^ 2016) * (1 + x ^ 2018) = 1 + x ^ 2016 + x ^ 2018 + x ^ 4034 := by
      ring
    nlinarith
  have h9 : (1 + x ^ 2018) ≥ 4 * x ^ 2017 / (1 + x ^ 2016) := by
    have h7 : (1 + x ^ 2016) * (1 + x ^ 2018) ≥ 4 * x ^ 2017 := h3
    have h8 : (1 + x ^ 2016) > 0 := by positivity
    have h12 : (1 + x ^ 2018) ≥ 4 * x ^ 2017 / (1 + x ^ 2016) := by
      apply (div_le_iff₀ (by linarith)).mpr
      linarith
    linarith
  linarith