import Mathlib
/-What is the equation of the oblique asymptote of the graph of (2 * x ^ 2 + 7 * x + 10) / (2 * x + 3) ?-/
theorem algebra_13599 (f : ℝ → ℝ) (hf : f = fun x => (2 * x ^ 2 + 7 * x + 10) / (2 * x + 3)) :
    ∀ ε > 0, ∃ x₁, ∀ x, x > x₁ → |f x - (x + 2)| < ε := by
    -- prove step by step
  intro ε hε
  use (4 / ε - 3) / 2
  intro x hx
  have h1 : 2 * x + 3 ≠ 0 := by
    by_contra h
    have : x = -3 / 2 := by linarith
    linarith [show x > -3 / 2 from by
      linarith [hx, show (4 / ε - 3) / 2 > -3 / 2 from by
        have h1 : ε > 0 := hε
        have h2 : (4 / ε - 3) / 2 > -3 / 2 := by
          have h3 : 4 / ε > 0 := by positivity
          linarith [h3]
        linarith]]
  have hfx : f x = (2 * x ^ 2 + 7 * x + 10) / (2 * x + 3) := by
    rw [hf]
  have h2 : |f x - (x + 2)| = 4 / |(2 * x + 3 : ℝ)| := by
    rw [hfx]
    have h3 : (2 * x + 3 : ℝ) ≠ 0 := h1
    have eq1 : (2 * x ^ 2 + 7 * x + 10 : ℝ) / (2 * x + 3) - (x + 2) = (4 : ℝ) / (2 * x + 3) := by
      field_simp [h3]
      ring
    rw [eq1]
    simp [abs_div, abs_of_pos]
    -- show some fundamental results
  have h3 : |(2 * x + 3 : ℝ)| > 4 / ε := by
    have h4 : (2 * x + 3 : ℝ) > 4 / ε := by
      have h5 : x > (4 / ε - 3) / 2 := hx
      linarith [h5]
    have h6 : (2 * x + 3 : ℝ) > 0 := by
      have h7 : x > (4 / ε - 3) / 2 := hx
      have h8 : x > -3 / 2 := by
        have h9 : (4 / ε - 3) / 2 > -3 / 2 := by
          have h10 : ε > 0 := hε
          have h11 : (4 / ε : ℝ) > 0 := by positivity
          linarith [h11]
        linarith [h7, h9]
      nlinarith
    rw [abs_of_pos h6]
    linarith [h4]
  have h4 : 4 / |(2 * x + 3 : ℝ)| < ε := by
    have h5 : |(2 * x + 3 : ℝ)| > 0 := by
      have h6 : (2 * x + 3 : ℝ) > 0 := by
        have h7 : x > (4 / ε - 3) / 2 := hx
        have h8 : x > -3 / 2 := by
          have h9 : (4 / ε - 3) / 2 > -3 / 2 := by
            have h10 : ε > 0 := hε
            have h11 : (4 / ε : ℝ) > 0 := by positivity
            linarith [h11]
          linarith [h7, h9]
        nlinarith
      have h7 : |(2 * x + 3 : ℝ)| = (2 * x + 3 : ℝ) := by
        rw [abs_of_pos]
        linarith [h6]
      rw [h7]
      linarith [h6]
    have h6 : |(2 * x + 3 : ℝ)| > 4 / ε := h3
    have h7 : (4 : ℝ) < ε * |(2 * x + 3 : ℝ)| := by
      have h8 : ε > 0 := hε
      have h9 : |(2 * x + 3 : ℝ)| > 0 := h5
      have h10 : ε * |(2 * x + 3 : ℝ)| > (4 / ε) * ε := by
        nlinarith [h6, h8, h9]
      have h11 : (4 / ε) * ε = 4 := by
        field_simp [h8]
      nlinarith [h10, h11]
    have h12 : (4 : ℝ) / |(2 * x + 3 : ℝ)| < ε := by
      have h13 : |(2 * x + 3 : ℝ)| > 0 := h5
      have h14 : (4 : ℝ) < ε * |(2 * x + 3 : ℝ)| := h7
      have h15 : (4 : ℝ) / |(2 * x + 3 : ℝ)| < (ε * |(2 * x + 3 : ℝ)|) / |(2 * x + 3 : ℝ)| := by
        apply (div_lt_div_iff_of_pos_right h13).mpr
        linarith [h14]
      have h16 : (ε * |(2 * x + 3 : ℝ)|) / |(2 * x + 3 : ℝ)| = ε := by
        have h17 : |(2 * x + 3 : ℝ)| ≠ 0 := ne_of_gt h13
        field_simp [h17]
      linarith [h15, h16]
    linarith
  linarith [h2, h4]