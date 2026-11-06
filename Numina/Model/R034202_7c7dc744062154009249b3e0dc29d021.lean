import Mathlib
theorem algebra_13599 (f : ℝ → ℝ) (hf : f = fun x => (2 * x ^ 2 + 7 * x + 10) / (2 * x + 3)) :
    ∀ ε > 0, ∃ x₁, ∀ x, x > x₁ → |f x - (x + 2)| < ε := by
  intro ε hε
  use (4 / ε - 3) / 2
  intro x hx
  have h1 : x > (4 / ε - 3) / 2 := hx
  have h2 : 2 * x + 3 > 4 / ε := by
    linarith
  have h3 : |(2 * x ^ 2 + 7 * x + 10) / (2 * x + 3) - (x + 2)| = 4 / (2 * x + 3) := by
    have h4 : (2 * x ^ 2 + 7 * x + 10) / (2 * x + 3) - (x + 2) = (4 / (2 * x + 3)) := by
      have h5 : 2 * x + 3 ≠ 0 := by
        have h6 : 2 * x + 3 > 0 := by
          have h10 : (4 / ε : ℝ) > 0 := by
            apply div_pos
            norm_num
            all_goals linarith
          nlinarith
        linarith
      field_simp [h5]
      ring
    rw [h4]
    have h7 : (2 * x + 3) > 0 := by
      have h10 : (4 / ε : ℝ) > 0 := by
        apply div_pos
        norm_num
        all_goals linarith
      nlinarith
    have h8 : 4 / (2 * x + 3) ≥ 0 := by
      apply div_nonneg
      · norm_num
      all_goals linarith
    have h9 : |(4 / (2 * x + 3) : ℝ)| = (4 / (2 * x + 3) : ℝ) := by
      rw [abs_of_nonneg h8]
    rw [h9]
  have hx2 : f x = (2 * x ^ 2 + 7 * x + 10) / (2 * x + 3) := by rw [hf]
  rw [hx2] at *
  rw [h3]
  have h10 : (4 / (2 * x + 3) : ℝ) < (ε : ℝ) := by
    have h11 : (2 * x + 3 : ℝ) > (4 / ε : ℝ) := by
      linarith [h2]
    have h12 : ε * (2 * x + 3) > (4 : ℝ) := by
      have h14 : (2 * x + 3) > (4 / ε : ℝ) := h11
      have h13 : ε > 0 := hε
      have h15 : ε * (2 * x + 3) > ε * (4 / ε : ℝ) := by nlinarith [h14, h13]
      have h16 : ε * (4 / ε : ℝ) = (4 : ℝ) := by
        field_simp [show ε ≠ 0 by linarith [hε]]
      nlinarith [h15, h16]
    have h17 : (2 * x + 3 : ℝ) > 0 := by
      have h10 : (4 / ε : ℝ) > 0 := by
        apply div_pos
        norm_num
        all_goals linarith
      nlinarith
    have h18 : (4 / (2 * x + 3) : ℝ) < (ε : ℝ) := by
      apply (div_lt_iff₀ (by linarith)).mpr
      nlinarith
    linarith
  linarith