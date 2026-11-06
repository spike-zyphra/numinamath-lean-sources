import Mathlib

open Real

theorem algebra_108072 {f : ℝ → ℝ} (hf : ∀ x ∈ Set.Ioo 0 1, f x = x / log x) :
    ∀ x ∈ Set.Ioo 0 1, f x < f (x ^ 2) ∧ f (x ^ 2) < f x ^ 2 := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have hfx : f x = x / log x := hf x ⟨hx1, hx2⟩
  have hfx2 : f (x ^ 2) = x ^ 2 / log (x ^ 2) := hf (x ^ 2) ⟨by nlinarith, by nlinarith⟩
  have h1 : log (x ^ 2) = 2 * log x := by
    simp [log_pow]
  have eq1 : f (x ^ 2) = x ^ 2 / (2 * log x) := by
    rw [hfx2]
    rw [h1]
  have eq2 : f x = x / log x := hfx
  have h2 : log x < 0 := by
    have h3 : log x < log (1 : ℝ) := by
      apply Real.log_lt_log
      all_goals nlinarith
    have h4 : log (1 : ℝ) = 0 := Real.log_one
    have h5 : log x < (0 : ℝ) := by linarith [h3, h4]
    linarith
  have h3 : f x < f (x ^ 2) := by
    rw [eq2, eq1]
    have h4 : x / log x < x ^ 2 / (2 * log x) := by
      have h7 : x / log x - x ^ 2 / (2 * log x) < 0 := by
        have h8 : x / log x - x ^ 2 / (2 * log x) = (2 * x - x ^ 2) / (2 * log x) := by
          field_simp [(show log x ≠ 0 by
            have h8 : log x < 0 := h2
            linarith
          )]
          <;> ring
        rw [h8]
        have h9 : 2 * log x < 0 := by
          nlinarith [h2]
        have h10 : 2 * x - x ^ 2 > 0 := by
          have h11 : x > 0 := by linarith [hx1]
          have h12 : x < 1 := by linarith [hx2]
          nlinarith
        apply div_neg_of_pos_of_neg
        linarith
        nlinarith
      linarith
    linarith
  have h4 : f (x ^ 2) < (f x) ^ 2 := by
    rw [eq1, eq2]
    have h7 : x ^ 2 / (2 * log x) < (x / log x) ^ 2 := by
      have h7 : x ^ 2 / (2 * log x) - (x / log x) ^ 2 < 0 := by
        have h8 : x ^ 2 / (2 * log x) - (x / log x) ^ 2 = (x ^ 2 / (2 * (log x) ^ 2)) * (log x - 2) := by
          field_simp [(show log x ≠ 0 by
            have h8 : log x < 0 := h2
            linarith
          )]
          <;> ring
        rw [h8]
        have h9 : log x - 2 < 0 := by
          nlinarith [h2]
        have h10 : x ^ 2 / (2 * (log x) ^ 2) > 0 := by
          have h6 : log x < 0 := h2
          have h7 : (log x) ^ 2 > 0 := by nlinarith
          positivity
        nlinarith
      linarith
    linarith
  exact ⟨h3, h4⟩