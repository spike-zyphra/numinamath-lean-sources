import Mathlib

theorem inequalities_320170 (a b t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
    a^2 / t^3 + b^2 / (1 - t^3) ≥ (a + b)^2 := by
  rcases ht with ⟨ht0, ht1⟩
  have ht2 : t^3 > 0 := by positivity
  have ht3 : 1 - t^3 > 0 := by
    have h1 : t^3 < 1 := by
      have ht1' : t < 1 := ht1
      nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (t^2 - t / 2)]
    nlinarith
  have h1 : a^2 / t^3 + b^2 / (1 - t^3) - (a + b) ^ 2 ≥ 0 := by
    have h2 : a^2 / t^3 + b^2 / (1 - t^3) - (a + b) ^ 2 =
      (a^2 * (1 - t^3) + b^2 * t^3 - (a + b)^2 * t^3 * (1 - t^3)) / (t^3 * (1 - t^3)) := by
      field_simp [ht2, ht3]
      ring
    rw [h2]
    have h3 : a^2 * (1 - t^3) + b^2 * t^3 - (a + b)^2 * t^3 * (1 - t^3) ≥ 0 := by
      nlinarith [sq_nonneg (a * t^3 - b * (1 - t^3)), sq_nonneg (a * (1 - t^3) - b * t^3), 
        sq_nonneg (a - b), sq_nonneg (t^3 - (1 - t^3)), 
        mul_pos ht2 ht3, sq_nonneg (a * b), sq_nonneg (t^3)]
    apply div_nonneg
    linarith
    positivity
  linarith