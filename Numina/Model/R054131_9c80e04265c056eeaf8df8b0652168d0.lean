import Mathlib

/- When $x$ varies, the minimum value of the fraction $\frac{3{{x}^{2}}+6x+5}{\dfrac{1}{2}{{x}^{2}}+x+1}$ is ___          ___. -/
theorem algebra_87 : IsLeast {y : ℝ | ∃ x, y = (3 * x ^ 2 + 6 * x + 5) / (1 / 2 * x ^ 2 + x + 1)} 4 := by
  constructor
  · -- Show that 4 is indeed attainable, meaning there's some x such that the fraction equals 4
    use -1
    norm_num
  · -- Show that 4 is the smallest value, so for all y in the set, y ≥ 4
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : (3 * x ^ 2 + 6 * x + 5 : ℝ) / (1 / 2 * x ^ 2 + x + 1) ≥ (4 : ℝ) := by
      have h_pos : (1 / 2 * x ^ 2 + x + 1 : ℝ) > 0 := by
        nlinarith [sq_nonneg (x + 1)]
      have h2 : (3 * x ^ 2 + 6 * x + 5 : ℝ) ≥ 4 * (1 / 2 * x ^ 2 + x + 1) := by
        nlinarith [sq_nonneg (x + 1)]
      apply (le_div_iff₀ h_pos).mpr
      linarith
    linarith [h1, hx]