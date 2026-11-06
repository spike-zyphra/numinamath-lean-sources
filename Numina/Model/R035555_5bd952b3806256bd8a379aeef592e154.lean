import Mathlib

open Real Set

/- Given $a>b$, $a+b=2$, then the minimum value of $\frac{{{a}^{2}}+{{b}^{2}}}{a-b}$ is ___          ___. -/
theorem algebra_7365 {a b : ℝ} (ha : a > b) (h : a + b = 2) :
    IsLeast {x | ∃ a b : ℝ, a > b ∧ a + b = 2 ∧ x = (a ^ 2 + b ^ 2) / (a - b)} 2 := by
  constructor
  · -- Show that 2 is in the set.
    use 2, 0
    norm_num
  · -- Show that 2 is a lower bound of the set.
    intro x hx
    rcases hx with ⟨a, b, h1, h2, hx⟩
    have h3 : a - b > 0 := by linarith
    have h4 : a ^ 2 + b ^ 2 ≥ 2 * (a - b) := by
      have h5 : b = 2 - a := by linarith
      rw [h5]
      nlinarith [sq_nonneg (a - 2)]
    have h5 : (a ^ 2 + b ^ 2) / (a - b) ≥ 2 := by
      have h6 : a - b > 0 := h3
      apply (le_div_iff₀ (by linarith)).mpr
      nlinarith [sq_pos_of_pos (show a - b > 0 by linarith), sq_nonneg (a - 2)]
    linarith [h5, hx]