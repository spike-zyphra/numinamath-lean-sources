import Mathlib

theorem algebra_224192 {a b c : ℝ} (h : (a + 3)^2 + (b + 4)^2 - (c + 5)^2 = a^2 + b^2 - c^2) :
    ∃ m, m^2 = (a + 3)^2 + (b + 4)^2 - (c + 5)^2 ∧ ∃ n, n^2 = a^2 + b^2 - c^2 := by
  have h1 : 3 * a + 4 * b = 5 * c := by
    nlinarith
  have hc : c = (3 * a + 4 * b) / 5 := by
    linarith
  use ( (4 * a - 3 * b) / 5 )
  constructor
  · -- Show that m^2 equals the left side of the equation
    have h2 : (a + 3) ^ 2 + (b + 4) ^ 2 - (c + 5) ^ 2 = a ^ 2 + b ^ 2 - c ^ 2 := h
    have h3 : ( (4 * a - 3 * b) / 5 ) ^ 2 = a ^ 2 + b ^ 2 - c ^ 2 := by
      rw [hc]
      nlinarith [sq_nonneg (a * 3 - b * 4), sq_nonneg (a * 4 - b * 3)]
    nlinarith [h3, h2]
  · -- Show the existence of n such that n^2 equals the right side
    use ( (4 * a - 3 * b) / 5 )
    have h4 : ( (4 * a - 3 * b) / 5 ) ^ 2 = a ^ 2 + b ^ 2 - c ^ 2 := by
      rw [hc]
      nlinarith [sq_nonneg (a * 3 - b * 4), sq_nonneg (a * 4 - b * 3)]
    linarith [h4]