import Mathlib

theorem algebra_20734 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h₀ : a^2 + b^2 + c^2 = 13) (h₁ : a * b + b * c + c * a = 6) :
    a + b + c = 5 := by
  have h2 : (a + b + c) ^ 2 = 25 := by
    calc
      (a + b + c) ^ 2 = (a^2 + b^2 + c^2) + 2 * (a * b + b * c + c * a) := by ring
      _ = 13 + 2 * 6 := by rw [h₀, h₁]
      _ = 25 := by norm_num

  have h3 : a + b + c ≥ 0 := by
    linarith [ha, hb, hc]

  have h4 : a + b + c = 5 := by
    nlinarith [h2, h3]

  exact h4