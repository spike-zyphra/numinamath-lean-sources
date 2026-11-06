import Mathlib

theorem algebra_302927 (a b c : ℝ) (h₀ : a + b + c = 0) (h₁ : a * b * c = 2) :
    abs a^3 + abs b^3 + abs c^3 ≥ 10 := by
  have h2 : a^3 + b^3 + c^3 = 6 := by
    have h2 : a^3 + b^3 + c^3 = 3 * (a * b * c) := by
      have h3 : a + b + c = 0 := h₀
      have h4 : a^3 + b^3 + c^3 - 3 * (a * b * c) = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + a * c + b * c)) := by
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
      rw [h3] at h4
      linarith
    rw [h2]
    linarith
  by_cases ha1 : 0 ≤ a
  · -- Case a ≥ 0
    have ha2 : abs a = a := abs_of_nonneg ha1
    rw [show abs a ^ 3 = a ^ 3 by rw [ha2]]
    by_cases hb1 : 0 ≤ b
    · -- Case b ≥ 0
      have hb2 : abs b = b := abs_of_nonneg hb1
      rw [show abs b ^ 3 = b ^ 3 by rw [hb2]]
      by_cases hc1 : 0 ≤ c
      · -- Case c ≥ 0
        have hc2 : abs c = c := abs_of_nonneg hc1
        rw [show abs c ^ 3 = c ^ 3 by rw [hc2]]
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * b * c - 2), sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]
      · -- Case c < 0
        have hc2 : abs c = -c := abs_of_neg (lt_of_not_ge hc1)
        rw [show abs c ^ 3 = (-c) ^ 3 by rw [hc2]]
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * b * c - 2), sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]
    · -- Case b < 0
      have hb2 : abs b = -b := abs_of_neg (lt_of_not_ge hb1)
      rw [show abs b ^ 3 = (-b) ^ 3 by rw [hb2]]
      by_cases hc1 : 0 ≤ c
      · -- Case c ≥ 0
        have hc2 : abs c = c := abs_of_nonneg hc1
        rw [show abs c ^ 3 = c ^ 3 by rw [hc2]]
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * b * c - 2), sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]
      · -- Case c < 0
        have hc2 : abs c = -c := abs_of_neg (lt_of_not_ge hc1)
        rw [show abs c ^ 3 = (-c) ^ 3 by rw [hc2]]
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * b * c - 2), sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]
  · -- Case a < 0
    have ha2 : abs a = -a := abs_of_neg (lt_of_not_ge ha1)
    rw [show abs a ^ 3 = (-a) ^ 3 by rw [ha2]]
    by_cases hb1 : 0 ≤ b
    · -- Case b ≥ 0
      have hb2 : abs b = b := abs_of_nonneg hb1
      rw [show abs b ^ 3 = b ^ 3 by rw [hb2]]
      by_cases hc1 : 0 ≤ c
      · -- Case c ≥ 0
        have hc2 : abs c = c := abs_of_nonneg hc1
        rw [show abs c ^ 3 = c ^ 3 by rw [hc2]]
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * b * c - 2), sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]
      · -- Case c < 0
        have hc2 : abs c = -c := abs_of_neg (lt_of_not_ge hc1)
        rw [show abs c ^ 3 = (-c) ^ 3 by rw [hc2]]
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * b * c - 2), sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]
    · -- Case b < 0
      have hb2 : abs b = -b := abs_of_neg (lt_of_not_ge hb1)
      rw [show abs b ^ 3 = (-b) ^ 3 by rw [hb2]]
      by_cases hc1 : 0 ≤ c
      · -- Case c ≥ 0
        have hc2 : abs c = c := abs_of_nonneg hc1
        rw [show abs c ^ 3 = c ^ 3 by rw [hc2]]
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * b * c - 2), sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]
      · -- Case c < 0
        have hc2 : abs c = -c := abs_of_neg (lt_of_not_ge hc1)
        rw [show abs c ^ 3 = (-c) ^ 3 by rw [hc2]]
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * b * c - 2), sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]