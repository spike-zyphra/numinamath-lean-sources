import Mathlib

theorem algebra_314258 {a b c d : ℝ} (ha : a < b) (h : ∀ x, (x - c) * (x - c - d) - 2 = 0 → x = a ∨ x = b) :
    |a - c| + |c - b| = b - a := by
  have eq1 : (c + (d + Real.sqrt (d ^ 2 + 8)) / 2 - c) * (c + (d + Real.sqrt (d ^ 2 + 8)) / 2 - c - d) - 2 = 0 := by
    have h1 : Real.sqrt (d ^ 2 + 8) ≥ 0 := Real.sqrt_nonneg (d ^ 2 + 8)
    nlinarith [Real.sq_sqrt (show 0 ≤ (d^2 + 8) by nlinarith)]
  have h1 := h (c + (d + Real.sqrt (d ^ 2 + 8)) / 2) eq1

  have eq2 : (c + (d - Real.sqrt (d ^ 2 + 8)) / 2 - c) * (c + (d - Real.sqrt (d ^ 2 + 8)) / 2 - c - d) - 2 = 0 := by
    have h2 : Real.sqrt (d ^ 2 + 8) ≥ 0 := Real.sqrt_nonneg (d ^ 2 + 8)
    nlinarith [Real.sq_sqrt (show 0 ≤ (d^2 + 8) by nlinarith)]
  have h2 := h (c + (d - Real.sqrt (d ^ 2 + 8)) / 2) eq2

  rcases h1 with h1 | h1
  · -- Case where $c + \frac{d + \sqrt{d^2 + 8}}{2} = a$
    rcases h2 with h2 | h2
    · -- Case where $c + \frac{d - \sqrt{d^2 + 8}}{2} = a$
      exfalso
      nlinarith [Real.sqrt_nonneg (d^2 + 8)]
    · -- Case where $c + \frac{d - \sqrt{d^2 + 8}}{2} = b$
      exfalso
      nlinarith [Real.sqrt_nonneg (d^2 + 8)]
  · -- Case where $c + \frac{d + \sqrt{d^2 + 8}}{2} = b$
    rcases h2 with h2 | h2
    · -- Case where $c + \frac{d - \sqrt{d^2 + 8}}{2} = a$
      have ha_eq : a = c + (d - Real.sqrt (d ^ 2 + 8)) / 2 := by linarith
      have hb_eq : b = c + (d + Real.sqrt (d ^ 2 + 8)) / 2 := by linarith
      rw [ha_eq, hb_eq]
      cases' abs_cases ((c + (d - Real.sqrt (d ^ 2 + 8)) / 2) - c) with h1 h1 <;> 
      cases' abs_cases (c - (c + (d + Real.sqrt (d ^ 2 + 8)) / 2)) with h2 h2 <;> 
      nlinarith [Real.sq_sqrt (show 0 ≤ (d^2 + 8) by nlinarith)]
    · -- Case where $c + \frac{d - \sqrt{d^2 + 8}}{2} = b$
      exfalso
      nlinarith [Real.sqrt_nonneg (d^2 + 8)]