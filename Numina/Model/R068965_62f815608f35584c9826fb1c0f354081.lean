import Mathlib

theorem algebra_17 {x : ℝ} (hx : x > 0) (h : (1 + x / 100)^2 = 900000 / 400000) :
    x = 50 := by
  have h1 : (1 + x / 100) ^ 2 = (9 / 4 : ℝ) := by
    norm_num at h ⊢
    linarith
  have h3 : (1 + x / 100) = (3 / 2 : ℝ) ∨ (1 + x / 100) = (-3 / 2 : ℝ) := by
    have h4 : (1 + x / 100) ^ 2 - (9 / 4 : ℝ) = 0 := by
      linarith
    have h5 : ((1 + x / 100) - (3 / 2 : ℝ)) * ((1 + x / 100) + (3 / 2 : ℝ)) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case where $1 + \frac{x}{100} - \frac{3}{2} = 0$, so the first disjunction holds
      have h8 : (1 + x / 100 - 3 / 2 : ℝ) = 0 := by
        linarith
      have h9 : (1 + x / 100) = (3 / 2 : ℝ) := by linarith
      left
      linarith
    · -- Case where $1 + \frac{x}{100} + \frac{3}{2} = 0$, which implies a negative x.
      have h8 : (1 + x / 100 + 3 / 2 : ℝ) = 0 := by
        linarith
      have h9 : (1 + x / 100) = (-3 / 2 : ℝ) := by linarith
      right
      linarith
  cases' h3 with h4 h5
  · -- Case where (1 + x / 100) = 3/2, solving for x gives x = 50
    have hx_eq : x = 50 := by
      nlinarith
    linarith
  · -- Case where (1 + x / 100) = -3/2, which would require x < 0, contradicting hx: x > 0
    exfalso
    nlinarith