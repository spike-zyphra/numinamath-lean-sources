import Mathlib

lemma lemma_1 {x : ℝ} (hx : (x - Real.sqrt 2)^3 = 8) : x^2 - 4 * x + 2 = 0 := by
  have h1 : x - Real.sqrt 2 = 2 := by
    have h2 : (x - Real.sqrt 2) ^ 3 - 8 = 0 := by linarith
    have h3 : (x - Real.sqrt 2 - 2) * ((x - Real.sqrt 2) ^ 2 + (x - Real.sqrt 2) * 2 + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h3) with h4 h5
    ·
      linarith
    ·
      nlinarith [sq_nonneg ((x - Real.sqrt 2) + 1)]
  have hx3 : x = Real.sqrt 2 + 2 := by
    nlinarith [Real.sqrt_nonneg 2, h1, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hx3]
  nlinarith [Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem algebra_321722 {x : ℝ}
    (hx : x^3 - 3 * Real.sqrt 2 * x^2 + 6 * x - 2 * Real.sqrt 2 - 8 = 0) :
    x^5 - 41 * x^2 + 1 = -13 := by
  have hx0 : x^3 - 3 * Real.sqrt 2 * x^2 + 6 * x - 2 * Real.sqrt 2 = 8 := by linarith
  have h1 : (x - Real.sqrt 2)^3 = 8 := by
    have eq1 : (x - Real.sqrt 2) ^ 3 = x^3 - 3 * Real.sqrt 2 * x^2 + 6 * x - 2 * Real.sqrt 2 := by
      ring_nf
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      have h3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
        calc
          Real.sqrt 2 ^ 3 = (Real.sqrt 2 ^ 2) * Real.sqrt 2 := by ring
          _ = 2 * Real.sqrt 2 := by rw [h2]
      simp [h2, h3]
      ring
    rw [eq1] at *
    linarith [hx0]
  have hx2 : x^2 - 4 * x + 2 = 0 := by
    apply lemma_1
    exact h1
  have h2 : x^2 = 4 * x - 2 := by linarith
  have h3 : x^3 = 14 * x - 8 := by
    calc
      x^3 = x * x^2 := by ring
      _ = x * (4 * x - 2) := by rw [h2]
      _ = 4 * x^2 - 2 * x := by ring
      _ = 4 * (4 * x - 2) - 2 * x := by rw [h2]
      _ = 14 * x - 8 := by nlinarith
  have h4 : x^4 = 48 * x - 28 := by
    calc
      x^4 = x * x^3 := by ring
      _ = x * (14 * x - 8) := by rw [h3]
      _ = 14 * x^2 - 8 * x := by ring
      _ = 14 * (4 * x - 2) - 8 * x := by rw [h2]
      _ = 48 * x - 28 := by nlinarith
  have h5 : x^5 = 164 * x - 96 := by
    calc
      x^5 = x * x^4 := by ring
      _ = x * (48 * x - 28) := by rw [h4]
      _ = 48 * x^2 - 28 * x := by ring
      _ = 48 * (4 * x - 2) - 28 * x := by rw [h2]
      _ = 164 * x - 96 := by nlinarith
  nlinarith [h5, h2, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]