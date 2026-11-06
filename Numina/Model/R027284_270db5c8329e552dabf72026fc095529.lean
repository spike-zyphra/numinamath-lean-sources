import Mathlib

open Real

theorem inequalities_304171 (a : ℝ) (ha : a > 0) :
    (∀ x y : ℝ, x > 0 → y > 0 → (x + y) * (1 / x + a / y) ≥ 9) ↔ a ≥ 4 := by
  constructor
  · -- Assume the inequality holds for all positive real numbers x, y.
    intro h
    by_contra h1
    push_neg at h1
    have h2 := h 2 4 (by norm_num) (by norm_num)
    norm_num at h2
    nlinarith
  · -- Assume $a \geq 4$, need to prove the inequality holds.
    intro ha x y hx hy
    have h1 : (x + y) * (1 / x + a / y) = 1 + a + y / x + a * (x / y) := by
      field_simp
      ring
    rw [h1] at *
    have h2 : y / x + a * (x / y) ≥ 2 * Real.sqrt a := by
      have h3 : y / x + a * (x / y) - 2 * Real.sqrt a ≥ 0 := by
        have h4 : y / x + a * (x / y) - 2 * Real.sqrt a = (y ^ 2 + a * x ^ 2 - 2 * Real.sqrt a * x * y) / (x * y) := by
          field_simp
          ring
        rw [h4]
        have h5 : y ^ 2 + a * x ^ 2 - 2 * Real.sqrt a * x * y ≥ 0 := by
          have h6 : y ^ 2 + a * x ^ 2 - 2 * Real.sqrt a * x * y = (y - Real.sqrt a * x) ^ 2 := by
            have h7 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
            nlinarith [Real.sqrt_nonneg a]
          rw [h6]
          positivity
        have h7 : x * y > 0 := mul_pos hx hy
        apply div_nonneg
        linarith
        all_goals
          nlinarith
      linarith
    have h3 : 1 + a + y / x + a * (x / y) ≥ 1 + a + 2 * Real.sqrt a := by
      linarith [h2]
    have h4 : 1 + a + 2 * Real.sqrt a ≥ 9 := by
      have h5 : Real.sqrt a ≥ 2 := by
        nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ a by linarith), sq_nonneg (Real.sqrt a - 2)]
      nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ a by linarith)]
    linarith [h3, h4]