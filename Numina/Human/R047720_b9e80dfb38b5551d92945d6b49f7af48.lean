import Mathlib

theorem algebra_155942 :
    IsLeast {√(a * b) + √(b * c) + √(c * a) | (a : ℝ) (b : ℝ) (c : ℝ) (_ : 0 ≤ a) (_ : 0 ≤ b) (_ : 0 ≤ c) (_ : a * b + b * c + c * a = a + b + c) (_ : a + b + c > 0)} 2 := by
  constructor
  . use 0, 2, 2
    simp
    norm_num
  . rintro x ⟨a, b, c, ha, hb, hc, h, h₀, rfl⟩
    have H : (a + b + c) * (√(a * b) + √(b * c) + √(c * a)) ≥ (a * b + b * c + c * a) * 2 := by
      calc (a + b + c) * (√(a * b) + √(b * c) + √(c * a))
        _ = (a + b) * √(a * b) + (b + c) * √(b * c) + (c + a) * √(c * a) + c * √(a * b) + a * √(b * c) + b * √(c * a) := by ring
        _ ≥ (a + b) * √(a * b) + (b + c) * √(b * c) + (c + a) * √(c * a) := by linarith only [show c * √(a * b) ≥ 0 by positivity, show a * √(b * c) ≥ 0 by positivity, show b * √(c * a) ≥ 0 by positivity]
        _ ≥ 2 * √(a * b)^2 + 2 * √(b * c)^2 + 2 * √(c * a)^2 := by
          have lem {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 2 * √(a * b) ≤ a + b := by
            rw [Real.sqrt_mul ha]
            nth_rw 2 [← Real.sq_sqrt ha, ← Real.sq_sqrt hb]
            linarith only [sq_nonneg (√a - √b)]
          nlinarith only [lem ha hb, lem hb hc, lem hc ha, show √(a * b) ≥ 0 by positivity, show √(b * c) ≥ 0 by positivity, show √(c * a) ≥ 0 by positivity]
        _ = (a * b + b * c + c * a) * 2 := by
          rw [Real.sq_sqrt (mul_nonneg ha hb), Real.sq_sqrt (mul_nonneg hb hc), Real.sq_sqrt (mul_nonneg hc ha)]
          ring
    rw [h] at H
    exact le_of_mul_le_mul_left H h₀
