import Mathlib

/- Let $a, b, c$ be positive real numbers such that $a+b+c=3$. Find the minimum value of the expression

$$
A=\frac{2-a^{3}}{a}+\frac{2-b^{3}}{b}+\frac{2-c^{3}}{c}
$$

![](https://cdn.mathpix.com/cropped/2024_06_05_f56efd4e6fb711c0f78eg-2.jpg?height=348&width=477&top_left_y=109&top_left_x=241)

$19^{\text {th }}$ Junior Balkan Mathematical Olympiad June 24-29, 2015, Belgrade, Serbia -/
theorem inequalities_605667 :
  IsLeast {(2 - a ^ 3) / a + (2 - b ^ 3) / b + (2 - c ^ 3) / c | (a : ℝ) (b : ℝ) (c : ℝ) (_ : a > 0) (_ : b > 0) (_ : c > 0) (_ : a + b + c = 3)} 3 := by
  constructor
  -- We first show that 3 can be attained.
  . use 1, 1, 1
    norm_num
  -- We now show that 3 is the minimum value.
  -- Let a, b, c be positive real numbers such that a + b + c = 3.
  . rintro x ⟨a, b, c, ha, hb, hc, h, rfl⟩
    rw [← ge_iff_le]
    calc (2 - a ^ 3) / a + (2 - b ^ 3) / b + (2 - c ^ 3) / c
      _ = 2 * (1 / a + 1 / b + 1 / c) - (a ^ 2 + b ^ 2 + c ^ 2) := by field_simp [ha, hb, hc]; ring
      _ = 2 * (a * b + b * c + c * a) / (a * b * c) - (a ^ 2 + b ^ 2 + c ^ 2) := by field_simp [ha, hb, hc]; ring
      -- Formula for the sum of squares.
      _ = 2 * (a * b + b * c + c * a) / (a * b * c) - ((a + b + c) ^ 2 - 2 * (a * b + b * c + c * a)) := by ring
      -- Substitute a + b + c = 3.
      _ = 2 * (a * b + b * c + c * a) / (a * b * c) - (9 - 2 * (a * b + b * c + c * a)) := by rw [h]; norm_num
      _ = 2 * (a * b + b * c + c * a) * (1 / (a * b * c) + 1) - 9 := by ring
      _ ≥ 3 := ?_
    -- Now it suffices to show that (a * b + b * c + c * a) * (1 / (a * b * c) + 1) ≥ 6.
    suffices (a * b + b * c + c * a) * (1 / (a * b * c) + 1) ≥ 6 by linarith
    -- We first show that a * b + b * c + c * a ≥ 3 * √(a * b * c).
    have h₁ : 3 * √(a * b * c) ≤ a * b + b * c + c * a := by
      -- Square both sides.
      rw [← sq_le_sq₀ (by positivity) (by positivity)]
      ring_nf
      rw [Real.sq_sqrt (by positivity)]
      -- Rewrite 9 as 3 * (a + b + c).
      rw [show 9 = 3 * (a + b + c) by rw [h]; norm_num]
      -- Now it comes from 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2.
      linarith only [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
    -- Now we show that 2 / √(a * b * c) ≤ 1 / (a * b * c) + 1.
    -- AM-GM.
    have h₂ : 2 / √(a * b * c) ≤ 1 / (a * b * c) + 1 := by
      have h₂ : (1 / √(a * b * c)) ^ 2 = 1 / (a * b * c) := by
        field_simp
        ring_nf
        repeat rw [Real.sq_sqrt (by positivity)]
      calc 2 / √(a * b * c)
        _ = 2 * (1 / √(a * b * c)) := by ring
        _ ≤ (1 / √(a * b * c)) ^ 2 + 1 := by linarith only [sq_nonneg (1 / √(a * b * c) - 1)]
        _ = 1 / (a * b * c) + 1 := by rw [h₂]
    -- Now combine the two inequalities.
    calc (a * b + b * c + c * a) * (1 / (a * b * c) + 1)
      _ ≥ 3 * √(a * b * c) * (2 / √(a * b * c)) := mul_le_mul_of_nonneg h₁ h₂ (by positivity) (by positivity)
      _ = 6 := by field_simp; ring
