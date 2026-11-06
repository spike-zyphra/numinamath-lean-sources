import Mathlib

/- Problem 2. Prove that for any positive numbers $a$ and $b$ the following inequality holds

$$
\sqrt{\frac{a^{2}}{b}}+\sqrt{\frac{b^{2}}{a}} \geq \sqrt{a}+\sqrt{b}
$$-/
theorem inequalities_143364 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a ^ 2 / b) + Real.sqrt (b ^ 2 / a) ≥ Real.sqrt a + Real.sqrt b := by
  -- Square both sides of the inequality.
  rw [ge_iff_le, <-sq_le_sq₀ (by positivity) (by positivity)]
  -- Show that a² / b * (b² / a) = ab, which is useful for simplification later.
  have h₀ : (a ^ 2 / b) * (b ^ 2 / a) = a * b := by
    field_simp [ha.ne.symm, hb.ne.symm]
    ring
  -- Show that a² / b + b² / a ≥ a + b.
  have h₁ : a ^ 2 / b + b ^ 2 / a ≥ a + b := by
    -- Since a, b > 0, this is essentially (a - b)² ≥ 0.
    field_simp
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (a - b)]
  -- Simplify the inequality after squaring both sides.
  iterate 2 rw [add_sq, mul_assoc, <-Real.sqrt_mul (by positivity)]
  repeat rw [Real.sq_sqrt (by positivity)]
  rw [h₀]
  linarith