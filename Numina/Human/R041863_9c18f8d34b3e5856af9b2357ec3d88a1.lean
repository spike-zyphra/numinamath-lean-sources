import Mathlib

/- Let $a,b,c,d$ be positive real numbers. Prove that
\[\frac{a}{b+2c+3d}+\frac{b}{c+2d+3a}+\frac{c}{d+2a+3b}+\frac{d}{a+2b+3c} \geq \frac{2}{3}.\] -/
theorem inequalities_75015 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a / (b + 2 * c + 3 * d) + b / (c + 2 * d + 3 * a) +
    c / (d + 2 * a + 3 * b) + d / (a + 2 * b + 3 * c) ≥ 2 / 3 := by
  have h₀ : 0 < a + b + c + d := by linarith
  have h₁ : 0 < a * b := by nlinarith
  have h₂ : 0 < a * c := by nlinarith
  have h₃ : 0 < a * d := by nlinarith
  have h₄ : 0 < b * c := by nlinarith
  have h₅ : 0 < b * d := by nlinarith
  have h₆ : 0 < c * d := by nlinarith
  -- Clear denominators and manipulate the inequality
  field_simp
  rw [div_le_div_iff] <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]