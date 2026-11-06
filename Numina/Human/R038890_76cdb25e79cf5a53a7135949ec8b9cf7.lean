import Mathlib

/- Prove inequality, with $a$ and $b$ nonnegative real numbers:
$\frac{a+b}{1+a+b}\leq \frac{a}{1+a} + \frac{b}{1+b} \leq \frac{2(a+b)}{2+a+b}$
 -/
theorem inequalities_33141 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / (1 + a + b) ≤ a / (1 + a) + b / (1 + b) ∧
    a / (1 + a) + b / (1 + b) ≤ 2 * (a + b) / (2 + a + b) := by 
  constructor
  case left =>
    -- Prove the first part of the conjunction:
    -- $\frac{a+b}{1+a+b} \leq \frac{a}{1+a} + \frac{b}{1+b}$
    have h₀ : 0 ≤ a + b := by linarith
    have h₁ : 0 ≤ a * b := by nlinarith
    field_simp [add_pos, ha, hb, h₀]
    rw [div_le_div_iff] <;>
      nlinarith [sq_nonneg (a - b)]
  case right =>
    -- Prove the second part of the conjunction:
    -- $\frac{a}{1+a} + \frac{b}{1+b} \leq \frac{2(a+b)}{2+a+b}$
    have h₀ : 0 ≤ a + b := by linarith
    have h₁ : 0 ≤ a * b := by nlinarith
    field_simp [add_pos, ha, hb, h₀]
    rw [div_le_div_iff] <;>
      nlinarith [sq_nonneg (a - b)]