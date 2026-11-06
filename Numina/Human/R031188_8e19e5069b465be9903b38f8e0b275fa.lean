import Mathlib

open Real

/- Exercise 6. Show that for all strictly positive real numbers $a, b, c$:


$$
\frac{b c}{a^{2}+2 b c}+\frac{c a}{b^{2}+2 c a}+\frac{a b}{c^{2}+2 a b} \leqslant 1 \leqslant \frac{a^{2}}{a^{2}+2 b c}+\frac{b^{2}}{b^{2}+2 c a}+\frac{c^{2}}{c^{2}+2 a b}
$$
 -/

theorem inequalities_292930 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b * c / (a ^ 2 + 2 * b * c) + c * a / (b ^ 2 + 2 * c * a) +
     a * b / (c ^ 2 + 2 * a * b)) ≤ 1 ∧
    1 ≤ (a ^ 2 / (a ^ 2 + 2 * b * c) + b ^ 2 / (b ^ 2 + 2 * c * a) +
        c ^ 2 / (c ^ 2 + 2 * a * b)) := by
  -- we'll need AM-GM on two variables, so let's prove it
  have hamgm: ∀ a b:ℝ, 2*a*b ≤ a^2+b^2 := by
    intro a b
    have h: 0 ≤ (a - b)^2 := by nlinarith
    linarith [h]
  -- we do the right inequality first, we'll need it later so we store it
  have h_right: 1 ≤ a^2/(a^2+2*b*c) + b^2/(b^2+2*c*a) + c^2/(c^2+2*a*b) := by
    calc 1
      _ ≤ a^2/(a^2+b^2+c^2) + b^2/(a^2+b^2+c^2) + c^2/(a^2+b^2+c^2) := by field_simp
      _ ≤ a^2/(a^2+2*b*c) + b^2/(b^2+2*c*a) + c^2/(c^2+2*a*b) := by
        apply add_le_add; apply add_le_add
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by nlinarith) (by rw [add_assoc]; apply add_le_add; simp; exact hamgm _ _)
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by nlinarith) (by rw [add_comm (a^2), add_assoc, mul_assoc, mul_comm c, ← mul_assoc]; apply add_le_add; simp; exact hamgm _ _)
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by nlinarith) (by rw [add_comm]; apply add_le_add; exact hamgm _ _; simp)
  constructor
  rotate_left
  exact h_right
  -- now the left inequality
  -- if we denote the rhs of first inequality with G, and the left side of current inequality with D, we can easily
  -- observe that G+2*D = 3
  have observation: a ^ 2 / (a ^ 2 + 2 * b * c) + b ^ 2 / (b ^ 2 + 2 * c * a) + c ^ 2 / (c ^ 2 + 2 * a * b) + 2 * (b * c / (a ^ 2 + 2 * b * c) + c * a / (b ^ 2 + 2 * c * a) + a * b / (c ^ 2 + 2 * a * b)) = 3 := by
    field_simp; ring_nf
  -- so we can factor out D = 1/2(3-G)
  have h_left: b * c / (a ^ 2 + 2 * b * c) + c * a / (b ^ 2 + 2 * c * a) + a * b / (c ^ 2 + 2 * a * b) = 1/2 * (3 - (a ^ 2 / (a ^ 2 + 2 * b * c) + b ^ 2 / (b ^ 2 + 2 * c * a) + c ^ 2 / (c ^ 2 + 2 * a * b))) := by
    linarith [observation]
  rw [h_left]
  -- the conclusion is then trivial
  linarith