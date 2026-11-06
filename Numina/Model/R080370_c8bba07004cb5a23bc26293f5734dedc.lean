import Mathlib

theorem inequalities_104719 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 + b^2 + c^2 ≥ a * b + b * c + c * a ∧ (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  constructor
  · -- Prove the first inequality $a^2 + b^2 + c^2 \geq a \cdot b + b \cdot c + c \cdot a$
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  · -- Prove the second inequality $(a + b + c)^2 \geq 3(a \cdot b + b \cdot c + c \cdot a)$
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]