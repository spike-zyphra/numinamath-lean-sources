import Mathlib

theorem inequalities_598832 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 ≤ a^2 / (a^2 + 2 * b * c) + b^2 / (b^2 + 2 * c * a) + c^2 / (c^2 + 2 * a * b) ∧
    1 ≥ b * c / (a^2 + 2 * b * c) + c * a / (b^2 + 2 * c * a) + a * b / (c^2 + 2 * a * b) := by
  constructor
  · -- First inequality: $\frac{a^2}{a^2 + 2bc} + \frac{b^2}{b^2 + 2ca} + \frac{c^2}{c^2 + 2ab} \geq 1$
    have h1 : 0 < a^2 + 2 * b * c := by positivity
    have h2 : 0 < b^2 + 2 * c * a := by positivity
    have h3 : 0 < c^2 + 2 * a * b := by positivity
    have h : a^2 / (a^2 + 2 * b * c) + b^2 / (b^2 + 2 * c * a) + c^2 / (c^2 + 2 * a * b) - 1 ≥ 0 := by
      have h4 : a^2 / (a^2 + 2 * b * c) + b^2 / (b^2 + 2 * c * a) + c^2 / (c^2 + 2 * a * b) - 1 =
        (a^2 * (b^2 + 2 * c * a) * (c^2 + 2 * a * b) + b^2 * (a^2 + 2 * b * c) * (c^2 + 2 * a * b) + c^2 * (a^2 + 2 * b * c) * (b^2 + 2 * c * a) - (a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b)) / ((a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b)) := by
        field_simp
        ring
      rw [h4]
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (c - a)),
        sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (c - a)),
        sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (c - a)),
        mul_pos ha hb, mul_pos hb hc, mul_pos hc ha]
      positivity
    linarith
  · -- Second inequality: $1 \geq \frac{bc}{a^2 + 2bc} + \frac{ca}{b^2 + 2ca} + \frac{ab}{c^2 + 2ab}$
    have h1 : 0 < a^2 + 2 * b * c := by positivity
    have h2 : 0 < b^2 + 2 * c * a := by positivity
    have h3 : 0 < c^2 + 2 * a * b := by positivity
    have h : 1 - (b * c / (a^2 + 2 * b * c) + c * a / (b^2 + 2 * c * a) + a * b / (c^2 + 2 * a * b)) ≥ 0 := by
      have h4 : 1 - (b * c / (a^2 + 2 * b * c) + c * a / (b^2 + 2 * c * a) + a * b / (c^2 + 2 * a * b)) =
        ((a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b) - (b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b) - (c * a) * (a^2 + 2 * b * c) * (c^2 + 2 * a * b) - (a * b) * (a^2 + 2 * b * c) * (b^2 + 2 * c * a)) / ((a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b)) := by
        field_simp
        ring
      rw [h4]
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (c - a)),
        sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (c - a)),
        sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (c - a)),
        mul_pos ha hb, mul_pos hb hc, mul_pos hc ha]
      positivity
    linarith