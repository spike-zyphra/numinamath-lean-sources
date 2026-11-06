import Mathlib

open Real
open scoped BigOperators

theorem inequalities_263134 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (f : ℝ → ℝ → ℝ → ℝ)
  (hf : f = λ a b c => A * (a^3 + b^3 + c^3) + B * (a^2 * b + b^2 * c + c^2 * a + a * b^2 + b * c^2 + c * a^2) +
    C * a * b * c) :
  (f 1 1 1 ≥ 0 ∧ f 1 1 0 ≥ 0 ∧ f 2 1 1 ≥ 0) → f a b c ≥ 0 ∧
  (f 1 1 1 > 0 ∧ f 1 1 0 ≥ 0 ∧ f 2 1 1 ≥ 0) → f a b c > 0 ∧
  (f 1 1 1 = 0 ∧ f 1 1 0 > 0 ∧ f 2 1 1 ≥ 0) → f a b c ≥ 0 := by 
  intro h1 h2 h3
  simp [hf] at *
  <;> nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), mul_pos (sub_pos.mpr h'') (sub_pos.mpr h)]