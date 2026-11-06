import Mathlib

open BigOperators Real

theorem inequalities_228204 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 + b^2 + c^2)^2 > 2 * (a^4 + b^4 + c^4) ↔
    ∃ d e f : ℝ, 0 < d ∧ 0 < e ∧ 0 < f ∧
      a = d + e ∧ b = e + f ∧ c = f + d := by
  constructor
  · -- Forward direction: if (a^2 + b^2 + c^2)^2 > 2 * (a^4 + b^4 + c^4), then a, b, c form a triangle.
    intro h
    have h1 : (a + b - c) * (a + c - b) * (b + c - a) > 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h2 : a + b > c := by
      nlinarith [sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h3 : a + c > b := by
      nlinarith [sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h4 : b + c > a := by
      nlinarith [sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    use (a + c - b) / 2, (a + b - c) / 2, (b + c - a) / 2
    constructor
    · -- Show d > 0
      nlinarith
    constructor
    · -- Show e > 0
      nlinarith
    constructor
    · -- Show f > 0
      nlinarith
    constructor
    · -- Show a = d + e
      ring
    constructor
    · -- Show b = e + f
      ring
    · -- Show c = f + d
      ring
  · -- Backward direction: if exists d, e, f, then (a^2 + b^2 + c^2)^2 > 2 * (a^4 + b^4 + c^4)
    rintro ⟨d, e, f, hd, he, hf, ha_eq, hb_eq, hc_eq⟩
    have ha1 : a = d + e := by linarith
    have hb1 : b = e + f := by linarith
    have hc1 : c = f + d := by linarith
    have h1 : a + b > c := by
      nlinarith [hb1, hc1, ha1, he, hf, hd]
    have h2 : a + c > b := by
      nlinarith [hb1, hc1, ha1, he, hf, hd]
    have h3 : b + c > a := by
      nlinarith [hb1, hc1, ha1, he, hf, hd]
    have h10 : (a + b - c) * (a + c - b) * (b + c - a) > 0 := by
      have h4 : a + b - c > 0 := by linarith
      have h5 : a + c - b > 0 := by linarith
      have h6 : b + c - a > 0 := by linarith
      positivity
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
      mul_pos (show 0 < a + b + c by positivity) (show 0 < (a + b - c) * (a + c - b) * (b + c - a) by linarith)]