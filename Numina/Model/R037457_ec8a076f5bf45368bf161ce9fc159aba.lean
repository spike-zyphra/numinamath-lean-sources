import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_173489 {a b : ℝ} (ha : 0 < a) (hb : a < b)
  (x : ℝ) :
  (b - a) / (b + a) ≤ (b + a * sin x) / (b - a * sin x) ∧
  (b + a * sin x) / (b - a * sin x) ≤ (b + a) / (b - a) := by
  have h1 : 0 < b := by linarith
  have h2 : 0 < b + a := by linarith
  have h3 : 0 < b - a * sin x := by
    nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_le_one x, Real.neg_one_le_sin x]
  constructor
  · -- Prove: (b - a) / (b + a) ≤ (b + a * sin x) / (b - a * sin x)
    have hx1 : -1 ≤ sin x := by linarith [Real.neg_one_le_sin x, Real.sin_le_one x]
    have hx2 : sin x ≤ 1 := by linarith [Real.sin_le_one x]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [Real.sin_le_one x, Real.neg_one_le_sin x, mul_pos ha (show 0 < b - a by linarith), mul_pos ha (show 0 < b + a by linarith)]
  · -- Prove: (b + a * sin x) / (b - a * sin x) ≤ (b + a) / (b - a)
    have hx1 : -1 ≤ sin x := by linarith [Real.neg_one_le_sin x, Real.sin_le_one x]
    have hx2 : sin x ≤ 1 := by linarith [Real.sin_le_one x]
    have h7 : 0 < b - a := by linarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [Real.sin_le_one x, Real.neg_one_le_sin x, mul_pos ha (show 0 < b - a by linarith), mul_pos ha (show 0 < b + a by linarith)]