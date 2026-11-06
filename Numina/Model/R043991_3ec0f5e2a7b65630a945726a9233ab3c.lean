import Mathlib

lemma lemma_1 (x y : ℝ) (hy : 0 < y) : x^2 / y + 4 * y ≥ 4 * x := by
  have h1 : 0 < y := hy
  have h23 : x^2 / y + 4 * y - 4 * x ≥ 0 := by
    have h3 : x^2 / y + 4 * y - 4 * x = (x^2 + 4 * y^2 - 4 * x * y) / y := by
      field_simp
      ring
    rw [h3]
    have h45 : x^2 + 4 * y^2 - 4 * x * y ≥ 0 := by
      have h46 : x^2 + 4 * y^2 - 4 * x * y = (x - 2 * y) ^ 2 := by
        ring
      rw [h46]
      apply sq_nonneg
    apply div_nonneg
    all_goals nlinarith
  linarith

theorem inequalities_55931 (a b c d e : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) (he : 1 < e) :
    20 ≤ a^2 / (c - 1) + b^2 / (d - 1) + c^2 / (e - 1) + d^2 / (a - 1) + e^2 / (b - 1) := by

  have h1 : 0 < c - 1 := by linarith
  have h2 : 0 < d - 1 := by linarith
  have h3 : 0 < e - 1 := by linarith
  have h4 : 0 < a - 1 := by linarith
  have h5 : 0 < b - 1 := by linarith

  have h6 : a ^ 2 / (c - 1) + 4 * (c - 1) ≥ 4 * a := by
    apply lemma_1
    all_goals nlinarith
  
  have h7 : b ^ 2 / (d - 1) + 4 * (d - 1) ≥ 4 * b := by
    apply lemma_1
    all_goals nlinarith
  
  have h8 : c ^ 2 / (e - 1) + 4 * (e - 1) ≥ 4 * c := by
    apply lemma_1
    all_goals nlinarith
  
  have h9 : d ^ 2 / (a - 1) + 4 * (a - 1) ≥ 4 * d := by
    apply lemma_1
    all_goals nlinarith
  
  have h10 : e ^ 2 / (b - 1) + 4 * (b - 1) ≥ 4 * e := by
    apply lemma_1
    all_goals nlinarith
  
  nlinarith