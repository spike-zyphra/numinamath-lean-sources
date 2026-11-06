import Mathlib

open Real Set

lemma lemma_1 (x : ℝ) (hx : x ∈ Icc 0 1) : sqrt (3 * x + 1) ≥ x + 1 := by
  rcases hx with ⟨hx0, hx1⟩
  have h1 : 0 ≤ x := by linarith
  have h2 : x ≤ 1 := by linarith
  have h3 : 0 ≤ 3 * x + 1 := by nlinarith
  have h4 : (x + 1) ^ 2 ≤ (3 * x + 1 : ℝ) := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x), sq_nonneg (x - 1)]
  have h5 : (x + 1 : ℝ) ≤ sqrt (3 * x + 1) := by
    have h6 : (x + 1 : ℝ) ^ 2 ≤ (3 * x + 1 : ℝ) := h4
    have h7 : 0 ≤ (x + 1 : ℝ) := by nlinarith
    have h8 : (x + 1 : ℝ) ≤ sqrt (3 * x + 1) := by
      nlinarith [Real.sqrt_nonneg (3 * x + 1), Real.sq_sqrt (show 0 ≤ (3 * x + 1 : ℝ) by nlinarith)]
    linarith
  linarith


theorem algebra_118138 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    ⌊Real.sqrt (3 * a + 1) + Real.sqrt (3 * b + 1) + Real.sqrt (3 * c + 1)⌋ = 4 := by

  have h1 : 0 < a := by linarith
  have h2 : 0 < b := by linarith
  have h3 : 0 < c := by linarith
  have ha1 : a ≤ 1 := by nlinarith
  have hb1 : b ≤ 1 := by nlinarith
  have hc1 : c ≤ 1 := by nlinarith

  have h4 : Real.sqrt (3 * a + 1) + Real.sqrt (3 * b + 1) + Real.sqrt (3 * c + 1) ≥ 4 := by
    have h5 : Real.sqrt (3 * a + 1) ≥ a + 1 := by
      have ha2 : a ∈ Icc (0 : ℝ) 1 := by
        constructor
        · linarith
        · linarith
      apply lemma_1 a ha2
    have h6 : Real.sqrt (3 * b + 1) ≥ b + 1 := by
      have hb2 : b ∈ Icc (0 : ℝ) 1 := by
        constructor
        · linarith
        · linarith
      apply lemma_1 b hb2
    have h7 : Real.sqrt (3 * c + 1) ≥ c + 1 := by
      have hc2 : c ∈ Icc (0 : ℝ) 1 := by
        constructor
        · linarith
        · linarith
      apply lemma_1 c hc2
    nlinarith [h5, h6, h7, show a + b + c = 1 by linarith]

  have h8 : Real.sqrt (3 * a + 1) + Real.sqrt (3 * b + 1) + Real.sqrt (3 * c + 1) < 5 := by

    have h9 : Real.sqrt (3 * a + 1) ≤ (3 * a + 2)/2 := by
      nlinarith [Real.sqrt_nonneg (3 * a + 1), Real.sq_sqrt (show 0 ≤ (3 * a + 1 : ℝ) by nlinarith), sq_nonneg (Real.sqrt (3 * a + 1) - (3 * a + 2)/2), sq_nonneg (a - 1)]
    have h10 : Real.sqrt (3 * b + 1) ≤ (3 * b + 2)/2 := by
      nlinarith [Real.sqrt_nonneg (3 * b + 1), Real.sq_sqrt (show 0 ≤ (3 * b + 1 : ℝ) by nlinarith), sq_nonneg (Real.sqrt (3 * b + 1) - (3 * b + 2)/2), sq_nonneg (b - 1)]
    have h11 : Real.sqrt (3 * c + 1) ≤ (3 * c + 2)/2 := by
      nlinarith [Real.sqrt_nonneg (3 * c + 1), Real.sq_sqrt (show 0 ≤ (3 * c + 1 : ℝ) by nlinarith), sq_nonneg (Real.sqrt (3 * c + 1) - (3 * c + 2)/2), sq_nonneg (c - 1)]
    nlinarith [h9, h10, h11, show a + b + c = 1 by linarith]

  have h9 : 4 ≤ Real.sqrt (3 * a + 1) + Real.sqrt (3 * b + 1) + Real.sqrt (3 * c + 1) := by linarith [h4]
  have h10 : Real.sqrt (3 * a + 1) + Real.sqrt (3 * b + 1) + Real.sqrt (3 * c + 1) < 5 := by linarith [h8]

  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (3 * a + 1), Real.sqrt_nonneg (3 * b + 1), Real.sqrt_nonneg (3 * c + 1)]