import Mathlib

open Real Set

lemma lemma_1 (x : ℝ) (hx : 0 ≤ 3 - x ∧ 0 ≤ x + 1) (h : √(3 - x) - √(x + 1) > 1/ 2) :
    x < 7/8 := by
  have h1 : 0 ≤ 3 - x := hx.1
  have h2 : 0 ≤ x + 1 := hx.2
  have h3 : √(3 - x) > √(x + 1) + 1 / 2 := by linarith
  have h4 : (√(3 - x)) ^ 2 > (√(x + 1) + 1 / 2) ^ 2 := by
    have h5 : √(3 - x) ≥ 0 := by positivity
    have h6 : √(x + 1) + 1 / 2 ≥ 0 := by
      have h7 : √(x + 1) ≥ 0 := by positivity
      linarith
    nlinarith [h3, h5, h6]
  have h7 : (√(3 - x)) ^ 2 = 3 - x := Real.sq_sqrt (show 0 ≤ (3 - x : ℝ) by linarith)
  have h8 : (√(x + 1) + 1 / 2) ^ 2 = (√(x + 1)) ^ 2 + √(x + 1) + 1 / 4 := by
    nlinarith [Real.sqrt_nonneg (x + 1)]
  have h9 : (√(x + 1)) ^ 2 = x + 1 := Real.sq_sqrt (show 0 ≤ (x + 1 : ℝ) by linarith)
  rw [h7, h8, h9] at h4
  nlinarith [Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1),
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 - x : ℝ) by linarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1 : ℝ) by linarith),
          sq_nonneg (Real.sqrt (x + 1) - 3 / 4), sq_nonneg (x - 7 / 8)]

theorem inequalities_603985 :
    {x : ℝ | 0 ≤ 3 - x ∧ 0 ≤ x + 1 ∧ √(3 - x) - √(x + 1) > 1 / 2} = Ico (-1) (1 - √31 / 8) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · -- Assume x in {x | 0 ≤ 3 - x ∧ 0 ≤ x + 1 ∧ √(3 - x) - √(x + 1) > 1/2}, prove x in Ico (-1) (1 - √31 / 8)
    rintro ⟨h1, h2, h3⟩
    have h4 : x ≥ -1 := by linarith
    have h5 : x < 1 - Real.sqrt 31 / 8 := by
      have h6 : √(3 - x) - √(x + 1) > 1 / 2 := h3
      have h7 : √(3 - x) > √(x + 1) + 1 / 2 := by linarith
      have h8 : (√(3 - x)) ^ 2 > (√(x + 1) + 1 / 2) ^ 2 := by
        have h9 : √(3 - x) ≥ 0 := by positivity
        have h10 : √(x + 1) + 1 / 2 ≥ 0 := by
          have h11 : √(x + 1) ≥ 0 := by positivity
          linarith
        nlinarith [h7, h9, h10]
      have h9 : (√(3 - x)) ^ 2 = 3 - x := Real.sq_sqrt (by linarith)
      have h10 : (√(x + 1) + 1 / 2) ^ 2 = (√(x + 1)) ^ 2 + √(x + 1) + 1 / 4 := by
        nlinarith [Real.sqrt_nonneg (x + 1)]
      have h11 : (√(x + 1)) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
      rw [h9, h10, h11] at h8
      by_cases h13 : (7 / 4 : ℝ) - 2 * x ≥ 0
      · -- If $7/4 - 2x \geq 0$, then we can square both sides.
        have h14 : (7 / 4 - 2 * x) ^ 2 > (Real.sqrt (x + 1)) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (x + 1), sq_nonneg (7 / 4 - 2 * x), sq_nonneg (Real.sqrt (x + 1) - 3 / 4)]
        have h15 : (Real.sqrt (x + 1)) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
        have h16 : (7 / 4 - 2 * x) ^ 2 > x + 1 := by
          nlinarith [h14, h15]
        have h17 : 64 * x ^ 2 - 128 * x + 33 > 0 := by
          nlinarith
        have h18 : (x - (8 + Real.sqrt 31) / 8) * (x - (8 - Real.sqrt 31) / 8) > 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 31 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), Real.sqrt_nonneg 31]
        cases (mul_pos_iff.mp h18) with
        | inl h20 =>
          nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num)]
        | inr h21 =>
          nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num)]
      · -- If $\neg (7/4 - 2x \geq 0)$, i.e., $7/4 - 2x < 0$.
        have h13' : (7 / 4 - 2 * x) < 0 := by nlinarith
        nlinarith [Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1),
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 - x : ℝ) by linarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1 : ℝ) by linarith),
          sq_nonneg (Real.sqrt (x + 1) - 3 / 4), sq_nonneg (x - 7 / 8),
          Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num)]
    constructor
    · linarith
    · nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num)]
  · -- Assume x ∈ Ico (-1) (1 - √31 / 8), prove x in {x | 0 ≤ 3 - x ∧ 0 ≤ x + 1 ∧ √(3 - x) - √(x + 1) > 1/2}
    rintro ⟨h1, h2⟩
    have h3 : x ≥ -1 := by linarith
    have h4 : x < 1 - Real.sqrt 31 / 8 := by linarith
    have h5 : 3 - x > 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 31 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), Real.sqrt_nonneg 31]
    have h6 : x + 1 ≥ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 31 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), Real.sqrt_nonneg 31]
    constructor
    · -- Show $0 \leq 3 - x$.
      nlinarith
    constructor
    · -- Show $0 \leq x + 1$.
      nlinarith
    · -- Show $\sqrt{3-x} - \sqrt{x+1} > \frac{1}{2}$.
      have h7 : (√(3 - x) - √(x + 1)) > 1 / 2 := by
        have h8 : (√(3 - x)) ^ 2 > (√(x + 1) + 1 / 2) ^ 2 := by
          have h9' : (√(3 - x)) ^ 2 = 3 - x := Real.sq_sqrt (by linarith)
          have h10' : (√(x + 1) + 1 / 2) ^ 2 = (√(x + 1)) ^ 2 + √(x + 1) + 1 / 4 := by
            nlinarith [Real.sqrt_nonneg (x + 1)]
          have h11' : (√(x + 1)) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
          rw [h9', h10', h11']
          have h14 : (7 / 4 - 2 * x) > 0 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 31 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), Real.sqrt_nonneg 31]
          nlinarith [Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1),
            Real.sq_sqrt (show (0 : ℝ) ≤ (3 - x : ℝ) by linarith),
            Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1 : ℝ) by linarith),
            sq_nonneg (Real.sqrt (x + 1) - 3 / 4), sq_nonneg (x - 7 / 8),
            Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num)]
        have h9 : √(3 - x) ≥ 0 := by positivity
        have h10 : √(x + 1) + 1 / 2 ≥ 0 := by
          have h11 : √(x + 1) ≥ 0 := by positivity
          linarith
        nlinarith [Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1),
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 - x : ℝ) by linarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1 : ℝ) by linarith),
          sq_nonneg (Real.sqrt (x + 1) - 3 / 4), sq_nonneg (x - 7 / 8),
          Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num)]
      nlinarith