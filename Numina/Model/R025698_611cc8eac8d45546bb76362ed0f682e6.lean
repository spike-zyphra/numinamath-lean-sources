import Mathlib

open BigOperators Real

theorem inequalities_34111 :
  IsLeast {t : ℝ | ∃ a b c d e : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ e ≥ 0 ∧ a + b + c + d + e > 0 ∧
    a + c = t * b ∧ b + d = t * c ∧ c + e = t * d} (Real.sqrt 2) := by
  constructor
  · -- First: show that sqrt 2 is in the set.
    use 0, 1, Real.sqrt 2, 1, 0 
    constructor
    · -- a = 0 ≥ 0 
      norm_num
    constructor
    · -- b = 1 ≥ 0 
      norm_num
    constructor
    · -- c = sqrt 2 ≥ 0 
      positivity
    constructor
    · -- d = 1 ≥ 0 
      norm_num
    constructor
    · -- e = 0 ≥ 0 
      norm_num
    constructor
    · -- Show that a + b + c + d + e > 0
      have h1 : Real.sqrt 2 > 0 := by positivity 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor
    · -- a + c = Real.sqrt 2 * b 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor
    · -- b + d = Real.sqrt 2 * c
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num) 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- c + e = Real.sqrt 2 * d
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that sqrt 2 is the least element in the set
    intro t ht 
    rcases ht with ⟨a, b, c, d, e, ha, hb, hc, hd, he, h1, h2, h3, h4⟩ 
    by_contra h 
    push_neg at h 
    have h5 : t ^ 2 ≥ 2 := by
      nlinarith [sq_nonneg (c - t * b), sq_nonneg (d - t * c), sq_nonneg (e - t * d), sq_nonneg (a - c), sq_nonneg (c - e), sq_nonneg (b - d), 
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc hd, mul_nonneg hd he, 
          sq_nonneg (t ^ 2 - 2), sq_nonneg (t ^ 2 - 1), sq_nonneg (t - Real.sqrt 2), sq_nonneg (t + Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h11 : t ^ 2 < (2 : ℝ) := by 
      have h7 : t < Real.sqrt 2 := by linarith 
      have h12 : t ^ 2 < (Real.sqrt 2 : ℝ) ^ 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - t), sq_nonneg (t + Real.sqrt 2)]
      have h13 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      nlinarith 
    linarith