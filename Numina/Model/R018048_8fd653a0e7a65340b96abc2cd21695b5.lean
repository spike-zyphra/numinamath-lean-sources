import Mathlib


theorem algebra_305112 : {x : ℝ | abs (x ^ 2 - 1) = (1 / 10) * (x + 11 / 10)}.ncard = 4 := by
  have h1 : {x : ℝ | abs (x ^ 2 - 1) = (1 / 10) * (x + 11 / 10)} = 
    { (1 + Real.sqrt 445) / 20, (1 - Real.sqrt 445) / 20, (-1 + Real.sqrt 357) / 20, (-1 - Real.sqrt 357) / 20 } := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume abs (x^2 - 1) = (1/10) * (x + 11/10), show x is one of the four roots
      intro h_eq
      by_cases h2 : x^2 - 1 ≥ 0
      · -- If x^2 - 1 ≥ 0, then abs (x^2 - 1) = x^2 - 1
        rw [abs_of_nonneg h2] at h_eq
        have h3 : 100 * x^2 - 10 * x - 111 = 0 := by
          nlinarith
        have h4 : (x - (1 + Real.sqrt 445) / 20) * (x - (1 - Real.sqrt 445) / 20) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (by norm_num : (445 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (445 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 h4) with h5 h6
        · -- x = (1 + Real.sqrt 445) / 20
          left
          linarith
        · -- x = (1 - Real.sqrt 445) / 20
          right
          left
          linarith
      · -- If x^2 - 1 < 0, then abs (x^2 - 1) = 1 - x^2
        rw [abs_of_neg (show x^2 - 1 < 0 by linarith)] at h_eq
        have h3 : 100 * x^2 + 10 * x - 89 = 0 := by
          nlinarith
        have h4 : (x - (-1 + Real.sqrt 357) / 20) * (x - (-1 - Real.sqrt 357) / 20) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (by norm_num : (357 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (357 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 h4) with h5 h6
        · -- x = (-1 + Real.sqrt 357) / 20
          right
          right
          left
          linarith
        · -- x = (-1 - Real.sqrt 357) / 20
          right
          right
          right
          linarith
    · -- Assume x is one of the four roots, show abs (x^2 - 1) = (1/10) * (x + 11/10)
      rintro (h_eq | h_eq | h_eq | h_eq)
      · -- x = (1 + Real.sqrt 445) / 20
        rw [h_eq]
        have h2 : ((1 + Real.sqrt 445) / 20 : ℝ) ^ 2 - 1 ≥ 0 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < 445 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (445 : ℝ) by norm_num)]
        rw [abs_of_nonneg h2]
        nlinarith [Real.sqrt_pos.mpr (show 0 < 445 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (445 : ℝ) by norm_num)]
      · -- x = (1 - Real.sqrt 445) / 20
        rw [h_eq]
        have h2 : ((1 - Real.sqrt 445) / 20 : ℝ) ^ 2 - 1 ≥ 0 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < 445 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (445 : ℝ) by norm_num)]
        rw [abs_of_nonneg h2]
        nlinarith [Real.sqrt_pos.mpr (show 0 < 445 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (445 : ℝ) by norm_num)]
      · -- x = (-1 + Real.sqrt 357) / 20
        rw [h_eq]
        have h2 : ((-1 + Real.sqrt 357) / 20 : ℝ) ^ 2 - 1 < 0 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < 357 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (357 : ℝ) by norm_num)]
        rw [abs_of_neg h2]
        nlinarith [Real.sqrt_pos.mpr (show 0 < 357 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (357 : ℝ) by norm_num)]
      · -- x = (-1 - Real.sqrt 357) / 20
        rw [h_eq]
        have h2 : ((-1 - Real.sqrt 357) / 20 : ℝ) ^ 2 - 1 < 0 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < 357 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (357 : ℝ) by norm_num)]
        rw [abs_of_neg h2]
        nlinarith [Real.sqrt_pos.mpr (show 0 < 357 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (357 : ℝ) by norm_num)]
  rw [h1]
  have h2 : Real.sqrt 445 > 0 := by
    positivity
  have h3 : Real.sqrt 357 > 0 := by
    positivity
  have h4 : (1 + Real.sqrt 445) / 20 ≠ (1 - Real.sqrt 445) / 20 := by
    intro h
    have h5 : Real.sqrt 445 = 0 := by
      nlinarith
    linarith [show Real.sqrt 445 > 0 by positivity]
  have h5 : (1 + Real.sqrt 445) / 20 ≠ (-1 + Real.sqrt 357) / 20 := by
    intro h
    have h7 : (1 + Real.sqrt 445) = (-1 + Real.sqrt 357) := by
      linarith
    nlinarith [Real.sqrt_nonneg 445, Real.sqrt_nonneg 357, Real.sq_sqrt (show (0 : ℝ) ≤ (445 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (357 : ℝ) by norm_num), sq_nonneg (Real.sqrt 445 - Real.sqrt 357)]
  have h6 : (1 + Real.sqrt 445) / 20 ≠ (-1 - Real.sqrt 357) / 20 := by
    intro h
    have h7 : (1 + Real.sqrt 445) = (-1 - Real.sqrt 357) := by
      linarith
    nlinarith [Real.sqrt_nonneg 445, Real.sqrt_nonneg 357, Real.sq_sqrt (show (0 : ℝ) ≤ (445 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (357 : ℝ) by norm_num), sq_nonneg (Real.sqrt 445 + Real.sqrt 357)
      ]
  have h7 : (1 - Real.sqrt 445) / 20 ≠ (-1 + Real.sqrt 357) / 20 := by
    intro h
    have h8 : (1 - Real.sqrt 445) = (-1 + Real.sqrt 357) := by
      linarith
    nlinarith [Real.sqrt_nonneg 445, Real.sqrt_nonneg 357, Real.sq_sqrt (show (0 : ℝ) ≤ (445 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (357 : ℝ) by norm_num), sq_nonneg (Real.sqrt 445 + Real.sqrt 357)
      ]
  have h8 : (1 - Real.sqrt 445) / 20 ≠ (-1 - Real.sqrt 357) / 20 := by
    intro h
    have h9 : (1 - Real.sqrt 445) = (-1 - Real.sqrt 357) := by
      linarith
    nlinarith [Real.sqrt_nonneg 445, Real.sqrt_nonneg 357, Real.sq_sqrt (show (0 : ℝ) ≤ (445 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (357 : ℝ) by norm_num), sq_nonneg (Real.sqrt 445 + Real.sqrt 357)
      ]
  have h9 : (-1 + Real.sqrt 357) / 20 ≠ (-1 - Real.sqrt 357) / 20 := by
    intro h
    have h10 : Real.sqrt 357 = 0 := by
      nlinarith
    linarith [show Real.sqrt 357 > 0 by positivity]
  rw [Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals
    try { 
      norm_num [h4, h5, h6, h7, h8, h9]
    }