import Mathlib

open Real

theorem algebra_16761 {a b c d : ℝ}
    (ha : a = √2 + √3 + √6)
    (hb : b = -√2 + √3 + √6)
    (hc : c = √2 - √3 + √6)
    (hd : d = -√2 - √3 + √6) :
    ((1 / a + 1 / b + 1 / c + 1 / d) ^ 2 = 96 / 529) := by
  have ha' : a = √2 + √3 + √6 := ha
  have hb' : b = -√2 + √3 + √6 := hb
  have hc' : c = √2 - √3 + √6 := hc
  have hd' : d = -√2 - √3 + √6 := hd
  have h1 : 1 / a + 1 / b + 1 / c + 1 / d = (4 * Real.sqrt 6) / (a * b * c * d) := by
    rw [ha', hb', hc', hd']
    have h9 : 1 / (√2 + √3 + √6) + 1 / (-√2 + √3 + √6) + 1 / (√2 - √3 + √6) + 1 / (-√2 - √3 + √6) =
        ((-√2 + √3 + √6) * (√2 - √3 + √6) * (-√2 - √3 + √6) + (√2 + √3 + √6) * (√2 - √3 + √6) * (-√2 - √3 + √6) + (√2 + √3 + √6) * (-√2 + √3 + √6) * (-√2 - √3 + √6) + (√2 + √3 + √6) * (-√2 + √3 + √6) * (√2 - √3 + √6)) / ((√2 + √3 + √6) * (-√2 + √3 + √6) * (√2 - √3 + √6) * (-√2 - √3 + √6)) := by
      field_simp [show (√2 + √3 + √6) ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (2:ℝ) by norm_num : (2:ℝ) > 0), Real.sqrt_pos.mpr (show (0:ℝ) < (3:ℝ) by norm_num : (3:ℝ) > 0), Real.sqrt_pos.mpr (show (0:ℝ) < (6:ℝ) by norm_num : (6:ℝ) > 0),
            Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
            mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 6)]
      , show (-√2 + √3 + √6) ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (2:ℝ) by norm_num : (2:ℝ) > 0), Real.sqrt_pos.mpr (show (0:ℝ) < (3:ℝ) by norm_num : (3:ℝ) > 0), Real.sqrt_pos.mpr (show (0:ℝ) < (6:ℝ) by norm_num : (6:ℝ) > 0),
            Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
            mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 6)]
      , show (√2 - √3 + √6) ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (2:ℝ) by norm_num : (2:ℝ) > 0), Real.sqrt_pos.mpr (show (0:ℝ) < (3:ℝ) by norm_num : (3:ℝ) > 0), Real.sqrt_pos.mpr (show (0:ℝ) < (6:ℝ) by norm_num : (6:ℝ) > 0),
            Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
            mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 6)]
      , show (-√2 - √3 + √6) ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (2:ℝ) by norm_num : (2:ℝ) > 0), Real.sqrt_pos.mpr (show (0:ℝ) < (3:ℝ) by norm_num : (3:ℝ) > 0), Real.sqrt_pos.mpr (show (0:ℝ) < (6:ℝ) by norm_num : (6:ℝ) > 0),
            Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
            mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 6)]
      ]
      <;> ring
    rw [h9]
    have h3' : (√2 + √3 + √6) * (-√2 + √3 + √6) * (√2 - √3 + √6) * (-√2 - √3 + √6) = -23 := by
      nlinarith [ Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6),
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 6),
          sq_nonneg (√2 - √3), sq_nonneg (√2 - √6), sq_nonneg (√3 - √6),
          Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6,
          mul_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
    have h12 : (-√2 + √3 + √6) * (√2 - √3 + √6) * (-√2 - √3 + √6) + (√2 + √3 + √6) * (√2 - √3 + √6) * (-√2 - √3 + √6) + (√2 + √3 + √6) * (-√2 + √3 + √6) * (-√2 - √3 + √6) + (√2 + √3 + √6) * (-√2 + √3 + √6) * (√2 - √3 + √6) = 4 * Real.sqrt 6 := by
      nlinarith [ Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
              Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
              Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
              mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3),
              mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6),
              mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 6),
              sq_nonneg (√2 - √3), sq_nonneg (√2 - √6), sq_nonneg (√3 - √6),
              Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6,
              mul_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
    rw [h12, h3']
    all_goals ring_nf
  have h2 : a * b * c * d = -23 := by
    rw [ha', hb', hc', hd']
    nlinarith [ Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6),
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 6),
          sq_nonneg (√2 - √3), sq_nonneg (√2 - √6), sq_nonneg (√3 - √6),
          Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6,
          mul_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
  rw [h1, h2]
  have h3 : (4 * Real.sqrt 6 / (-23 : ℝ)) ^ 2 = 96 / 529 := by
    have h4 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)
    field_simp
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  linarith