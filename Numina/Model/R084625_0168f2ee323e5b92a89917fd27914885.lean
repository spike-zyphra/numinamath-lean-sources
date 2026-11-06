import Mathlib

open Real

theorem inequalities_118 {a b c : ℝ}
    (ha : a = sqrt 2 - 1) (hb : b = sqrt 3 - sqrt 2) (hc : c = sqrt 6 - 2) :
    b < a ∧ a < c := by
  have h1 : b < a := by
    rw [hb, ha]
    have h2 : sqrt 3 + 1 < 2 * sqrt 2 := by
      have h2' : (sqrt 3 + 1) ^ 2 < (2 * sqrt 2) ^ 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, 
          Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num), 
          sq_nonneg (sqrt 3 - sqrt 2), sq_nonneg (sqrt 2 - 1), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), 
          mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 3 by norm_num), 
          mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 6 by norm_num)]
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
        mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), 
        sq_nonneg (sqrt 3 - sqrt 2)
      ]
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3),
      Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num),
      Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, 
      sq_nonneg (sqrt 2 - 1)
    ]
  have h2 : a < c := by
    rw [ha, hc]
    have h3 : sqrt 2 + 1 < sqrt 6 := by
      have h4 : (sqrt 2 + 1) ^ 2 < (sqrt 6) ^ 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
          Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, 
          Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (6 : ℝ) by norm_num), 
          sq_nonneg (sqrt 6 - sqrt 2), 
          sq_nonneg (sqrt 2 - 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6), 
          mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 6 by norm_num)
        ]
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
        mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6), 
        Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (6 : ℝ) by norm_num),
        sq_nonneg (sqrt 6 - sqrt 2)
      ]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
      Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (6 : ℝ) by norm_num), 
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6),
      sq_nonneg (sqrt 2 - 1)
    ]
  constructor
  · linarith [h1]
  · linarith [h2]
  <;> try { norm_num }
  <;> try { nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6] }
  <;> try { exact_mod_cast h1 }
  <;> try { exact_mod_cast h2 }
  <;> try { tauto }
  <;> try { linarith }
  <;> try { linarith }
  <;> try { nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6] }
  <;> try { tauto }