import Mathlib

theorem algebra_8036 {a b c : ℝ} (ha : 5 * a + 4 * b - 3 * c - 6 ≥ 0) (hb : 3 * a + 3 * b - 2 * c ≥ 0)
    (hc : a + b - 2012 ≥ 0) (hd : 2012 - a - b ≥ 0) (h : Real.sqrt (5 * a + 4 * b - 3 * c - 6) +
    Real.sqrt (3 * a + 3 * b - 2 * c) - 2 * Real.sqrt (a + b - 2012) + 3 * Real.sqrt (2012 - a - b) = 0) :
    a = 1012 ∧ b = 1000 ∧ c = 3018 := by
  have h1 : Real.sqrt (5 * a + 4 * b - 3 * c - 6) + Real.sqrt (3 * a + 3 * b - 2 * c) =
      2 * Real.sqrt (a + b - 2012) - 3 * Real.sqrt (2012 - a - b) := by linarith
  have h2 : (Real.sqrt (5 * a + 4 * b - 3 * c - 6) + Real.sqrt (3 * a + 3 * b - 2 * c)) ^ 2 =
    (2 * Real.sqrt (a + b - 2012) - 3 * Real.sqrt (2012 - a - b)) ^ 2 := by
    rw [h1]
  have h3 : (Real.sqrt (5 * a + 4 * b - 3 * c - 6) + Real.sqrt (3 * a + 3 * b - 2 * c)) ^ 2 =
      (Real.sqrt (5 * a + 4 * b - 3 * c - 6)) ^ 2 + (Real.sqrt (3 * a + 3 * b - 2 * c)) ^ 2 +
      2 * (Real.sqrt (5 * a + 4 * b - 3 * c - 6) * Real.sqrt (3 * a + 3 * b - 2 * c)) := by ring
  have h4 : (2 * Real.sqrt (a + b - 2012) - 3 * Real.sqrt (2012 - a - b)) ^ 2 =
      4 * (Real.sqrt (a + b - 2012)) ^ 2 + 9 * (Real.sqrt (2012 - a - b)) ^ 2 - 12 * (Real.sqrt (a + b - 2012) * Real.sqrt (2012 - a - b)) := by ring
  rw [h3, h4] at h2
  have h5 : (Real.sqrt (5 * a + 4 * b - 3 * c - 6)) ^ 2 = 5 * a + 4 * b - 3 * c - 6 := by 
    rw [Real.sq_sqrt]
    linarith
  have h6 : (Real.sqrt (3 * a + 3 * b - 2 * c)) ^ 2 = 3 * a + 3 * b - 2 * c := by
    rw [Real.sq_sqrt]
    linarith
  have h7 : (Real.sqrt (a + b - 2012)) ^ 2 = a + b - 2012 := by 
    rw [Real.sq_sqrt]
    linarith
  have h8 : (Real.sqrt (2012 - a - b)) ^ 2 = 2012 - a - b := by 
    rw [Real.sq_sqrt]
    linarith
  rw [h5, h6, h7, h8] at h2
  have ha' : 5 * a + 4 * b - 3 * c - 6 = 0 := by
    nlinarith [Real.sqrt_nonneg (5 * a + 4 * b - 3 * c - 6), Real.sqrt_nonneg (3 * a + 3 * b - 2 * c),
          Real.sqrt_nonneg (a + b - 2012), Real.sqrt_nonneg (2012 - a - b),
          sq_nonneg (Real.sqrt (5 * a + 4 * b - 3 * c - 6) - Real.sqrt (3 * a + 3 * b - 2 * c)),
          sq_nonneg (Real.sqrt (a + b - 2012) - Real.sqrt (2012 - a - b))
        ]
  have hb' : 3 * a + 3 * b - 2 * c = 0 := by
    nlinarith [Real.sqrt_nonneg (5 * a + 4 * b - 3 * c - 6), Real.sqrt_nonneg (3 * a + 3 * b - 2 * c),
          Real.sqrt_nonneg (a + b - 2012), Real.sqrt_nonneg (2012 - a - b),
          sq_nonneg (Real.sqrt (5 * a + 4 * b - 3 * c - 6) - Real.sqrt (3 * a + 3 * b - 2 * c)),
          sq_nonneg (Real.sqrt (a + b - 2012) - Real.sqrt (2012 - a - b))
        ]
  have ha'' : a = 1012 := by
    nlinarith [Real.sqrt_nonneg (5 * a + 4 * b - 3 * c - 6), Real.sqrt_nonneg (3 * a + 3 * b - 2 * c),
          Real.sqrt_nonneg (a + b - 2012), Real.sqrt_nonneg (2012 - a - b),
          sq_nonneg (Real.sqrt (5 * a + 4 * b - 3 * c - 6) - Real.sqrt (3 * a + 3 * b - 2 * c)),
          sq_nonneg (Real.sqrt (a + b - 2012) - Real.sqrt (2012 - a - b)),
          ha', hb'
        ]
  have hb'' : b = 1000 := by 
    nlinarith [Real.sqrt_nonneg (5 * a + 4 * b - 3 * c - 6), Real.sqrt_nonneg (3 * a + 3 * b - 2 * c),
          Real.sqrt_nonneg (a + b - 2012), Real.sqrt_nonneg (2012 - a - b),
          sq_nonneg (Real.sqrt (5 * a + 4 * b - 3 * c - 6) - Real.sqrt (3 * a + 3 * b - 2 * c)),
          sq_nonneg (Real.sqrt (a + b - 2012) - Real.sqrt (2012 - a - b)),
          ha', hb'
        ]
  have hc' : c = 3018 := by
    nlinarith [ha', hb']
  exact ⟨ha'', hb'', hc'⟩