import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_1812 (a : ℝ) :
  (∀ x : ℝ, (cos x)^2 - 2*a*cos x + a^2 + a - 2 > 0) ↔
  a > (1 + sqrt 5)/2 ∨ a < (-3 - sqrt 13)/2 := by
  constructor
  · -- Assume the inequality holds for all x, prove the disjunction about a.
    intro h
    by_contra h1
    push_neg at h1
    rcases h1 with ⟨ha1, ha2⟩
    by_cases h3 : a > 1
    · -- Case where a > 1, so minimum occurs at cos x = 1
      have h4 := h 0
      have h5 : cos (0 : ℝ) = 1 := by
        simpa using Real.cos_zero
      rw [h5] at h4
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 13, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), 
          sq_nonneg (a - (1 + Real.sqrt 5)/2), sq_nonneg (a + (3 + Real.sqrt 13)/2)
        ]
    · -- Case where a ≤ 1
      by_cases h4 : a < -1
      · -- Case where a < -1, so minimum occurs at cos x = -1
        have h5 := h (Real.pi)
        have h6 : cos (Real.pi : ℝ) = -1 := by
          simpa using Real.cos_pi
        rw [h6] at h5
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 13, 
            Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), 
            sq_nonneg (a - (1 + Real.sqrt 5)/2), sq_nonneg (a + (3 + Real.sqrt 13)/2)
          ]
      · -- Case where -1 ≤ a ≤ 1
        have h7 : -1 ≤ a := by nlinarith
        have h8 : a ≤ 1 := by nlinarith
        have h9 := h (0)
        have h5 : cos (0 : ℝ) = 1 := by
          simpa using Real.cos_zero
        rw [h5] at h9
        have h10 := h (Real.pi)
        have h6 : cos (Real.pi : ℝ) = -1 := by
          simpa using Real.cos_pi
        rw [h6] at h10
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 13, 
            Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), 
            sq_nonneg (a - (1 + Real.sqrt 5)/2), sq_nonneg (a + (3 + Real.sqrt 13)/2)
          ]
  · -- Assume the disjunction, prove the inequality.
    intro h
    rcases h with (ha | ha)
    · -- Case a > (1 + sqrt 5)/2
      intro x
      have h1 : -1 ≤ cos x := Real.neg_one_le_cos x
      have h2 : cos x ≤ 1 := Real.cos_le_one x
      nlinarith [sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), sq_nonneg (cos x - a),
        Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
        Real.sqrt_pos.mpr (show (5: ℝ) > 0 by norm_num), 
        h1, h2, sq_nonneg (a - (1 + Real.sqrt 5)/2)
      ]
    · -- Case a < (-3 - sqrt 13)/2
      intro x
      have h1 : -1 ≤ cos x := Real.neg_one_le_cos x
      have h2 : cos x ≤ 1 := Real.cos_le_one x
      nlinarith [sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), sq_nonneg (cos x - a),
        Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
        Real.sqrt_pos.mpr (show (5: ℝ) > 0 by norm_num), 
        Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), 
        Real.sqrt_pos.mpr (show (13: ℝ) > 0 by norm_num), 
        h1, h2, sq_nonneg (a + (3 + Real.sqrt 13)/2)
      ]