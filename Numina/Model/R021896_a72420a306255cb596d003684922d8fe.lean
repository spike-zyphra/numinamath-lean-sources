import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_171184 (f : ℝ → ℝ) (hf : f = λ x => 25 * 2^x - 10^x + 5^x) :
    {x | f x > 25} = {x | 0 < x ∧ x < 2} := by
  ext x
  simp [hf]
  constructor
  · -- First, prove that if $25 * 2^x - 10^x + 5^x > 25$, then $0 < x ∧ x < 2$.
    intro h
    have h2 : x > (0 : ℝ) := by
      by_contra h3
      push_neg at h3
      have h7 : x ≤ (0 : ℝ) := by nlinarith
      have h9 : 25 * (2 : ℝ) ^ x - (10 : ℝ) ^ x + (5 : ℝ) ^ x ≤ (25 : ℝ) := by
      -- Show $f(x) \leq 25$ for x \leq 0.
        have h4 : x ≤ (0 : ℝ) := h7
        have h10 : (2 : ℝ) ^ x ≤ (1 : ℝ) := by
          have h11a : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (0 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le
            all_goals linarith
          have h11b : (2 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
            simp
          have h11c : (2 : ℝ) ^ x ≤ (1 : ℝ) := by
            linarith [h11a, h11b]
          linarith
        have h11 : (5 : ℝ) ^ x ≤ (1 : ℝ) := by
          have h12a : (5 : ℝ) ^ x ≤ (5 : ℝ) ^ (0 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le
            all_goals linarith
          have h12b : (5 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
            simp
          have h12c : (5 : ℝ) ^ x ≤ (1 : ℝ) := by
            linarith [h12a, h12b]
          linarith
        have h12 : 25 * (2 : ℝ) ^ x - (10 : ℝ) ^ x + (5 : ℝ) ^ x ≤ (25 : ℝ) := by
          have h4a : (10 : ℝ) ^ x = (2 : ℝ) ^ x * (5 : ℝ) ^ x := by
            rw [show (10 : ℝ) ^ x = (2 * (5 : ℝ)) ^ x by ring]
            rw [show (2 * (5 : ℝ)) ^ x = (2 : ℝ) ^ x * (5 : ℝ) ^ x by
                rw [← Real.mul_rpow]
                all_goals linarith
            ]
          rw [h4a]
          nlinarith [sq_nonneg ((2 : ℝ) ^ x - (1 : ℝ)), sq_nonneg ((5 : ℝ) ^ x - (1 : ℝ)), 
            (show (2 : ℝ) ^ x > 0 by positivity), 
            (show (5 : ℝ) ^ x > 0 by positivity), 
            mul_pos (show (2 : ℝ) ^ x > 0 by positivity) (show (5 : ℝ) ^ x > 0 by positivity)]
        nlinarith
      nlinarith
    have h3 : x < (2 : ℝ) := by
      by_contra h4
      push_neg at h4
      have h4a : x ≥ (2 : ℝ) := by nlinarith
      have h10 : 25 * (2 : ℝ) ^ x - (10 : ℝ) ^ x + (5 : ℝ) ^ x ≤ (25 : ℝ) := by
        have h4a : x ≥ (2 : ℝ) := by nlinarith
        have h11 : 25 * (2 : ℝ) ^ x - (10 : ℝ) ^ x + (5 : ℝ) ^ x ≤ (25 : ℝ) := by
          have h12 : (10 : ℝ) ^ x = (2 : ℝ) ^ x * (5 : ℝ) ^ x := by
            rw [show (10 : ℝ) ^ x = (2 * (5 : ℝ)) ^ x by ring]
            rw [show (2 * (5 : ℝ)) ^ x = (2 : ℝ) ^ x * (5 : ℝ) ^ x by
                rw [← Real.mul_rpow]
                all_goals linarith
            ]
          rw [h12]
          nlinarith [sq_nonneg ((2 : ℝ) ^ x - (4 : ℝ)), sq_nonneg ((5 : ℝ) ^ x - (25 : ℝ)), 
            (show (2 : ℝ) ^ x ≥ (4 : ℝ) by
              have h8 : (2 : ℝ) ^ x ≥ (2 : ℝ) ^ (2 : ℝ) := by
                apply Real.rpow_le_rpow_of_exponent_le
                all_goals linarith
              have h8a : (2 : ℝ) ^ (2 : ℝ) = (4 : ℝ) := by norm_num
              nlinarith
            ), 
            (show (5 : ℝ) ^ x ≥ (25 : ℝ) by
              have h9 : (5 : ℝ) ^ x ≥ (5 : ℝ) ^ (2 : ℝ) := by
                apply Real.rpow_le_rpow_of_exponent_le
                all_goals linarith
              have h9a : (5 : ℝ) ^ (2 : ℝ) = (25 : ℝ) := by norm_num
              nlinarith
            ), 
            (show (2 : ℝ) ^ x > 0 by positivity), 
            (show (5 : ℝ) ^ x > 0 by positivity)
          ]
        linarith
      nlinarith
    exact ⟨h2, h3⟩
  · -- Now the reverse direction: if $0 < x ∧ x < 2$, then $25 * 2^x - 10^x + 5^x > 25$.
    rintro ⟨h1, h2⟩
    have h3 : 25 * (2 : ℝ) ^ x - (10 : ℝ) ^ x + (5 : ℝ) ^ x > (25 : ℝ) := by
      have h4a : (2 : ℝ) ^ x > (1 : ℝ) := by
        have h7a : x > (0 : ℝ) := by linarith
        have h7b : (2 : ℝ) ^ x > (2 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h7c : (2 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
          simp
        nlinarith
      have h6a : (5 : ℝ) ^ x > (1 : ℝ) := by
        have h6a1 : x > (0 : ℝ) := by linarith
        have h6a2 : (5 : ℝ) ^ x > (5 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h6a3 : (5 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
          simp
        nlinarith
      have h9a : (2 : ℝ) ^ x < (4 : ℝ) := by
        have h9a1 : x < (2 : ℝ) := by linarith
        have h9a2 : (2 : ℝ) ^ x < (2 : ℝ) ^ (2 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h9a3 : (2 : ℝ) ^ (2 : ℝ) = (4 : ℝ) := by norm_num
        nlinarith
      have h10a : (5 : ℝ) ^ x < (25 : ℝ) := by
        have h10a1 : x < (2 : ℝ) := by linarith
        have h10a2 : (5 : ℝ) ^ x < (5 : ℝ) ^ (2 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h10a3 : (5 : ℝ) ^ (2 : ℝ) = (25 : ℝ) := by norm_num
        nlinarith
      have h7a : (10 : ℝ) ^ x = (2 : ℝ) ^ x * (5 : ℝ) ^ x := by
        rw [show (10 : ℝ) ^ x = (2 * (5 : ℝ)) ^ x by ring]
        rw [show (2 * (5 : ℝ)) ^ x = (2 : ℝ) ^ x * (5 : ℝ) ^ x by
            rw [← Real.mul_rpow]
            all_goals linarith
        ]
      have h11a : (25 * (2 : ℝ) ^ x - (10 : ℝ) ^ x + (5 : ℝ) ^ x) > (25 : ℝ) := by
        rw [h7a]
        have h8a1 : 0 < (2 : ℝ) ^ x := by positivity
        have h8a2 : 0 < (5 : ℝ) ^ x := by positivity
        have h11a : (25 * (2 : ℝ) ^ x - (2 : ℝ) ^ x * (5 : ℝ) ^ x + (5 : ℝ) ^ x) > (25 : ℝ) := by
          nlinarith [ 
            sq_pos_of_pos (show 0 < (2 : ℝ) ^ x - 1 by nlinarith), 
            sq_pos_of_pos (show 0 < (5 : ℝ) ^ x - 1 by nlinarith), 
            sq_nonneg ((2 : ℝ) ^ x - 2), 
            sq_nonneg ((5 : ℝ) ^ x - 5), 
            mul_pos (show 0 < (2 : ℝ) ^ x by positivity) (show 0 < (5 : ℝ) ^ x by positivity), 
            mul_pos (show 0 < (2 : ℝ) ^ x - 1 by nlinarith) (show 0 < (5 : ℝ) ^ x - 1 by nlinarith), 
            h9a, h10a
          ]
        linarith
      linarith
    linarith