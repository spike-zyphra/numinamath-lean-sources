import Mathlib

theorem number_theory_289172 :
    IsLeast {n | 0 < n ∧ ∃ k : ℤ, Real.sqrt (2019 - n) = k} 83 := by
  constructor
  · -- Show 83 is in the set
    constructor
    · norm_num
    · use 44
      have h1 : Real.sqrt (2019 - (83 : ℝ)) = (44 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      all_goals norm_num
  · -- Show there is no smaller element in the set
    intro n hn
    rcases hn with ⟨hn_pos, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have h2 : (2019 - (n : ℝ) ) > (1936 : ℝ) := by
      have hn1 : (n : ℝ) < (83 : ℝ) := by
        exact_mod_cast h
      nlinarith
    have h3 : (Real.sqrt (2019 - (n : ℝ) ) : ℝ) = (k : ℝ) := by
      simpa using hk
    have h4 : (k : ℝ) > (44 : ℝ) := by
      have h5 : Real.sqrt (2019 - (n : ℝ) ) > Real.sqrt (1936 : ℝ) := by
        apply Real.sqrt_lt_sqrt
        all_goals
          nlinarith
      have h6 : Real.sqrt (1936 : ℝ) = (44 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h7 : Real.sqrt (2019 - (n : ℝ) ) = (k : ℝ) := by
        linarith [h3]
      nlinarith [h5, h6, h7]
    have hk1 : k > 44 := by
      by_contra h
      push_neg at h
      have : k ≤ 44 := by omega
      have h5 : (k : ℝ) ≤ (44 : ℝ) := by
        have : k ≤ 44 := by omega
        exact_mod_cast this
      nlinarith
    have hk2 : k ≥ 45 := by
      omega
    have h5 : (k : ℝ) ≥ (45 : ℝ) := by
      have : k ≥ 45 := by omega
      exact_mod_cast this
    have h8 : (2019 - (n : ℝ) ) ≥ (2025 : ℝ) := by
      have h9 : Real.sqrt (2019 - (n : ℝ) ) = (k : ℝ) := by
        linarith [h3
        ]
      have h10 : (Real.sqrt (2019 - (n : ℝ) ) ) ^ 2 = (2019 - (n : ℝ) ) := by
        rw [Real.sq_sqrt
        ]
        have hn1 : (n : ℝ) > 0 := by
          exact_mod_cast hn_pos
        nlinarith
      have h11 : (k : ℝ) ≥ (45 : ℝ) := h5
      nlinarith [h9, h10, h11
      ]
    have h9 : (n : ℝ) ≤ (2019 - (2025 : ℝ) ) := by
      nlinarith
    have h10 : (n : ℝ) ≤ (-6 : ℝ) := by
      nlinarith
    have h11 : (n : ℝ) > (0 : ℝ) := by
      exact_mod_cast hn_pos
    nlinarith