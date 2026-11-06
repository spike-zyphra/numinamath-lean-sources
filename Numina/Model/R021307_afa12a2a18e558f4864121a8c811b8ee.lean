import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_191413 (x : ℝ) :
  3 * cos (2 * (π / 4 - x / 3)) + 2 * cos (π / 4 - x / 3) - 5 ≥ 0 ↔
  ∃ k : ℤ, cos (π / 4 - x / 3) = 1 ∨ π / 4 - x / 3 = 2 * π * k := by
  have h1 : cos (2 * (π / 4 - x / 3)) = 2 * cos (π / 4 - x / 3) ^ 2 - 1 := by
    rw [cos_two_mul]
  rw [h1]
  constructor
  · -- Forward direction: if the inequality holds, then either cos(π/4 - x/3) = 1 or π/4 - x/3 = 2πk for some integer k
    intro h
    have h2 : 6 * (cos (π / 4 - x / 3) - 1) * (cos (π / 4 - x / 3) + 4 / 3) ≥ 0 := by
      nlinarith [sq_nonneg (cos (π / 4 - x / 3) - 1), Real.cos_le_one (π / 4 - x / 3), Real.neg_one_le_cos (π / 4 - x / 3)]
    
    have h3 : cos (π / 4 - x / 3) = 1 := by
      nlinarith [Real.cos_le_one (π / 4 - x / 3), Real.neg_one_le_cos (π / 4 - x / 3)]
    
    have h4 : ∃ k : ℤ, π / 4 - x / 3 = 2 * π * k := by 
      have h5 : cos (π / 4 - x / 3) = 1 := h3
      have h6 : ∃ k : ℤ, π / 4 - x / 3 = 2 * π * k := by
        rw [Real.cos_eq_one_iff] at h5
        rcases h5 with ⟨k, hk⟩
        use k
        all_goals linarith
      exact h6

    rcases h4 with ⟨k, hk⟩
    refine ⟨k, Or.inr hk⟩
  · -- Backward direction: if ∃ k, cos (π/4 - x/3) =1 ∨ π/4 -x/3 =2πk then the inequality holds
    intro h
    rcases h with ⟨k, hk⟩
    rcases hk with (h1' | h2)
    · -- Case cos (π / 4 - x / 3) = 1 
      have h1 : cos (π / 4 - x / 3) = 1 := h1'
      nlinarith [Real.cos_le_one (π / 4 - x / 3), Real.neg_one_le_cos (π / 4 - x / 3), h1, sq_nonneg (cos (π / 4 - x / 3) - 1)]
    · -- Case π / 4 - x / 3 = 2 * π * k 
      -- First, we need to establish cos(π / 4 - x / 3) = 1 from h2: π / 4 - x / 3 = 2 * π * k
      have hk2 : cos (π / 4 - x / 3) = 1 := by
        have hk1 : π / 4 - x / 3 = 2 * π * (k : ℝ) := by
          linarith [h2]
        rw [hk1]
        have h8 : cos (2 * π * (k : ℝ)) = 1 := by 
          have h9 : cos (2 * π * (k : ℝ)) = 1 := by 
            have h10 : cos (2 * π * (k : ℝ)) = cos ((↑k : ℝ) * (2 * π)) := by 
              ring_nf
            rw [h10]
            have h11 : cos ((↑k : ℝ) * (2 * π)) = 1 := by 
              have h12 : cos ((↑k : ℝ) * (2 * π)) = 1 := by 
                have h30 : cos ((↑k : ℝ) * (2 * π)) = 1 := by 
                  have h34 : cos ((↑k : ℝ) * (2 * π)) = 1 := by 
                    rw [show (↑k : ℝ) * (2 * π) = (↑k : ℤ) * (2 * π) by simp]
                    rw [Real.cos_int_mul_two_pi]
                  linarith
                linarith
              linarith
            linarith
          linarith
        linarith
      -- Now we have cos(π / 4 - x / 3) = 1, so the inequality is true.
      nlinarith [Real.cos_le_one (π / 4 - x / 3), Real.neg_one_le_cos (π / 4 - x / 3), hk2, sq_nonneg (cos (π / 4 - x / 3) - 1)]