import Mathlib

theorem algebra_300011 (m : ℝ) :
    ∃ x : ℝ, |1 - x| = m * x ↔ m < -1 ∨ m ≥ 0 := by
  by_cases h : m ≥ 0
  · -- If m ≥ 0, then x = 1/(1+m) is a solution.
    use 1 / (1 + m)
    constructor
    · -- Forward: If the equation holds, then m < -1 or m ≥ 0
      intro h_eq
      right
      linarith
    · -- Backward: If m < -1 or m ≥ 0, then the equation holds
      rintro (h' | h')
      · -- Contradiction: m cannot be < -1 and ≥0
        linarith
      · -- Trivial: if m ≥ 0, then the solution exists
        have hm1 : (1 + m) > 0 := by linarith
        have h1mx : (1 - (1 / (1 + m))) = m / (1 + m) := by
          field_simp
          <;> linarith
        rw [show |1 - (1 / (1 + m))| = (1 - (1 / (1 + m))) by
          rw [abs_of_nonneg]
          have h1 : (1 - (1 / (1 + m)) : ℝ) ≥ 0 := by
            have h11 : (1 / (1 + m) : ℝ) ≤ 1 := by
              have h2 : (1 + m) ≥ 1 := by linarith
              have h3 : (1 / (1 + m) : ℝ) ≤ (1 : ℝ) := by
                apply (div_le_iff₀ (by linarith)).mpr
                nlinarith
              linarith
            nlinarith
          linarith
        ]
        rw [show m * (1 / (1 + m)) = m / (1 + m) by
          field_simp
        ]
        rw [h1mx]
  · -- If m < 0, need to check further.
    by_cases h1 : m < -1
    · -- If m < -1, then choose x = 1/(1+m) as solution
      use 1 / (1 + m)
      constructor
      · -- Forward: If the equation holds, then m < -1 or m ≥ 0
        intro h_eq
        left
        linarith
      · -- Backward: If m < -1 or m ≥ 0, then the equation holds
        rintro (h' | h')
        · -- If m < -1, then the equation holds
          have hm1 : (1 + m) < (0 : ℝ) := by linarith
          have h1mx : (1 - (1 / (1 + m))) = m / (1 + m) := by
            field_simp [(show (1 + m) ≠ 0 by linarith)]
            <;> nlinarith
          rw [show |1 - (1 / (1 + m))| = (1 - (1 / (1 + m))) by
            rw [abs_of_pos]
            have h1 : (1 - (1 / (1 + m)) : ℝ) > 0 := by
              have h11 : (1 / (1 + m) : ℝ) < 0 := by
                have h2 : (1 + m) < 0 := by linarith
                apply div_neg_of_pos_of_neg
                · norm_num
                · nlinarith
              nlinarith
            linarith
          ]
          rw [show m * (1 / (1 + m)) = m / (1 + m) by
            field_simp [(show (1 + m) ≠ 0 by linarith)]
            <;> nlinarith
          ]
          rw [h1mx]
          all_goals nlinarith
        · -- Contradiction: m cannot be ≥0 and < -1
          linarith
    · -- If -1 ≤ m < 0, then there is no solution. Need to choose a different x.
      use (0 : ℝ)
      constructor
      · -- Forward: If the equation holds, then m < -1 or m ≥ 0
        intro h_eq
        simp at h_eq
        all_goals try { linarith }
      · -- Backward: If m < -1 or m ≥ 0, then the equation holds
        rintro (h' | h')
        · -- If m < -1, contradiction: -1 ≤ m <0
          linarith
        · -- If m ≥ 0, contradiction: -1 ≤ m <0
          linarith