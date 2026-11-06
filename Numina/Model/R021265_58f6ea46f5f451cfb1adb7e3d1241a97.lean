import Mathlib

open Real

theorem algebra_119383 {a : ℕ → ℝ} (ha : ∀ n, a n = (2 * n - 17) / (2 * n - 19)) :
    IsGreatest {x | ∃ n, x = a n ∧ n ≥ 1} (a 10) := by
  constructor
  · -- Show a 10 is in the set
    use 10
    all_goals norm_num [ha]
  · -- Show a 10 is greatest in the set
    intro x hx
    rcases hx with ⟨n, hn1, hn2⟩
    have h1 : a 10 = 3  := by
      rw [ha 10]
      norm_num
    have h2 : a n = (2 * (n : ℝ) - 17) / (2 * (n : ℝ) - 19) := by
      rw [ha n]
    rw [hn1, h1, h2]
    by_cases h4 : (2 * (n : ℝ) - 19) > 0
    · -- Case where 2n - 19 > 0, so n > 9.5
      have h5' : n ≥ 10 := by
        by_contra h
        push_neg at h
        have h8 : n ≤ 9 := by omega
        have h9 : (n : ℝ) ≤ (9 : ℝ) := by exact_mod_cast h8
        nlinarith
      have h5'' : (n : ℝ) ≥ (10 : ℝ) := by exact_mod_cast h5'
      have h3 : (2 * (n : ℝ) - 17) / (2 * (n : ℝ) - 19) ≤ (3 : ℝ) := by
        apply (div_le_iff₀ h4).mpr
        have h4' : (n : ℝ) ≥ (10 : ℝ) := by exact_mod_cast h5'
        nlinarith
      linarith
    · -- Case where 2n - 19 ≤ 0
      have h4' : (2 * (n : ℝ) - 19) ≤ 0 := by linarith
      by_cases h6 : (2 * (n : ℝ) - 19) < 0
      · -- Case where 2n - 19 < 0
        have h7' : n ≤ 9 := by
          by_contra h
          push_neg at h
          have h8 : n ≥ 10 := by omega
          have h9 : (n : ℝ) ≥ (10 : ℝ) := by exact_mod_cast h8
          nlinarith
        have h8 : (2 * (n : ℝ) - 17) / (2 * (n : ℝ) - 19) ≤ (3 : ℝ) := by
          apply (div_le_iff_of_neg' (by linarith)).mpr
          have h9 : (n : ℝ) ≤ (9 : ℝ) := by exact_mod_cast h7'
          nlinarith
        linarith
      · -- Case where 2n - 19 = 0
        have h8 : (2 * (n : ℝ) - 19) = 0 := by linarith
        have h14 : (2 * (n : ℝ) ) = (19 : ℝ) := by
          linarith
        have h15 : 2 * (n : ℤ) = 19 := by
          have h16 : (2 * (n : ℝ)) = (19 : ℝ) := h14
          exact_mod_cast h16
        omega