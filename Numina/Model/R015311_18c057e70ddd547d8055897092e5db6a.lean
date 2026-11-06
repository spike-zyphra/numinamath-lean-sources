import Mathlib.Tactic

theorem number_theory_123081 :
    ¬∃ m n : ℤ, 0 < m ∧ 0 < n ∧ 4 * m * (m + 1) = n * (n + 1) := by 
  rintro ⟨m, n, hm, hn, heq⟩
  have eq1 : (4 * m + 2 : ℤ) ^ 2 - (2 * n + 1 : ℤ) ^ 2 = 3 := by
    nlinarith 
  -- Factor difference of squares
  have eq2 : (4 * m - 2 * n + 1 : ℤ) * (4 * m + 2 * n + 3 : ℤ) = 3 := by 
    ring_nf at eq1 ⊢
    nlinarith 
  -- All integer factors of 3 must be in {1, 3, -1, -3}
  have h3 : (4 * m - 2 * n + 1 : ℤ) = 1 ∨ (4 * m - 2 * n + 1 : ℤ) = 3 ∨ (4 * m - 2 * n + 1 : ℤ) = -1 ∨ (4 * m - 2 * n + 1 : ℤ) = -3 := by 
    have h2 : (4 * m - 2 * n + 1 : ℤ) ∣ 3 := by
      use (4 * m + 2 * n + 3 : ℤ)
      all_goals linarith [eq2]
    have h2' : (4 * m - 2 * n + 1 : ℤ) ≤ 3 := by 
      apply Int.le_of_dvd (by norm_num) h2
    have h2'' : (4 * m - 2 * n + 1 : ℤ) ≥ -3 := by 
      have h2_neg : -(4 * m - 2 * n + 1 : ℤ) ∣ 3 := by 
        exact Int.neg_dvd.2 h2
      have h2_neg_le : -(4 * m - 2 * n + 1 : ℤ) ≤ 3 := by 
        apply Int.le_of_dvd (by norm_num) h2_neg
      omega 
    interval_cases (4 * m - 2 * n + 1 : ℤ) <;> tauto 
  rcases h3 with (h | h | h | h)
  · -- Case 1: 4 * m - 2 * n + 1 = 1
    have h4 : (4 * m + 2 * n + 3 : ℤ) = 3 := by 
      nlinarith [eq2, h]
    have h6 : m = 0 := by 
      nlinarith [h4, h]
    linarith [hm, h6]
  · -- Case 2: 4 * m - 2 * n + 1 = 3
    have h7 : (4 * m + 2 * n + 3 : ℤ) = 1 := by 
      nlinarith [eq2, h]
    have h8 : m = 0 := by 
      nlinarith [h7, h]
    linarith [hm, h8]
  · -- Case 3: 4 * m - 2 * n + 1 = -1
    have h9 : (4 * m + 2 * n + 3 : ℤ) = -3 := by 
      nlinarith [eq2, h]
    nlinarith
  · -- Case 4: 4 * m - 2 * n + 1 = -3
    have h11 : (4 * m + 2 * n + 3 : ℤ) = -1 := by 
      nlinarith [eq2, h]
    nlinarith