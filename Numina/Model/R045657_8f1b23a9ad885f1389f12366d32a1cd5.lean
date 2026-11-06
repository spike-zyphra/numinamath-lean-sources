import Mathlib

theorem algebra_142574 (m n : ℤ) :
    (m ^ 2 + n) * (m + n ^ 2) = (m + n) ^ 3 ↔
    (m = 0 ∧ n = 0) ∨ (m = 0 ∧ n ≠ 0) ∨ (m ≠ 0 ∧ n = 0) ∨
    (m = -5 ∧ n = 2) ∨ (m = -1 ∧ n = 1) ∨ (m = 1 ∧ n = -1) ∨
    (m = 2 ∧ n = -5) ∨ (m = 4 ∧ n = 11) ∨ (m = 5 ∧ n = 7) ∨
    (m = 7 ∧ n = 5) ∨ (m = 11 ∧ n = 4) := by
  constructor
  · -- Assume the equation holds, prove the solutions
    rintro h
    have h_eq : m * n * (m * n + 1 - 3 * m - 3 * n) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h_eq) with h_eq1 h_eq2
    cases' (mul_eq_zero.mp h_eq1) with h_eq3 h_eq4
    · -- Case m = 0.
      have hm0 : m = 0 := by
        nlinarith
      by_cases hn0 : n = 0
      · -- Case m = 0, n = 0
        left
        exact ⟨hm0, hn0⟩
      · -- Case m = 0, n ≠ 0
        right
        left
        exact ⟨hm0, hn0⟩
    · -- Case n = 0.
      have hn0 : n = 0 := by
        nlinarith
      by_cases hm0 : m = 0
      · -- Case m = 0, n = 0
        left
        exact ⟨hm0, hn0⟩
      · -- Case m ≠ 0, n = 0
        right
        right
        left
        exact ⟨hm0, hn0⟩
    · -- Case m * n + 1 - 3 * m - 3 * n = 0.
      have h_eq5 : m * n + 1 - 3 * m - 3 * n = 0 := by
        nlinarith
      have h_eq6 : (m - 3) * (n - 3) = 8 := by
        nlinarith
      have h_eq7 : m - 3 ∣ 8 := by
        use (n - 3)
        all_goals
          nlinarith
      have h_eq8 : m - 3 ≤ 8 := by
        exact Int.le_of_dvd (show 0 < 8 by norm_num) h_eq7
      have h_eq10 : m - 3 ≥ -8 := by 
        have h_eq10 : -(m - 3) ∣ 8 := by
          exact Int.neg_dvd.2 h_eq7
        have h_eq11 : -(m - 3) ≤ 8 := by 
          exact Int.le_of_dvd (show 0 < 8 by norm_num) h_eq10
        omega
      interval_cases h : m - 3 <;> omega
  · -- Assume the solutions, prove the equation.
    rintro (h | h | h | h | h | h | h | h | h | h | h)
    · -- Case m = 0, n = 0
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case m = 0, n ≠ 0
      rcases h with ⟨rfl, hn⟩
      ring
    · -- Case m ≠ 0, n = 0
      rcases h with ⟨hm, rfl⟩
      ring
    · -- Case m = -5, n = 2
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case m = -1, n = 1
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case m = 1, n = -1
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case m = 2, n = -5
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case m = 4, n = 11
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case m = 5, n = 7
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case m = 7, n = 5
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case m = 11, n = 4
      rcases h with ⟨rfl, rfl⟩
      norm_num