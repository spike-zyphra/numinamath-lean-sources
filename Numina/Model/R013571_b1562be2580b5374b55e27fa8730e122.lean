import Mathlib

theorem algebra_127394 (n : ℕ) :
    ∃ m, m^2 = n^2 - 4 * n + 11 ↔ n = 5 := by 
  by_cases h : n ≤ 9
  · -- n ≤ 9
    have h1 : n ≤ 9 := by omega
    use 4
    constructor
    · -- Assume 4^2 = n^2 - 4 * n + 11
      intro h_eq
      interval_cases n <;> omega
    · -- Assume n = 5
      intro h_eq
      rw [h_eq]
      all_goals
        native_decide
  · -- n > 9
    have h1 : n > 9 := by omega
    use 0
    constructor 
    · -- Assume 0^2 = n^2 - 4 * n + 11 
      intro h_eq
      have h8 : n^2 - 4 * n + 11 = 0 := by
        omega
      have h2 : n^2 ≥ 4 * n := by
        nlinarith
      have h4 : n^2 - 4 * n + 11 > 0 := by
        omega
      omega
    · -- Assume n = 5 
      intro h7
      omega