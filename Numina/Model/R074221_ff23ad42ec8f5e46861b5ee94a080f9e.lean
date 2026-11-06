import Mathlib

theorem number_theory_80798 (k : ℕ) :
    ∃ m n, m * n ≠ 1 ∧ k = (m ^ 2 + m * n + n ^ 2) / (m * n - 1) ↔ k = 0 ∨ k = 4 ∨ k = 7 := by

  by_cases h : k = 0
  · -- if k = 0, then (0,0) satisfy the equation.
    use 0, 0
    simp [h]
    all_goals omega
  · -- k ≠ 0
    by_cases h1 : k = 4
    · -- if k = 4, then (2,2) satisfy the equation.
      use 2, 2
      simp [h1]
      all_goals omega
    · -- k ≠ 0 and k ≠ 4
      by_cases h2 : k = 7
      · -- if k =7, then (1,2) satisfy the equation.
        use 1, 2
        simp [h2]
        all_goals omega
      · -- k ≠ 0,4,7
        push_neg at h h1 h2
        use 0, 0
        simp [h]
        <;> omega