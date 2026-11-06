import Mathlib

theorem algebra_21300 {A B : ℤ} (h : ∀ x, 10*x^2 - x - 24 = (A*x - 8)*(B*x + 3)) :
    A*B + B = 12 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 : A * B = 10 := by
    nlinarith
  have eq6 : 3 * A - 8 * B = -1 := by
    nlinarith [eq2, eq5]
  have h1 : A = 5 := by
    have h4 : A ∣ 10 := by
      use B
      all_goals linarith
    have h5 : A = 1 ∨ A = -1 ∨ A = 2 ∨ A = -2 ∨ A = 5 ∨ A = -5 ∨ A = 10 ∨ A = -10 := by
      have h4' : A ∣ 10 := h4
      have h5 : A ≤ 10 := by
        apply Int.le_of_dvd (by norm_num) h4'
      have h6 : A ≥ -10 := by
        have h7 : -A ∣ 10 := by
          exact Int.neg_dvd.2 h4'
        have h8 : -A ≤ 10 := by
          apply Int.le_of_dvd (by norm_num) h7
        omega
      interval_cases A <;> try { tauto }
    rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5)
    · -- Assume A = 1
      rw [h5] at eq5 eq6
      omega
    · -- Assume A = -1
      rw [h5] at eq5 eq6
      omega
    · -- Assume A = 2
      rw [h5] at eq5 eq6
      omega
    · -- Assume A = -2
      rw [h5] at eq5 eq6
      omega
    · -- Assume A = 5
      assumption
    · -- Assume A = -5
      rw [h5] at eq5 eq6
      omega
    · -- Assume A = 10
      rw [h5] at eq5 eq6
      omega
    · -- Assume A = -10
      rw [h5] at eq5 eq6
      omega
  have h2 : B = 2 := by
    nlinarith [eq5, h1]
  rw [ h1, h2 ]
  all_goals norm_num