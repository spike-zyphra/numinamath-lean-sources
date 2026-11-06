import Mathlib
theorem algebra_605222 (n : ℤ) :
    (n ≥ 0 ∧ ∃ a b : ℤ, n ^ 2 = a + b ∧ n ^ 3 = a ^ 2 + b ^ 2) ↔ n = 0 ∨ n = 1 ∨ n = 2 := by
  constructor
  · -- Forward implication: given n ≥ 0 and a,b with n²=a+b and n³=a²+b², prove n=0 or 1 or 2
    intro h
    rcases h with ⟨hn, ⟨a, b, h1, h2⟩⟩
    have h3 : n ≥ 0 := hn
    have h4 : b = n ^ 2 - a := by
      linarith
    rw [h4] at h2
    have h5 : n ≤ 2 := by
      nlinarith [sq_nonneg (a - n), sq_nonneg (n ^ 2 - a - n), sq_nonneg (a - (n ^ 2 - a)), sq_nonneg (n - 2)]
    have h6 : n = 0 ∨ n = 1 ∨ n = 2 := by
      interval_cases n <;> omega
    tauto
  · -- Backward implication: given n=0 or 1 or 2, prove existence a,b with n≥0
    intro h
    rcases h with (r | r | r)
    · -- n = 0
      constructor
      · -- n ≥ 0
        omega
      · -- existence of a and b
        use 0, 0
        all_goals
          norm_num [r]
    · -- n = 1
      constructor
      · -- n ≥ 0
        omega
      · -- existence of a and b
        use 0, 1
        all_goals
          norm_num [r]
    · -- n = 2
      constructor
      · -- n ≥ 0
        omega
      · -- existence of a and b
        use 2, 2
        all_goals
          norm_num [r]