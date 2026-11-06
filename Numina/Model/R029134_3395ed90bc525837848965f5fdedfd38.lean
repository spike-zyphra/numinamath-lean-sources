import Mathlib

theorem number_theory_105817 (a b : ℕ) :
    (∃ m n : ℕ, (3 * a + 8 * b + 2: ℚ) / (10 * a + 2 * b + 1) = m ∧
    (8 * a + b + 3: ℚ) / (2 * a + 7 * b + 3) = n) ↔ a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  constructor
  · -- Forward direction: if both fractions are natural numbers, then (a, b) is (0,0) or (1,1).
    rintro ⟨m, n, hm, hn⟩
    have hm_eq : (3 * a + 8 * b + 2 : ℚ) = (m : ℚ) * (10 * a + 2 * b + 1 : ℚ) := by
      field_simp [(show (10 * a + 2 * b + 1 : ℚ) ≠ 0 by positivity)] at hm ⊢
      nlinarith
    have hn_eq : (8 * a + b + 3 : ℚ) = (n : ℚ) * (2 * a + 7 * b + 3 : ℚ) := by
      field_simp [(show (2 * a + 7 * b + 3 : ℚ) ≠ 0 by positivity)] at hn ⊢
      nlinarith
    have h1 : (3 * a + 8 * b + 2) = m * (10 * a + 2 * b + 1) := by
      exact_mod_cast hm_eq
    have h2 : (8 * a + b + 3) = n * (2 * a + 7 * b + 3) := by
      exact_mod_cast hn_eq
    have h3 : m ≤ 3 := by
      nlinarith [show m * (10 * a + 2 * b + 1) = 3 * a + 8 * b + 2 from by linarith [h1], 
        show 10 * a + 2 * b + 1 > 0 by omega
      ]
    have h4 : n ≤ 8 := by
      nlinarith [show n * (2 * a + 7 * b + 3) = 8 * a + b + 3 from by linarith [h2], 
        show 2 * a + 7 * b + 3 > 0 by omega
      ]
    -- Now we can check all possible values.
    interval_cases m <;> interval_cases n <;> omega
  · -- Backward direction: if (a, b) is (0,0) or (1,1), then both fractions are natural numbers.
    rintro (h | h)
    · -- Case (0, 0)
      rcases h with ⟨rfl, rfl⟩
      use 2, 1
      all_goals norm_num
    · -- Case (1, 1)
      rcases h with ⟨rfl, rfl⟩
      use 1, 1
      all_goals norm_num