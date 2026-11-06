import Mathlib

theorem number_theory_256574 {n : ℕ} (hn : 2 ≤ n) :
    ∃ a b, a = n.minFac ∧ b ∣ n ∧ n = a^2 + b^2 ↔ n = 8 ∨ n = 20 := by
        cases' (le_or_gt n 20) with h1 h1
        · -- Case 1: n ≤ 20. We can check each value in this range.
          interval_cases n <;> try {
            use 2, 2
            native_decide
          } <;> try {
            use 2, 4
            native_decide
          } <;> try {
            simp [show n.minFac = 2 by native_decide]
            all_goals
            omega
          }
        · -- Case 2: n > 20. We prove that no such n can satisfy the condition.
          use n.minFac, 0
          simp [hn]
          <;> omega