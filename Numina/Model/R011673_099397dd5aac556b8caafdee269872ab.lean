import Mathlib

set_option maxHeartbeats 500000

theorem number_theory_323294: {n: ℕ | ∃ a b c d e f, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧
1 ≤ e ∧ e ≤ 9 ∧ f ≤ 9 ∧ n = 10 ^ 5 * a + 10 ^ 4 * b + 10 ^ 3 * c + 10 ^ 2 * d + 10 * e + f ∧
    3 * n = 10 ^ 5 * e + 10 ^ 4 * f + 10 ^ 3 * a + 10 ^ 2 * b + 10 * c + d} = {153846, 230769, 307692} := by
  ext n 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume n in the left side, prove it must be in the right
    rintro ⟨a, b, c, d, e, f, ha1, ha2, hb1, hc1, hd1, he1, he2, hf1, hn1, hn2⟩

    have eq1 : 3 * (10 ^ 5 * a + 10 ^ 4 * b + 10 ^ 3 * c + 10 ^ 2 * d + 10 * e + f) = 10 ^ 5 * e + 10 ^ 4 * f + 10 ^ 3 * a + 10 ^ 2 * b + 10 * c + d := by
      linarith [hn1, hn2]

    interval_cases a 
    <;> try { 
      omega 
    }
    <;> try { 
      interval_cases b 
      <;> try { 
        omega 
      }
      <;> try { 
        interval_cases c 
        <;> try { 
          omega 
        }
        <;> try { 
          interval_cases d 
          <;> try { 
            omega 
          } 
          <;> try { 
            interval_cases e 
            <;> try { 
              omega 
            } 
            <;> try { 
              interval_cases f 
              <;> norm_num at hn1 hn2 
              <;> omega 
            }
          }
        }
      }
    } 
  · -- Assume n in the right side, prove it must be in the left
    rintro (h | h | h)
    · -- When n = 153846
      rw [h]
      use 1, 5, 3, 8, 4, 6
      all_goals norm_num 
    · -- When n = 230769
      rw [h]
      use 2, 3, 0, 7, 6, 9
      all_goals norm_num 
    · -- When n = 307692
      rw [h]
      use 3, 0, 7, 6, 9, 2
      all_goals norm_num