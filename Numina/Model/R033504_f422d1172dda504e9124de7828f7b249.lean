import Mathlib

theorem number_theory_137058 :
    IsLeast {c : ℕ | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ a ≠ b ∧ 2 * c ^ 2 = a ^ 2 + b ^ 2} 5 ∧ 
    Set.Infinite {(a, b, c) : ℕ×ℕ×ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ 2 * c ^ 2 = a ^ 2 + b ^ 2} := by
  constructor
  · constructor
    · -- Show 5 is in the set
      use 1
      use 7
      native_decide
    · -- Show 5 is the smallest
      intro c hc
      rcases hc with ⟨a, b, ha, hb, hne, h⟩
      by_contra h'
      push_neg at h'
      interval_cases c <;> 
        { 
          have h1 : a ≤ 10 := by nlinarith 
          have h2 : b ≤ 10 := by nlinarith
          interval_cases a <;> 
            { 
              interval_cases b 
              <;> norm_num at *
            }
        }
  · -- Show that the set of triples is infinite
    apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (n + 1, 7 * (n + 1), 5 * (n + 1)))
    · -- Show f is injective
      intro n m h
      simp [Prod.ext_iff] at h
      all_goals 
        omega
    · -- Show that all elements in the image of f are in the set
      intro n
      simp [Prod.ext_iff]
      all_goals nlinarith