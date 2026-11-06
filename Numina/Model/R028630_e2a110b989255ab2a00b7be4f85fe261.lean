import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

theorem number_theory_838 :
  IsLeast {n : ℕ | ∃ k : ℕ, k > 0 ∧ n = k * (k + 1) * (k + 2) ∧ ∑ i in Finset.range 100, (i + 1) ∣ n} 999900 := by
  constructor
  · -- Show that 999900 is in the set
    use 99
    native_decide
  · -- Show that 999900 is the minimum
    intro n hn
    rcases hn with ⟨k, hk1, h_eq, hk2⟩
    by_contra h
    push_neg at h
    have h1 : k ≤ 98 := by
      by_contra h2
      push_neg at h2
      have h3 : k * (k + 1) * (k + 2) ≥ 999900 := by
        have h4 : k ≥ 99 := by
          omega
        have eq : k * (k + 1) * (k + 2) = k * (k + 1) * (k + 2) := rfl
        have h7 : k * (k + 1) * (k + 2) ≥ 99 * 100 * 101 := by
          have h8 : k ≥ 99 := by
            omega
          have h9 : k + 1 ≥ 100 := by
            omega
          have h10 : k + 2 ≥ 101 := by
            omega
          have h11 : k * (k + 1) * (k + 2) ≥ 99 * 100 * 101 := by
            apply Nat.mul_le_mul
            apply Nat.mul_le_mul
            all_goals
              try { omega }
          linarith
        nlinarith
      have h2 : n ≥ 999900 := by
        have eq2 : n = k * (k + 1) * (k + 2) := by linarith [h_eq]
        linarith [eq2, h3]
      linarith
    interval_cases k <;> try { 
      norm_num [h_eq] at hk2 ⊢ 
      all_goals try { 
        contradiction 
      }
    }
    all_goals try { 
      omega 
    }