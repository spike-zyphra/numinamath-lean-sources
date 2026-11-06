import Mathlib

open Finset

theorem number_theory_223300 {n : ℕ} (a : ℕ → ℕ) (h₀ : ∀ i ∈ range (n + 1), a i < 10) :
    3 ∣ ∑ i ∈ range (n + 1), a i * 10 ^ i ↔ 3 ∣ ∑ i ∈ range (n + 1), a i := by
  have h2 : (∑ i ∈ range (n + 1), a i * 10 ^ i) % 3 = (∑ i ∈ range (n + 1), a i) % 3 := by
    have h4 : ∀ (n : ℕ), (∑ i in range (n + 1), a i * 10 ^ i) % 3 = (∑ i in range (n + 1), a i) % 3 := by
      intro n 
      induction n with 
      | zero =>
        simp 
      | succ n ih =>
        have eq1 : (∑ i in range ((n + 1) + 1), a i * 10 ^ i) = 
            (∑ i in range (n + 1), a i * 10 ^ i) + (a (n + 1) * 10 ^ (n + 1) : ℕ) := by
          rw [show (n + 1 + 1 = (n + 1) + 1) by omega]
          rw [Finset.sum_range_succ]
          all_goals simp [add_assoc]
          all_goals try { tauto }
          all_goals try { trivial }
        have eq2 : (∑ i in range ((n + 1) + 1), a i) = 
            (∑ i in range (n + 1), a i) + (a (n + 1) : ℕ) := by
          rw [show (n + 1 + 1 = (n + 1) + 1) by omega]
          rw [Finset.sum_range_succ]
          all_goals simp [add_assoc]
          all_goals try { tauto }
          all_goals try { trivial }
        rw [eq1, eq2]
        have h91 : (a (n + 1) * 10 ^ (n + 1) : ℕ) % 3 = (a (n + 1) : ℕ) % 3 := by
          have h51 : (10 ^ (n + 1) : ℕ) % 3 = 1 := by
            have h6 : ∀ (j : ℕ), (10 ^ j : ℕ) % 3 = 1 := by
              intro j
              induction j with 
              | zero => 
                simp 
              | succ j ih => 
                simp [pow_succ, Nat.mul_mod, ih]
                all_goals try { omega }
                all_goals try { tauto } <;> try { trivial }
            exact h6 (n + 1)
          simp [Nat.mul_mod, h51]
          all_goals try { omega }
          all_goals try { tauto }
        simp [Nat.add_mod, ih, h91]
        all_goals try { omega }
        all_goals try { try { tauto } } <;> try { try { tauto } }
    exact h4 n 
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  rw [h2]
  all_goals try { try { tauto } } <;> try { try { tauto  } }
  all_goals try { try { omega } } <;> try { try { tauto } }
  all_goals try { try { trivial  } }