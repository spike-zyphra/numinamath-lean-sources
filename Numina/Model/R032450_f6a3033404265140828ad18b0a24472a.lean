import Mathlib

def a : ℕ → ℕ
| 0 => 2
| n + 1 => 2 * a n + 1

theorem number_theory_25977 :
    IsLeast {x | ∃ n, x = a n ∧ ¬Nat.Prime x} 95 := by 
  constructor
  · -- Show 95 is in the set
    use 5 
    native_decide
  · -- Show there is no smaller element in the set
    intro x hx 
    rcases hx with ⟨n, hn_eq, hn_not_prime⟩
    by_contra h
    push_neg at h 
    -- Now we need to show a contradiction that x < 95 and ¬Nat.Prime x
    have h1 : x < 95 := h 
    rw [hn_eq] at h1 
    have h2 : a n < 95 := by 
      exact_mod_cast h1 
    have h3 : n < 5 := by
      by_contra h'
      push_neg at h'
      have h4 : n ≥ 5 := by omega 
      have h5 : a n ≥ a 5 := by 
        have h4' : n ≥ 5 := h4 
        have h8 : ∀ (k : ℕ), a (k + 5) ≥ a 5 := by 
          intro k 
          induction k with 
          | zero => 
            rfl 
          | succ k ih => 
            simp [a] at ih ⊢ 
            omega 
        specialize h8 (n - 5)
        have h5' : (n - 5 + 5) = n := by
          omega 
        rw [h5'] at h8 
        linarith 
      have h5' : a 5 = 95 := by 
        norm_num [a] 
      linarith [h5, h5']
    -- Now n < 5, so we can compute a n and show it's prime
    have h6 : Nat.Prime (a n) := by 
      interval_cases n <;> norm_num [a]
    -- Contradicts hn_not_prime
    have h5' : ¬Nat.Prime (a n) := by 
      have eq1 : x = a n := hn_eq 
      rw [eq1] at hn_not_prime 
      exact_mod_cast hn_not_prime 
    contradiction