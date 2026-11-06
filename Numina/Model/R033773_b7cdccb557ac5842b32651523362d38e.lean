import Mathlib

/-Find the largest integer less than 2012
all of whose divisors have at most two 1 's in their binary representations.-/

def countOnes (n : ℕ) : ℕ :=
  ((Nat.bits n).filter (· == true)).length

theorem number_theory_609052: IsGreatest {n: ℕ | n < 2012 ∧ ∀ d: ℕ, d ∣ n → countOnes d ≤ 2} 1536 := by
  constructor
  · -- Show 1536 is in the set (1536 < 2012 and every divisor has at most two 1's in its binary representation)
    constructor
    · norm_num
    · 
      intro d h
      have h1 : d ∣ 1536 := h
      have h2 : d ≤ 1536 := Nat.le_of_dvd (by norm_num) h1
      have h3 : d ≤ 1536 := h2
      have : countOnes d ≤ 2 := by
        interval_cases d <;> norm_num [countOnes]
        <;> try { 
          trivial
        }
        <;> try { 
          native_decide
        }
      assumption
  · -- Show there is no larger element in the set
    intro n ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    have h2 := hn2 n (by exact dvd_refl n)
    have h3 : n ≥ 1537 := by 
      omega
    have h4 : n < 2012 := hn1
    have h5 : countOnes n > 2 := by
      interval_cases n <;> native_decide
    linarith
    all_goals try tauto
    all_goals try omega
    all_goals try tauto
    all_goals try omega
    <;> try { 
      native_decide
    }