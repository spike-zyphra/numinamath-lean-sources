import Mathlib

theorem number_theory_81089 :
    IsGreatest {x | ∀ n : ℕ, n ∈ Finset.Icc 10 99 → x ∣ (n - (Nat.digits 10 n).headI - (Nat.digits 10 n).tail.headI)} 9 := by
  constructor
  · -- Show that 9 is in the set
    show ∀ n : ℕ, n ∈ Finset.Icc 10 99 → 9 ∣ (n - (Nat.digits 10 n).headI - (Nat.digits 10 n).tail.headI)
    intro n hn
    rw [Finset.mem_Icc] at hn
    rcases hn with ⟨hn10, hn99⟩
    interval_cases n <;> norm_num
  · -- Show that 9 is greatest in the set
    intro x hx
    have h1 : x ∣ (10 - (Nat.digits 10 10).headI - (Nat.digits 10 10).tail.headI) := by
      apply hx
      norm_num
    norm_num at h1 
    have h2 : x ∣ 9 := h1 
    have h3 : x ≤ 9 := by 
      exact Nat.le_of_dvd (by norm_num) h2 
    linarith