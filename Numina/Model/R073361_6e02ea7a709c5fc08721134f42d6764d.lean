import Mathlib

theorem algebra_21521 {n : ℕ} (hn : n = Nat.factorial 5) :
    IsGreatest {x | Odd x ∧ x ∣ n} 15 := by 
  rw [hn]
  constructor
  · -- Show that 15 is in the set
    constructor
    · -- Show that 15 is odd
      exact Nat.odd_iff.mpr (by norm_num)
    · -- Show that 15 divides 5!
      native_decide
  · -- Show that 15 is greatest in the set
    intro x h
    rcases h with ⟨hx_odd, hx_div⟩
    have h1 : x ∣ 120 := by 
      rw [show Nat.factorial 5 = 120 by rfl] at hx_div
      exact hx_div
    have h4 : x ≤ 120 := by 
      exact Nat.le_of_dvd (by norm_num) h1
    by_contra h'
    push_neg at h'
    interval_cases x <;> norm_num at *
    <;> try { contradiction }
    <;> try { exfalso <;> try { contradiction } }
    <;> norm_num [Nat.odd_iff] at hx_odd <;> omega
    <;> try { native_decide }
    <;> try { contradiction }
    <;> try { exfalso <;> try { contradiction } }
    <;> norm_num [Nat.odd_iff] at hx_odd <;> try { contradiction } 
    <;> omega