import Mathlib

theorem algebra_19303 {n : ℕ} (hn : n = ∑ i ∈ Finset.range 80, (i + 1)) :
    IsGreatest {p | p.Prime ∧ p ∣ n} 5 := by
  have h1 : n = 3240 := by
    rw [hn]
    native_decide
  rw [h1]
  constructor
  · -- Show that 5 is in the set
    constructor
    · -- Show that 5 is prime
      norm_num
    · -- Show that 5 divides 3240
      norm_num
  · -- Show that there is no element in the set greater than 5
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    have h2 : p ∣ 3240 := h_div
    have h3 : p ≤ 3240 := by
      exact Nat.le_of_dvd (show 0 < 3240 by norm_num) h2
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at h_prime h2 ⊢ <;> contradiction