import Mathlib

theorem algebra_20935 : IsGreatest {p | p.Prime ∧ p ∣ 9951} 107 := by
  constructor
  · -- Show 107 is in the set
    constructor
    · -- Show 107 is prime
      norm_num
    · -- Show 107 divides 9951
      norm_num
  · -- Show that for any p in the set, p ≤ 107
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    by_contra h
    push_neg at h
    have h2 : p ∣ 9951 := h_div
    have h3 : p ∣ 3 ∨ p ∣ 31 ∨ p ∣ 107 := by
      have h4 : p ∣ 3 * 31 * 107 := by
        norm_num at h2 ⊢
        all_goals tauto
      have h5 : p ∣ 3 ∨ p ∣ (31 * 107) := (Nat.Prime.dvd_mul h_prime).mp h4
      cases h5 with
      | inl h6 =>
        tauto
      | inr h7 =>
        have h8 : p ∣ 31 ∨ p ∣ 107 := by
          apply (Nat.Prime.dvd_mul h_prime).mp at h7
          tauto
        tauto
    cases h3 with
    | inl h31 =>
      have h4 : p ≤ 3 := by
        exact Nat.le_of_dvd (by linarith) h31
      linarith
    | inr h32 =>
      cases h32 with
      | inl h31 =>
        have h4 : p ≤ 31 := by
          exact Nat.le_of_dvd (by linarith) h31
        linarith
      | inr h31 =>
        have h4 : p ≤ 107 := by
          exact Nat.le_of_dvd (by linarith) h31
        linarith