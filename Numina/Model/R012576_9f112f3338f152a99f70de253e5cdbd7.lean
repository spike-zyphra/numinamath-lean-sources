import Mathlib

def isAwesomePrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∀ q > 0, q < p → Nat.Prime (p + 2 * q)

theorem number_theory_5894 :
    IsGreatest {p | isAwesomePrime p} 3 ∧ isAwesomePrime 3 := by
  constructor
  · -- Show that 3 is greatest in the set
    constructor
    · -- Show that 3 is in the set
      refine' ⟨by norm_num, by
        intro q hq1 hq2
        interval_cases q <;> norm_num
      ⟩
    · -- Show that each element of the set is less than or equal to 3
      intro p hp
      rcases hp with ⟨h1, h⟩
      by_contra h2
      push_neg at h2
      have h3 := h 1 (by omega) (by omega)
      have h4 := h 2 (by omega) (by omega)
      have h5 : p % 3 = 1 ∨ p % 3 = 2 := by 
        by_contra h6
        push_neg at h6
        have h7 : p % 3 = 0 := by
          omega
        have h8 : 3 ∣ p := by
          omega
        have h9 : ¬Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        tauto
      rcases h5 with (h5 | h5)
      · -- p % 3 = 1
        have h9 : (p + 2 * 1) % 3 = 0 := by
          omega
        have h10 : ¬Nat.Prime (p + 2 * 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 2 * 1) by omega)
          all_goals omega
        tauto
      · -- p % 3 = 2
        have h9 : (p + 2 * 2) % 3 = 0 := by
          omega
        have h10 : ¬Nat.Prime (p + 2 * 2) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 2 * 2) by omega)
          all_goals omega
        tauto
  · -- Show that 3 is an element of the set
    refine' ⟨by norm_num, by 
      intro q hq1 hq2
      have h1 : q = 1 ∨ q = 2 := by 
        omega
      rcases h1 with (rfl | rfl) 
      · norm_num
      · norm_num
    ⟩