import Mathlib

theorem number_theory_197142 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    p^2 - 2 * q^2 = 1 ↔ (p = 3 ∧ q = 2) := by
  constructor
  · -- Assume p^2 - 2 * q^2 = 1, prove (p = 3 ∧ q = 2)
    intro h
    have h1 : p^2 = 2 * q^2 + 1 := by 
      omega
    have h2 : p > q := by
      by_contra h3
      push_neg at h3
      have h3 : p ≤ q := by omega
      have h4 : p^2 ≤ q^2 := by nlinarith 
      have h5 : 2 * q^2 + 1 ≤ 2 * q^2 := by nlinarith [h1, h4]
      nlinarith
    by_cases h3 : q > 2
    · -- q > 2, so q is odd
      have h4 : q % 2 = 1 := by
        by_contra h5
        push_neg at h5
        have h6 : q % 2 = 0 := by omega
        have h7 : q > 2 := by omega
        have h8 : ¬q.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
          all_goals omega
        contradiction
      have h5 : p % 8 = 0 ∨ p % 8 = 1 ∨ p % 8 = 2 ∨ p % 8 = 3 ∨ p % 8 = 4 ∨ p % 8 = 5 ∨ p % 8 = 6 ∨ p % 8 = 7 := by
        omega
      have h6 : p^2 % 8 = 0 ∨ p^2 % 8 = 1 ∨ p^2 % 8 = 4 := by
        rcases h5 with (h | h | h | h | h | h | h | h) <;> norm_num [pow_two, Nat.mul_mod, h] at *
      have h7 : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by
        omega
      have h8 : q^2 % 8 = 1 := by
        rcases h7 with (h | h | h | h) <;> norm_num [pow_two, Nat.mul_mod, h] at *
      have h9 : (2 * q^2 + 1) % 8 = 3 := by
        omega
      have h10 : (p^2) % 8 = (2 * q^2 + 1) % 8 := by
        omega
      omega
    · -- q ≤ 2
      have h4 : q = 2 := by 
        interval_cases q <;> norm_num at *
        <;> tauto
      have h5 : p = 3 := by 
        rw [h4] at h1
        have h6 : p ≤ 3 := by 
          nlinarith [show p ^ 2 ≤ 9 from by nlinarith]
        interval_cases p <;> norm_num at h1 <;> tauto
      constructor <;> tauto
  · -- Backward
    rintro ⟨rfl, rfl⟩
    all_goals
      norm_num