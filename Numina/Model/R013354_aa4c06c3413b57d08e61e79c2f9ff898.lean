import Mathlib

theorem number_theory_157615 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : (p * q + 1).Prime) :
    (2 * p + q) * (p + 2 * q) % 4 = 0 := by
  have h1 : p ≥ 2 := Nat.Prime.two_le hp
  have h2 : q ≥ 2 := Nat.Prime.two_le hq
  have h3 : p * q + 1 ≥ 2 := Nat.Prime.two_le h
  
  by_cases hp2 : p % 2 = 0
  · -- If p is even and prime, then p must be 2
    have h1' : p = 2 := by 
      have hp2' : p % 2 = 0 := hp2
      have h4 : p ≥ 2 := Nat.Prime.two_le hp
      have : p ≤ 2 := by
        by_contra h5
        push_neg at h5
        have h5' : p % 2 = 0 := by omega
        have : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals omega
        contradiction
      interval_cases p <;> trivial
    rw [show p = 2 by omega]
    by_cases hq2 : q % 2 = 0
    · -- If q is even and prime, then q must be 2
      have hq2' : q = 2 := by
        have hq2 : q % 2 = 0 := by omega
        have h6 : q ≥ 2 := Nat.Prime.two_le hq
        have : q ≤ 2 := by
          by_contra h7
          push_neg at h7
          have h7' : q % 2 = 0 := by omega
          have : ¬q.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
            all_goals omega
          contradiction
        interval_cases q <;> trivial
      rw [show q = 2 by omega]
      all_goals norm_num
    · -- q is odd
      have hq1 : q % 2 = 1 := by
        omega
      have : q % 4 = 1 ∨ q % 4 = 3 := by 
        omega
      rcases this with (h2 | h2)
      · -- q % 4 = 1
        simp [Nat.mul_add, Nat.mul_assoc, h1', h2, Nat.mul_mod, Nat.add_mod]
        <;> omega
      · -- q % 4 = 3
        simp [Nat.mul_add, Nat.mul_assoc, h1', h2, Nat.mul_mod, Nat.add_mod]
        <;> omega
  · -- p is odd, so p % 2 = 1
    have hp1 : p % 2 = 1 := by
      omega
    by_cases hq2 : q % 2 = 0
    · -- q is even, so q must be 2
      have hq2' : q = 2 := by
        have hq2 : q % 2 = 0 := by omega
        have h6 : q ≥ 2 := Nat.Prime.two_le hq
        have : q ≤ 2 := by
          by_contra h7
          push_neg at h7
          have h7' : q % 2 = 0 := by omega
          have : ¬q.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
            all_goals omega
          contradiction
        interval_cases q <;> trivial
      rw [show q = 2 by omega]
      have : p % 4 = 1 ∨ p % 4 = 3 := by
        omega
      rcases this with (h2 | h2)
      · -- p % 4 = 1
        simp [Nat.mul_add, Nat.mul_assoc, h2, Nat.mul_mod, Nat.add_mod]
        <;> omega
      · -- p % 4 = 3
        simp [Nat.mul_add, Nat.mul_assoc, h2, Nat.mul_mod, Nat.add_mod]
        <;> omega
      all_goals try norm_num
    · -- q is odd
      have hq1 : q % 2 = 1 := by
        omega
      have h1 : (p * q + 1) % 2 = 0 := by
        have hp1 : p % 2 = 1 := by assumption
        have hq1 : q % 2 = 1 := by assumption
        simp [Nat.mul_mod, Nat.add_mod, hp1, hq1]
        <;> omega
      have h2 : ¬ (p * q + 1).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (p * q + 1) by omega)
        all_goals
          nlinarith
      contradiction
      all_goals try contradiction