import Mathlib

theorem number_theory_159209 (n : ℕ) :
    (∃ p1 p2, Nat.Prime p1 ∧ Nat.Prime p2 ∧ p2^3 - 2 = p1 * n ∧ p2 = p1 + 2) ↔ n = 41 := by
  constructor
  · -- Assume the existence of p1 p2 satisfying the given conditions
    rintro ⟨p1, p2, hp1, hp2, heq, hp2_eq_p1_add_2⟩
    -- Substitute p2 = p1 + 2 in the equation
    have eq1 : p2 = p1 + 2 := hp2_eq_p1_add_2
    have eq2 : p2 ^ 3 = p1 ^ 3 + 6 * p1 ^ 2 + 12 * p1 + 8 := by
      rw [show p2 = p1 + 2 by linarith]
      ring_nf
    have eq3 : p1 ^ 3 + 6 * p1 ^ 2 + 12 * p1 + 8 - 2 = p1 * n := by
      have eq4 : p2 ^ 3 = p1 * n + 2 := by
        have heq2 : p2 ^ 3 - 2 = p1 * n := heq
        omega
      rw [eq2] at eq4
      omega
    -- Rearrange to get p1^3 + 6p1^2 + 12p1 + 6 = p1 * n
    have eq4 : p1 ^ 3 + 6 * p1 ^ 2 + 12 * p1 + 6 = p1 * n := by
      omega
    have eq5 : p1 ∣ 6 := by
      have h1 : p1 ∣ p1 ^ 3 + 6 * p1 ^ 2 + 12 * p1 + 6 := by
        have h2 : p1 ∣ p1 * n := by
          use n
          all_goals ring_nf
        have h3 : p1 * n = p1 ^ 3 + 6 * p1 ^ 2 + 12 * p1 + 6 := by
          omega
        rw [h3] at h2
        exact h2
      have h8 : p1 ∣ p1 ^ 3 + 6 * p1 ^ 2 + 12 * p1 := by
        have h5 : p1 ∣ p1 ^ 3 := by
          use p1 ^ 2
          all_goals ring
        have h6 : p1 ∣ 6 * p1 ^ 2 := by
          use 6 * p1
          all_goals ring
        have h7 : p1 ∣ 12 * p1 := by
          use 12
          all_goals ring
        exact Nat.dvd_add (Nat.dvd_add h5 h6) h7
      -- So p1 divides (p1^3 + 6p1^2 + 12p1 + 6) - (p1^3 + 6p1^2 + 12p1) = 6
      have h15 : p1 ∣ ( (p1 ^ 3 + 6 * p1 ^ 2 + 12 * p1 + 6) - (p1 ^ 3 + 6 * p1 ^ 2 + 12 * p1) ) := by
        apply Nat.dvd_sub'
        · exact h1
        · exact h8
      have h16 : ( (p1 ^ 3 + 6 * p1 ^ 2 + 12 * p1 + 6) - (p1 ^ 3 + 6 * p1 ^ 2 + 12 * p1) ) = 6 := by
        have h21 : p1 ≥ 2 := Nat.Prime.two_le hp1
        have h33 : (p1 ^ 3 + 6 * p1 ^ 2 + 12 * p1 + 6) = (p1 ^ 3 + 6 * p1 ^ 2 + 12 * p1) + 6 := by
          omega
        rw [h33]
        omega
      rw [h16] at h15
      exact h15
    have h20 : p1 = 2 ∨ p1 = 3 := by
      have h21 : p1 ≤ 6 := by
        exact Nat.le_of_dvd (by nlinarith) eq5
      interval_cases p1 <;> norm_num at hp1 eq5 <;> tauto
    rcases h20 with (h21 | h21)
    · -- Assume p1 = 2.
      have p2_eq4 : p2 = 4 := by
        nlinarith [eq1, h21]
      rw [p2_eq4] at hp2
      norm_num at hp2
    · -- Assume p1 = 3
      have h100 : p1 = 3 := by linarith [h21]
      rw [show p1 = 3 by linarith [h100]] at eq4
      have h200 : n = 41 := by
        have eq100 : (3 : ℕ) ^ 3 + 6 * (3 : ℕ) ^ 2 + 12 * (3 : ℕ) + 6 = (3 : ℕ) * n := by
          omega
        omega
      omega
  · -- Assume n = 41.
    intro hn
    rw [hn]
    use 3, 5
    all_goals
      constructor
      · -- Check 3 is prime.
        norm_num
      constructor
      · -- Check 5 is prime.
        norm_num
      constructor
      · -- Check 5^3 - 2 = 3 * 41.
        norm_num
      · -- Check 5 = 3 + 2.
        all_goals norm_num