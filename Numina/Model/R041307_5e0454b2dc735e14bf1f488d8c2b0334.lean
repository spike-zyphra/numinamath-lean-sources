import Mathlib

theorem number_theory_160349 (p : ℕ) (hp : Nat.Prime p) (p1 p2 : ℕ)
    (hp1 : p1 = 2 * p - 1) (hp2 : p2 = 2 * p + 1) :
    (p1.Prime ∧ p2.Prime) ↔ (p1 = 3 ∧ p2 = 5) ∨ (p1 = 5 ∧ p2 = 7) := by
  constructor
  · -- Forward direction: if $p_1$ and $p_2$ are both prime, then they form one of the pairs.
    intro h
    rcases h with ⟨h1, h2⟩
    rw [hp1] at h1
    rw [hp2] at h2
    by_cases h3 : p ≤ 3
    · -- p ≤ 3
      interval_cases p <;> norm_num at hp h1 h2 ⊢ <;> tauto
    · -- p > 3
      have h4 : p % 3 = 1 ∨ p % 3 = 2 := by
        by_contra h
        push_neg at h
        have h5 : p % 3 = 0 := by omega
        have h6 : p > 3 := by omega
        have h7 : ¬Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        contradiction
      rcases h4 with (h4 | h4)
      · -- Case p % 3 = 1
        -- Then 2p + 1 divisible by 3.
        have h8 : (2 * p + 1) % 3 = 0 := by
          omega
        have h9 : ¬Nat.Prime (2 * p + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2 * p + 1) by omega)
          all_goals
          omega
        contradiction
      · -- Case p % 3 = 2
        -- Then 2p - 1 divisible by 3.
        have h10 : (2 * p - 1) % 3 = 0 := by
          have h2p : p ≥ 4 := by omega
          omega
        have h11 : ¬Nat.Prime (2 * p - 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2 * p - 1) by omega)
          all_goals
          have h2p : p ≥ 4 := by omega
          omega
        contradiction
  · -- Backward direction: given the pairs, $p_1$ and $p_2$ are both prime.
    rintro (h | h)
    · -- Case (p1 = 3 ∧ p2 = 5)
      rcases h with ⟨hp1', hp2'⟩
      rw [hp1'] at *
      rw [hp2'] at *
      constructor <;> norm_num
    · -- Case (p1 = 5 ∧ p2 = 7)
      rcases h with ⟨hp1', hp2'⟩
      rw [hp1'] at *
      rw [hp2'] at *
      constructor <;> norm_num