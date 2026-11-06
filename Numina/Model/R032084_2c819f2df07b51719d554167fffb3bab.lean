import Mathlib

theorem number_theory_4567 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
  (hord : a < b ∧ b < c) (hdiff : c - b = 10 ∧ b - a = 4) : c ≤ 17 := by
  rcases hdiff with ⟨h1, h2⟩
  have h3 : c = b + 10 := by
    omega
  have h4 : b = a + 4 := by
    omega
  have h5 : c = a + 14 := by
    rw [h3, h4]
    all_goals omega
  by_contra h
  push_neg at h
  have h8 : c ≥ 18 := by
    omega
  have h9 : a ≥ 4 := by
    omega
  have h13 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
    omega
  rcases h13 with (h13 | h13 | h13)
  · -- Assume a % 3 = 0
    have h14 : a % 3 = 0 := h13
    have h15 : a > 3 := by
      omega
    -- `a` is divisible by 3 and `a > 3`, contradiction with `ha: a.Prime`.
    have h16 : ¬ (a).Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ a by omega)
      all_goals 
        omega
    contradiction
  · -- Assume a % 3 = 1
    have h14 : a % 3 = 1 := h13
    -- Then c divisible by 3
    have h17 : c % 3 = 0 := by
      omega
    -- Then c not prime.
    have h18 : c > 3 := by
      omega
    -- Contradicts with `hc: c.Prime`.
    have h19 : ¬ (c).Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ c by omega)
      all_goals
        omega
    contradiction
  · -- Assume a % 3 = 2
    have h14 : a % 3 = 2 := h13
    -- Then b divisible by 3
    have h18 : b % 3 = 0 := by
      omega
    -- Then b not prime.
    have h19 : b > 3 := by
      omega
    -- Contradicts with `hb: b.Prime`.
    have h20 : ¬ (b).Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ b by omega)
      all_goals
        omega
    contradiction