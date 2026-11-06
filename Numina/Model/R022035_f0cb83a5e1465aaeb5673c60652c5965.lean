import Mathlib

theorem number_theory_177465
    (p1 p2 : ℕ)
    (hp1 : p1.Prime)
    (hp2 : p2.Prime)
    (h : 3 < p1 ∧ p1 < p2) :
    ∃ a b, a + b = p2 ∧ a - b = p1 ∧ 6 ∣ a * b := by

  have h1 : 3 < p1 := h.1
  have h2 : p1 < p2 := h.2
  have h3 : p1 > 3 := by linarith
  have h4 : p2 > 3 := by linarith

  have h5 : p1 % 2 = 1 := by
    by_contra h6
    push_neg at h6
    have h8 : p1 % 2 = 0 := by omega
    have h9 : ¬p1.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p1 by omega)
      all_goals linarith
    tauto

  have h10 : p2 % 2 = 1 := by
    by_contra h11
    push_neg at h11
    have h12 : p2 % 2 = 0 := by omega
    have h13 : ¬p2.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p2 by omega)
      all_goals linarith
    tauto

  have h14 : (p1 + p2) % 2 = 0 := by
    omega

  have h15 : (p2 - p1) % 2 = 0 := by
    have h18 : p2 % 2 = 1 := h10
    have h19 : p1 % 2 = 1 := h5
    omega

  use (p1 + p2) / 2, (p2 - p1) / 2

  constructor
  · -- Show that a + b = p2
    omega

  constructor
  · -- Show that a - b = p1
    omega

  · -- Show that 6 divides a * b
    -- We need to show divisible by 2 and divisible by 3.
    -- First show divisible by 2.
    -- Show divisible by 3.
    -- Therefore divisible by 6.
    have h100 : ((p1 + p2) / 2 : ℕ) * ((p2 - p1) / 2 : ℕ) % 2 = 0 := by
      have h111 : p1 % 2 = 1 := h5
      have h112 : p2 % 2 = 1 := h10
      have h113 : (p1 + p2) % 4 = 0 ∨ (p1 + p2) % 4 = 2 := by
        omega
      rcases h113 with (h113 | h113)
      · -- If (p1 + p2) % 4 = 0, then (p1 + p2) / 2 is even
        have h114 : ((p1 + p2) / 2) % 2 = 0 := by
          omega
        simp [Nat.mul_mod, h114]
      · -- If (p1 + p2) % 4 = 2, then (p2 - p1) % 4 = 0
        have h116 : (p2 - p1) % 4 = 0 := by
          omega
        have h117 : ((p2 - p1) / 2) % 2 = 0 := by
          omega
        simp [Nat.mul_mod, h117]

    have h101 : ((p1 + p2) / 2 : ℕ) * ((p2 - p1) / 2 : ℕ) % 3 = 0 := by
      have h110 : p1 % 3 = 1 ∨ p1 % 3 = 2 := by
        by_contra h111
        push_neg at h111
        have h112 : p1 % 3 = 0 := by omega
        have h113 : 3 ∣ p1 := by
          omega
        have h114 : p1 ≠ 3 := by linarith
        have h115 : ¬p1.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p1 by omega)
          all_goals linarith
        tauto

      have h120 : p2 % 3 = 1 ∨ p2 % 3 = 2 := by
        by_contra h121
        push_neg at h121
        have h122 : p2 % 3 = 0 := by omega
        have h123 : 3 ∣ p2 := by
          omega
        have h124 : p2 ≠ 3 := by linarith
        have h125 : ¬p2.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p2 by omega)
          all_goals linarith
        tauto

      rcases h110 with (h110 | h110)
      · -- case p1 % 3 = 1
        rcases h120 with (h120 | h120)
        · -- case p2 % 3 = 1
          have h130 : (p2 - p1) % 3 = 0 := by
            omega
          have h131 : ((p2 - p1) / 2) % 3 = 0 := by
            omega
          simp [Nat.mul_mod, h131]
        · -- case p2 % 3 = 2
          have h130 : (p1 + p2) % 3 = 0 := by
            omega
          have h131 : ((p1 + p2) / 2) % 3 = 0 := by
            omega
          simp [Nat.mul_mod, h131]
      · -- case p1 % 3 = 2
        rcases h120 with (h120 | h120)
        · -- case p2 % 3 = 1
          have h130 : (p1 + p2) % 3 = 0 := by
            omega
          have h131 : ((p1 + p2) / 2) % 3 = 0 := by
            omega
          simp [Nat.mul_mod, h131]
        · -- case p2 % 3 = 2
          have h130 : (p2 - p1) % 3 = 0 := by
            omega
          have h131 : ((p2 - p1) / 2) % 3 = 0 := by
            omega
          simp [Nat.mul_mod, h131]

    omega