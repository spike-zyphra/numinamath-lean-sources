import Mathlib

theorem number_theory_236643 (a b c : ℕ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : Nat.Prime (a * b * c)) (h₄ : a * b * c > 2) :
    Odd (a + b + c) := by
  have h5 : a * b * c % 2 = 1 := by
    by_contra h
    push_neg at h
    have h6 : ¬ Nat.Prime (a * b * c) := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ a * b * c by omega)
      all_goals nlinarith
      all_goals linarith
      all_goals nlinarith
    contradiction
  have h6 : a % 2 = 1 := by
    by_contra h
    push_neg at h
    have h7 : a % 2 = 0 := by omega
    by_cases hb : b % 2 = 0
    · -- If a % 2 = 0 and b % 2 = 0, then a * b * c % 2 = 0
      have h8 : (a * b * c) % 2 = 0 := by
        simp [Nat.mul_mod, h7, hb]
        <;> all_goals
          try omega
      omega
      all_goals
        try omega
    · -- b % 2 = 1
      have hb1 : b % 2 = 1 := by omega
      by_cases hc : c % 2 = 0
      · -- a % 2 = 0, b % 2 = 1, c % 2 = 0
        have h9 : (a * b * c) % 2 = 0 := by
          simp [Nat.mul_mod, h7, hb1, hc]
          <;> all_goals
            try omega
        omega
      · -- a % 2 = 0, b % 2 = 1, c % 2 = 1
        have hc1 : c % 2 = 1 := by omega
        have h10 : (a * b * c) % 2 = 0 := by
          simp [Nat.mul_mod, h7, hb1, hc1]
          <;> all_goals
            try omega
        omega
        all_goals
          try omega
  have h7 : b % 2 = 1 := by
    by_contra h
    push_neg at h
    have h8 : b % 2 = 0 := by omega
    by_cases ha : a % 2 = 0
    · -- a % 2 = 0 and b % 2 = 0
      have h6 : a % 2 = 0 := by omega
      have h9 : (a * b * c) % 2 = 0 := by
        simp [Nat.mul_mod, h6, h8]
        <;> all_goals
          try omega
      omega
      all_goals
        try omega
    · -- a % 2 = 1
      have ha1 : a % 2 = 1 := by omega
      by_cases hc : c % 2 = 0
      · -- a % 2 = 1, b % 2 = 0, c % 2 = 0
        have h9 : (a * b * c) % 2 = 0 := by
          simp [Nat.mul_mod, ha1, h8, hc]
          <;> all_goals
            try omega
        omega
      · -- a % 2 = 1, b % 2 = 0, c % 2 = 1
        have hc1 : c % 2 = 1 := by omega
        have h10 : (a * b * c) % 2 = 0 := by
          simp [Nat.mul_mod, ha1, h8, hc1]
          <;> all_goals
            try omega
        omega
  have h8 : c % 2 = 1 := by
    by_contra h
    push_neg at h
    have h9 : c % 2 = 0 := by omega
    by_cases ha : a % 2 = 0
    · -- a % 2 = 0 and c % 2 = 0
      have h6 : a % 2 = 0 := by omega
      have h10 : (a * b * c) % 2 = 0 := by
        simp [Nat.mul_mod, h6, h9]
        <;> all_goals
          try omega
      omega
      all_goals
        try omega
    · -- a % 2 = 1
      have ha1 : a % 2 = 1 := by omega
      by_cases hb : b % 2 = 0
      · -- a % 2 = 1, b % 2 = 0, c % 2 = 0
        have h7 : b % 2 = 0 := by omega
        have h11 : (a * b * c) % 2 = 0 := by
          simp [Nat.mul_mod, ha1, h7, h9]
          <;> all_goals
            try omega
        omega
      · -- a % 2 = 1, b % 2 = 1, c % 2 = 0
        have hb1 : b % 2 = 1 := by omega
        have h12 : (a * b * c) % 2 = 0 := by
          simp [Nat.mul_mod, ha1, hb1, h9]
          <;> all_goals
            try omega
        omega
  have h9 : (a + b + c) % 2 = 1 := by
    omega
  exact Nat.odd_iff.mpr h9