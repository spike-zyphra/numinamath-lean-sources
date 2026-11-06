import Mathlib

theorem number_theory_253009 (n : ℕ) : 30 ∣ n^19 - n^7 := by
  have h1 : (n ^ 19) % 2 = (n ^ 7) % 2 := by
    have h1 : n % 2 = 0 ∨ n % 2 = 1 := by
      omega
    cases h1 with
    | inl h2 =>
      simp [Nat.pow_mod, h2]
    | inr h2 =>
      simp [Nat.pow_mod, h2]

  have h2 : (n ^ 19) % 3 = (n ^ 7) % 3 := by
    have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    cases h3 with
    | inl h3 =>
      simp [Nat.pow_mod, h3]
    | inr h3 =>
      cases h3 with
      | inl h3 =>
        simp [Nat.pow_mod, h3]
      | inr h3 =>
        simp [Nat.pow_mod, h3]

  have h3 : (n ^ 19) % 5 = (n ^ 7) % 5 := by
    have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    cases h4 with
    | inl h4 =>
      simp [Nat.pow_mod, h4]
    | inr h4 =>
      cases h4 with
      | inl h4 =>
        simp [Nat.pow_mod, h4]
      | inr h4 =>
        cases h4 with
        | inl h4 =>
          simp [Nat.pow_mod, h4]
        | inr h4 =>
          cases h4 with
          | inl h4 =>
            simp [Nat.pow_mod, h4]
          | inr h4 =>
            simp [Nat.pow_mod, h4]

  have h4 : 2 ∣ n ^ 19 - n ^ 7 := by
    omega

  have h5 : 3 ∣ n ^ 19 - n ^ 7 := by
    omega

  have h6 : 5 ∣ n ^ 19 - n ^ 7 := by
    omega

  have h7 : 30 ∣ n ^ 19 - n ^ 7 := by
    omega

  exact h7