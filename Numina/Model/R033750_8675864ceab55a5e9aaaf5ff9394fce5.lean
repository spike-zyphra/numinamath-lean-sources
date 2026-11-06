import Mathlib

theorem number_theory_266522 :
    (∀ p : ℕ, Nat.Prime p → ∃ a b c : ℕ,
      a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b = c ^ 2 ∧ a + b - 2 * c = p) ∧
    (∀ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b = c ^ 2 →
      ¬Nat.Prime (a + b + 2 * c)) := by
  constructor
  · -- Let p be a prime; then there exists a triple (a, b, c) such that a > 0, b > 0, c > 0, ab = c^2 and a + b - 2c = p
    intros p hp
    use 4 * p, p, 2 * p
    constructor
    · nlinarith [Nat.Prime.two_le hp]
    constructor
    · nlinarith [Nat.Prime.two_le hp]
    constructor
    · nlinarith [Nat.Prime.two_le hp]
    constructor
    · nlinarith [Nat.Prime.two_le hp]
    · -- Show that 4p + p - 2*(2p) = p
      omega
  · -- Let a, b, c : ℕ with a > 0, b > 0, c > 0, ab = c^2. Then a + b + 2c is composite.
    intro a b c h
    rcases h with ⟨ha, hb, hc, hab⟩
    have h2 : ¬ Nat.Prime (a + b + 2 * c) := by
      by_contra h'
      have h3 : a + b + 2 * c ∣ (a + c) * (b + c) := by
        use c
        nlinarith [hab]
      have h4 : a + b + 2 * c ∣ a + c ∨ a + b + 2 * c ∣ b + c := by
        apply (Nat.Prime.dvd_mul h').mp
        exact h3
      cases h4 with
      | inl h9 =>
        have h7 : a + b + 2 * c > a + c := by nlinarith [hb, hc]
        have h10 : a + b + 2 * c ≤ a + c := by exact Nat.le_of_dvd (by omega) h9
        linarith
      | inr h9 =>
        have h8 : a + b + 2 * c > b + c := by nlinarith [ha, hc]
        have h10 : a + b + 2 * c ≤ b + c := by exact Nat.le_of_dvd (by omega) h9
        linarith
    exact h2