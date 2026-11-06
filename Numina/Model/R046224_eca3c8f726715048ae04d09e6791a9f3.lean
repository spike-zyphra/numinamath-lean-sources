import Mathlib

theorem number_theory_230094 (a b c : ℕ) (ha : Odd a) (hb : Odd b) :
    Odd (3^a + (b - 1)^2 * c) := by
  have h1 : (3 ^ a : ℕ) % 2 = 1 := by
    have h2 : ∀ (a : ℕ), (3 ^ a : ℕ) % 2 = 1 := by
      intro a
      induction a with
      | zero =>
        simp
      | succ a ih =>
        simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
        all_goals omega
    specialize h2 a
    exact h2
  have h3 : b % 2 = 1 := by
    rcases hb with ⟨k, hk⟩
    omega
  have h4 : (b - 1 : ℕ) % 2 = 0 := by
    omega
  have h5 : ((b - 1 : ℕ)^2 * c) % 2 = 0 := by
    have h6 : (b - 1 : ℕ) % 2 = 0 := h4
    have h7 : (b - 1 : ℕ)^2 % 2 = 0 := by
      simp [Nat.pow_mod, h6]
    have h8 : ((b - 1 : ℕ)^2 * c) % 2 = 0 := by
      simp [Nat.mul_mod, h7]
    exact h8
  have h6 : (3 ^ a + (b - 1)^2 * c) % 2 = 1 := by
    omega
  have h7 : Odd (3^a + (b - 1)^2 * c) := by
    exact ⟨(3^a + (b - 1)^2 * c) / 2, by omega⟩
  exact h7