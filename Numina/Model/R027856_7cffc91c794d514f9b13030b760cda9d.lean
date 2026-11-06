import Mathlib

theorem number_theory_77066 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    4 ∣ a^2 + b^2 + c^2 ↔ Even a ∧ Even b ∧ Even c := by
  constructor
  · -- Assume 4 divides a^2 + b^2 + c^2, prove even a ∧ even b ∧ even c
    intro h
    have h1 : a % 2 = 0 := by
      by_contra h1
      push_neg at h1
      have h1' : a % 4 = 1 ∨ a % 4 = 3 := by omega
      have h1sq : a ^ 2 % 4 = 1 := by
        rcases h1' with (h1' | h1')
        · -- a % 4 = 1
          simp [Nat.pow_mod, h1']
        · -- a % 4 = 3
          simp [Nat.pow_mod, h1']
      have h2sq : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
        have h2 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
        rcases h2 with (h2 | h2 | h2 | h2) <;> simp [Nat.pow_mod, h2]
      have h3sq : c ^ 2 % 4 = 0 ∨ c ^ 2 % 4 = 1 := by
        have h1 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
        rcases h1 with (h1 | h1 | h1 | h1) <;> simp [Nat.pow_mod, h1]
      omega
    have h2 : b % 2 = 0 := by
      by_contra h2
      push_neg at h2
      have h2' : b % 4 = 1 ∨ b % 4 = 3 := by omega
      have h2sq : b ^ 2 % 4 = 1 := by
        rcases h2' with (h2' | h2')
        · -- b % 4 = 1
          simp [Nat.pow_mod, h2']
        · -- b % 4 = 3
          simp [Nat.pow_mod, h2']
      have h1sq : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
        have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
        rcases h1 with (h1 | h1 | h1 | h1) <;> simp [Nat.pow_mod, h1]
      have h3sq : c ^ 2 % 4 = 0 ∨ c ^ 2 % 4 = 1 := by
        have h3 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
        rcases h3 with (h3 | h3 | h3 | h3) <;> simp [Nat.pow_mod, h3]
      omega
    have h3 : c  % 2 = 0 := by
      by_contra h3
      push_neg at h3
      have h3' : c % 4 = 1 ∨ c % 4 = 3 := by omega
      have h3sq : c ^ 2 % 4 = 1 := by
        rcases h3' with (h3' | h3')
        · -- c % 4 = 1
          simp [Nat.pow_mod, h3']
        · -- c % 4 = 3
          simp [Nat.pow_mod, h3']
      have h1sq : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
        have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
        rcases h1 with (h1 | h1 | h1 | h1) <;> simp [Nat.pow_mod, h1]
      have h2sq : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
        have h2 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
        rcases h2 with (h2 | h2 | h2 | h2) <;> simp [Nat.pow_mod, h2]
      omega
    have ha : Even a := by
      have : a % 2 = 0 := h1
      exact ⟨a / 2, by omega⟩
    have hb : Even b := by
      have : b % 2 = 0 := h2
      exact ⟨b / 2, by omega⟩
    have hc : Even c := by
      have : c % 2 = 0 := h3
      exact ⟨c / 2, by omega⟩
    exact ⟨ha, hb, hc⟩
  · -- Assume even a ∧ even b ∧ even c, prove 4 ∣ a^2 + b^2 + c^2
    rintro ⟨ha, hb, hc⟩
    rcases ha with ⟨x, hx⟩
    rcases hb with ⟨y, hy⟩
    rcases hc with ⟨z, hz⟩
    rw [show a = 2 * x by omega, show b = 2 * y by omega, show c = 2 * z by omega]
    have h1 : (2 * x : ℕ)^2 + (2 * y : ℕ)^2 + (2 * z : ℕ)^2 = 4 * (x^2 + y^2 + z^2) := by
      nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
    rw [h1]
    omega