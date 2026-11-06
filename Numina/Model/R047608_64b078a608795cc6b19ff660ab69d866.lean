import Mathlib


open Nat


lemma lemma_1 (a b c : ℕ)
  (h₁ : a^2 + b^2 = c^2) : 3 ∣ a * b * c := by
  by_contra h2
  push_neg at h2
  have h3 : a % 3 = 1 ∨ a % 3 = 2 := by
    by_contra h
    push_neg at h
    have h4 : a % 3 = 0 := by
      omega
    have h5 : a * b * c % 3 = 0 := by
      simp [Nat.mul_mod, h4]
    omega
  have h4 : b % 3 = 1 ∨ b % 3 = 2 := by
    by_contra h
    push_neg at h
    have h5 : b % 3 = 0 := by
      omega
    have h6 : a * b * c % 3 = 0 := by
      simp [Nat.mul_mod, h5]
    omega
  have h5 : c % 3 = 1 ∨ c % 3 = 2 := by
    by_contra h
    push_neg at h
    have h6 : c % 3 = 0 := by
      omega
    have h7 : a * b * c % 3 = 0 := by
      simp [Nat.mul_mod, h6]
    omega
  have h6 : a ^ 2 % 3 = 1 := by
    rcases h3 with (h | h)
    ·
      simp [Nat.pow_mod, h]
    ·
      simp [Nat.pow_mod, h]
  have h7 : b ^ 2 % 3 = 1 := by
    rcases h4 with (h | h)
    ·
      simp [Nat.pow_mod, h]
    ·
      simp [Nat.pow_mod, h]
  have h8 : c ^ 2 % 3 = 1 := by
    rcases h5 with (h | h)
    ·
      simp [Nat.pow_mod, h]
    ·
      simp [Nat.pow_mod, h]
  have h9 : (a ^ 2 + b ^ 2) % 3 = c ^ 2 % 3 := by
    omega
  omega


lemma lemma_2 (a b c : ℕ)
  (h₂ : a^2 + b^2 = c^2) : 4 ∣ a * b * c := by
  by_contra h2
  push_neg at h2
  have h3 : a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
    by_contra h
    push_neg at h
    have h4 : a % 8 = 0 ∨ a % 8 = 4 := by
      omega
    rcases h4 with (h4 | h4)
    · -- a % 8 = 0
      have : a * b * c % 4 = 0 := by
        have : a % 4 = 0 := by
          omega
        simp [Nat.mul_mod, this]
      omega
    · -- a % 8 = 4
      have : a * b * c % 4 = 0 := by
        have : a % 4 = 0 := by
          omega
        simp [Nat.mul_mod, this]
      omega
  have h4 : b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
    by_contra h
    push_neg at h
    have h5 : b % 8 = 0 ∨ b % 8 = 4 := by
      omega
    rcases h5 with (h5 | h5)
    · -- b % 8 = 0
      have : a * b * c % 4 = 0 := by
        have : b % 4 = 0 := by
          omega
        simp [Nat.mul_mod, this]
      omega
    · -- b % 8 = 4
      have : a * b * c % 4 = 0 := by
        have : b % 4 = 0 := by
          omega
        simp [Nat.mul_mod, this]
      omega
  have h5 : c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
    by_contra h
    push_neg at h
    have h6 : c % 8 = 0 ∨ c % 8 = 4 := by
      omega
    rcases h6 with (h6 | h6)
    · -- c % 8 = 0
      have : a * b * c % 4 = 0 := by
        have : c % 4 = 0 := by
          omega
        simp [Nat.mul_mod, this]
      omega
    · -- c % 8 = 4
      have : a * b * c % 4 = 0 := by
        have : c % 4 = 0 := by
          omega
        simp [Nat.mul_mod, this]
      omega
  have h6 : a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
    rcases h3 with (h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
  have h7 : b ^ 2 % 8 = 1 ∨ b ^ 2 % 8 = 4 := by
    rcases h4 with (h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
  have h8 : c ^ 2 % 8 = 1 ∨ c ^ 2 % 8 = 4 := by
    rcases h5 with (h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
  have h9 : (a ^ 2 + b ^ 2) % 8 = c ^ 2 % 8 := by
    omega
  omega


lemma lemma_3 (a b c : ℕ)
  (h₃ : a^2 + b^2 = c^2) : 5 ∣ a * b * c := by
  by_contra h2
  push_neg at h2
  have h3 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
    by_contra h
    push_neg at h
    have h4 : a % 5 = 0 := by
      omega
    have h5 : a * b * c % 5 = 0 := by
      simp [Nat.mul_mod, h4]
    omega
  have h4 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by
    by_contra h
    push_neg at h
    have h5 : b % 5 = 0 := by
      omega
    have h6 : a * b * c % 5 = 0 := by
      simp [Nat.mul_mod, h5]
    omega
  have h5 : c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by
    by_contra h
    push_neg at h
    have h6 : c % 5 = 0 := by
      omega
    have h7 : a * b * c % 5 = 0 := by
      simp [Nat.mul_mod, h6]
    omega
  have h6 : a ^ 2 % 5 = 1 ∨ a ^ 2 % 5 = 4 := by
    rcases h3 with (h | h | h | h) <;> simp [Nat.pow_mod, h]
  have h7 : b ^ 2 % 5 = 1 ∨ b ^ 2 % 5 = 4 := by
    rcases h4 with (h | h | h | h) <;> simp [Nat.pow_mod, h]
  have h8 : c ^ 2 % 5 = 1 ∨ c ^ 2 % 5 = 4 := by
    rcases h5 with (h | h | h | h) <;> simp [Nat.pow_mod, h]
  have h9 : (a ^ 2 + b ^ 2) % 5 = c ^ 2 % 5 := by
    omega
  omega


theorem number_theory_5287
    (a b c : ℕ)
    (h : a^2 + b^2 = c^2) :
    60 ∣ a * b * c := by
  have h3 : 3 ∣ a * b * c := by
    apply lemma_1 a b c h
  have h4 : 4 ∣ a * b * c := by
    apply lemma_2 a b c h
  have h5 : 5 ∣ a * b * c := by
    apply lemma_3 a b c h
  omega