import Mathlib

theorem number_theory_126343 (n : ℕ) :
    ¬∃ a b c : ℕ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ (8 * n - 1) = a ^ 2 + b ^ 2 + c ^ 2 := by
  rintro ⟨a, b, c, ha, hb, hc, heq⟩
  have h1 : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
    have h1 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Nat.mul_mod, h1] 
    <;> try rfl
    <;> try tauto
  have h2 : b ^ 2 % 8 = 0 ∨ b ^ 2 % 8 = 1 ∨ b ^ 2 % 8 = 4 := by
    have h1 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Nat.mul_mod, h1] 
    <;> try rfl
    <;> try tauto
  have h3 : c ^ 2 % 8 = 0 ∨ c ^ 2 % 8 = 1 ∨ c ^ 2 % 8 = 4 := by
    have h1 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Nat.mul_mod, h1] 
    <;> try rfl
    <;> try tauto
  by_cases h : n > 0
  · -- Assume n > 0
    have h4 : n > 0 := h
    have h5 : (8 * n - 1) % 8 = 7 := by
      have h5 : n > 0 := h
      have h6 : 1 ≤ 8 * n := by omega
      have h8 : (8 * n) % 8 = 0 := by
        omega
      -- By the theorem, if `1 <= X` and `X % 8 = 0`, then `(X - 1) % 8 = 7`.
      have h7 : (8 * n - 1) % 8 = 7 := by
        have h9 : 8 * n ≥ 1 := by omega
        omega
      omega
    have h5' : (a ^ 2 + b ^ 2 + c ^ 2) % 8 = 7 := by 
      omega 
    omega
  · -- If n = 0
    push_neg at h
    have hn0 : n = 0 := by 
      omega
    rw [hn0] at heq
    have h4 : a ≥ 1 := by
      by_contra h'
      push_neg at h'
      have : a = 0 := by
        omega
      omega
    have h5 : b ≥ 1 := by
      by_contra h'
      push_neg at h'
      have : b = 0 := by
        omega
      omega
    have h6 : c ≥ 1 := by
      by_contra h'
      push_neg at h'
      have : c = 0 := by
        omega
      omega
    have h7 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                show a ≥ 1 by linarith, show b ≥ 1 by linarith, show c ≥ 1 by linarith]
    omega