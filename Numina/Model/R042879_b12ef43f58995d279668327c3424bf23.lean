import Mathlib

theorem number_theory_5645 :
  (∀ a b : ℕ, a ≠ b → (a > b ∨ a < b) ∧ ¬(a > b ∧ a < b)) ∧
  (∀ a : ℕ, ∃ e : ℕ, a ≥ e) ∧
  (∀ a b c : ℕ, a > b ∧ b > c → a > c) ∧
  (∀ a x : ℕ, a + x > b + x ↔ a > b) ∧
  (∀ a b : ℕ, a > b → a ≥ b + 1) ∧
  (∀ a : ℕ, ¬∃ m : ℕ, a + 1 > m ∧ m > a) := by
  constructor
  · -- Proof of (1)
    intro a b hneq
    have h1 : a > b ∨ a < b := by
      by_contra h
      push_neg at h
      have h2 : a = b := by linarith
      contradiction
    have h2 : ¬(a > b ∧ a < b) := by
      intro h
      omega
    exact ⟨h1, h2⟩
  constructor
  · -- Proof of (2)
    intro a
    use a
    all_goals try { omega }
  constructor
  · -- Proof of (3)
    intro a b c hab
    rcases hab with ⟨hab1, hab2⟩
    linarith
  constructor
  · -- Proof of (4)
    intro a x
    constructor
    · -- Proof of direction 1
      intro h
      omega
    · -- Proof of direction 2
      intro h
      omega
  constructor
  · -- Proof of (5)
    intro a b h
    omega
  · -- Proof of (6)
    intro a
    intro h
    rcases h with ⟨m, hm1, hm2⟩
    omega