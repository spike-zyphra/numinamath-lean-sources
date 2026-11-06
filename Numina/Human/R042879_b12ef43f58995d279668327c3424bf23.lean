import Mathlib

theorem number_theory_5645 :
  (∀ a b : ℕ, a ≠ b → (a > b ∨ a < b) ∧ ¬(a > b ∧ a < b)) ∧
  (∀ a : ℕ, ∃ e : ℕ, a ≥ e) ∧
  (∀ a b c : ℕ, a > b ∧ b > c → a > c) ∧
  (∀ a x : ℕ, a + x > b + x ↔ a > b) ∧
  (∀ a b : ℕ, a > b → a ≥ b + 1) ∧
  (∀ a : ℕ, ¬∃ m : ℕ, a + 1 > m ∧ m > a) := by 
  constructor
  · omega
  constructor
  · -- Proof that for any a, there exists e such that a ≥ e
    intro a
    refine ⟨a, by simp⟩
  constructor
  · -- Proof of transitivity: a > b ∧ b > c → a > c
    intros a b c h
    cases h with
    | intro h1 h2 => linarith
  constructor
  · -- Proof that a + x > b + x ↔ a > b
    intros a x
    apply Iff.intro
    · intro h
      linarith
    · intro h
      linarith
  constructor
  · -- Proof that a > b → a ≥ b + 1
    intros a b h
    linarith
  · -- Proof that there is no m such that a + 1 > m > a
    intro a
    intro h
    rcases h with ⟨m, hm1, hm2⟩
    have : m ≤ a := by linarith
    linarith