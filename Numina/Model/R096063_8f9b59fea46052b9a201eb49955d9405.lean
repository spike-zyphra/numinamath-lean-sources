import Mathlib

theorem number_theory_40045 (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (hp : Nat.Prime p)
    (S : ℕ → Finset ℕ) (hS : ∀ a, S a = {b | 0 ≤ b ∧ b ≤ p - 1 ∧ ∃ c, (c ^ n + a * c) ≡ b [MOD p]}) :
    ∃ k, (1 / ((p - 1) : ℚ)) * ∑ a in Finset.Icc 1 (p - 1), (S a).card = k := by 
  refine' ⟨(1 / ((p - 1) : ℚ)) * ∑ a in Finset.Icc 1 (p - 1), (S a).card, by simp ⟩