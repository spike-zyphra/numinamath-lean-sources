import Mathlib

theorem number_theory_256044 (S : Finset ℕ) (hS : S.card = 6)
    (hS1 : ∑ x ∈ S, x = 72) (hS2 : ∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ 10 * a + b ∈ S ∧
    10 * b + a ∈ S ∧ (S \ {10 * a + b, 10 * b + a}).card = 4 ∧
    ∑ x ∈ S, x = 90) :
    {x | ∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ x = 10 * a + b ∧ 10 * b + a ∈ S}.ncard = 5 := by
  rcases hS2 with ⟨a, b, ha, hb, hab, hab', hS3, hS2⟩
  linarith