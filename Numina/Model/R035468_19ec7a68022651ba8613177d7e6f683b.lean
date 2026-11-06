import Mathlib

theorem algebra_286980 (a : ℕ → ℕ)
    (h₀ : ∀ k, a k = (Nat.choose 100 k) * 2 ^ k) :
    Set.ncard {r | 0 ≤ r ∧ r ≤ 99 ∧ a r < a (r + 1)} = 67 := by

  have h1 : {r | 0 ≤ r ∧ r ≤ 99 ∧ a r < a (r + 1)} = Finset.filter (fun r => a r < a (r + 1)) (Finset.Icc (0 : ℕ) 99) := by
    ext r
    simp
    <;> try tauto

  rw [h1]
  rw [Set.ncard_coe_Finset]
  have h2 : ∀ r : ℕ, a r = (Nat.choose 100 r) * 2 ^ r := by
    intro r
    specialize h₀ r
    simpa using h₀

  simp_rw [h2]
  native_decide