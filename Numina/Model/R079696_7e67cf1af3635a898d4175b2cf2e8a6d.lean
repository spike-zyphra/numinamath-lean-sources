import Mathlib

theorem algebra_218607 (f : ℕ → ℕ) (hf : ∀ x, f x = x ^ 2 + 3 * x + 2)
    (S : Finset ℕ) (hS : S = Finset.Icc 0 100) :
    {a | a ∈ S ∧ 6 ∣ f a}.ncard = 67 := by
  have h1 : {a | a ∈ S ∧ 6 ∣ f a} = Finset.filter (λ a => 6 ∣ f a) S := by
    ext a
    simp [hS]
  rw [h1]
  rw [Finset.filter]
  simp [hS, hf]
  <;> try { native_decide }