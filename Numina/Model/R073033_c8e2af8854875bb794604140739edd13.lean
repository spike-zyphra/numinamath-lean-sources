import Mathlib

theorem algebra_93978 (f : ℕ → ℕ) (hf : ∀ x, f x = x ^ 2 + 3 * x + 2) :
    Set.ncard {s | s ∈ Finset.Icc 0 25 ∧ f s % 6 = 0} = 17 := by 
  have h1 : {s | s ∈ Finset.Icc 0 25 ∧ f s % 6 = 0} = 
    Finset.filter (λ s => f s % 6 = 0) (Finset.Icc 0 25) := by
    ext s
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  simp [hf]
  <;> try { native_decide }