import Mathlib

theorem algebra_16556 : {x | ∃ n, x = 3 * n + 1 ∧ n ≥ 0 ∧ n ≤ 669}.encard = 670 := by 
  have h1 : {x | ∃ n, x = 3 * n + 1 ∧ n ≥ 0 ∧ n ≤ 669} = Finset.image (λ (n : ℕ) => 3 * n + 1) (Finset.Icc 0 669) := by 
    ext x 
    simp 
    <;> aesop 
    <;> omega 
  rw [h1]
  rw [Finset.image]
  simp [Finset.Icc]
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { native_decide }