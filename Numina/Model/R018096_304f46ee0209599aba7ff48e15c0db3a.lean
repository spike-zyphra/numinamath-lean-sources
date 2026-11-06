import Mathlib

theorem algebra_238026 {n : ℕ} (hn : n ≥ 2) (A B : Finset ℂ)
    (hA : A.card = n) (hB : B.card = n) :
    ∑ x ∈ A, ∑ y ∈ B, x * y = ∑ x ∈ A, x * ∑ y ∈ B, y := by 
  simp [Finset.sum_mul, Finset.mul_sum]
  <;> try { ac_rfl }
  <;> try { tauto }