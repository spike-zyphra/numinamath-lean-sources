import Mathlib

/- Determine a subset $ A\subset \mathbb{N}^*$ having $ 5$ different elements, so that the sum of the squares of its elements equals their product.
Do not simply post the subset, show how you found it. -/
theorem number_theory_55916 (A : Finset ℕ+) :
    A = {1, 3, 4, 9, 107} → A.card = 5 ∧  ∑ x ∈ A, x.val ^2 = ∏ x ∈ A, x.val := by
    intro h
    simp [h]