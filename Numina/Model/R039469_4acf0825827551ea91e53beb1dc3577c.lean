import Mathlib

theorem number_theory_55916 (A : Finset ℕ+) :
    A = {1, 3, 4, 9, 107} → A.card = 5 ∧  ∑ x ∈ A, x.val ^2 = ∏ x ∈ A, x.val := by
  intro hA
  rw [hA]
  constructor
  · -- Show the cardinality of the set {1, 3, 4, 9, 107} is 5.
    native_decide
  · -- Show that the sum of the squares equals the product.
    native_decide