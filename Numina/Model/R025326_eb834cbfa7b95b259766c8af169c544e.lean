import Mathlib

theorem algebra_178732 :
    Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x ^ 2 + y ^ 2 - z ^ 2 - x - 3 * y - z - 4 = 0} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (8 * (t : ℤ) ^ 2 + 2 * (t : ℤ) - 3, 4 * (t : ℤ) + 2, 8 * (t : ℤ) ^ 2 + 2 * (t : ℤ) - 3))
  · -- Show f is injective
    intro t₁ t₂ h
    simp [Prod.ext_iff] at h ⊢
    all_goals omega
  · -- Show that all elements of f are in the set
    intro t 
    simp [Prod.ext_iff]
    <;> ring