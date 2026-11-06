import Mathlib

theorem algebra_271007 :
    Set.Infinite {(a, b, c, x, y) : ℤ × ℤ × ℤ × ℤ × ℤ |
      a + b + c = x + y ∧ a ^ 3 + b ^ 3 + c ^ 3 = x ^ 3 + y ^ 3 ∧
      ∃ d, b = a + d ∧ c = b + d} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (-1, (0 : ℤ), 1, (t : ℤ), (- (t : ℤ)) ) )
  · -- Show f is injective
    intro t₁ t₂ h
    simp [Prod.ext_iff] at h
    all_goals omega
  · -- Show that all elements in the image are part of the set
    intro t
    simp [Prod.ext_iff]
    <;> ring_nf
    <;> omega