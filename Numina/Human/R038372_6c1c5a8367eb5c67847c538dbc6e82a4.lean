import Mathlib

/- H.S.

Prove that the equation $x^{2}+y^{2}+z^{2}=x^{3}+y^{3}+z^{3}$ has an infinite number of solutions in integers $x, y, z$. -/
theorem algebra_190538 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x ^ 2 + y ^ 2 + z ^ 2 = x ^ 3 + y ^ 3 + z ^ 3} := by
  -- Let s = {(k * (2 * k^2 + 1), 2 * k^2 + 1, -k * (2 * k^2 + 1) | k ∈ ℕ}
  set s := (fun k : ℕ => (⟨k * (2 * k^2 + 1), 2 * k^2 + 1, -k * (2 * k^2 + 1)⟩ : ℤ × ℤ × ℤ)) '' Set.univ
  -- Show that s ⊆ {(x, y, z) : ℤ × ℤ × ℤ | x ^ 2 + y ^ 2 + z ^ 2 = x ^ 3 + y ^ 3 + z ^ 3}
  have hs : s ⊆ {(x, y, z) : ℤ × ℤ × ℤ | x ^ 2 + y ^ 2 + z ^ 2 = x ^ 3 + y ^ 3 + z ^ 3} := by
    intro ⟨x, y, z⟩
    simp only [Set.image_univ, neg_mul, Set.mem_range, Prod.mk.injEq, Set.mem_setOf_eq,
      forall_exists_index, and_imp, s]
    intro k eq1 eq2 eq3
    subst x y z
    -- Simplify and get the result.
    ring
  -- Show that s is infinite.
  apply Set.Infinite.mono hs
  -- It is enough to show that fun k => ⟨k * (2 * k^2 + 1), 2 * k^2 + 1, -k * (2 * k^2 + 1)⟩ is injective.
  apply Set.Infinite.image _ Set.infinite_univ
  simp [Set.InjOn]
  -- This function is injective because a * (2 * a^2 + 1) = b * (2 * b^2 + 1) implies a = b.
  norm_cast
  omega