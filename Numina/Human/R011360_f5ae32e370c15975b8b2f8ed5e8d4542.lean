import Mathlib

/-
PROBLEM 2. Let $(G, \cdot)$ be a group and the set $Z(G)=\{x \in G: x y=y x, \forall y \in G\}$.
Show that if $x^{2}=e$, for any $x \in G \backslash \mathrm{Z}(G)$, then the group is commutative.-/
theorem algebra_107072 {G : Type} [Group G]
  (h : ∀ x : G ⧸ Subgroup.center G, x ^ 2 = 1) :
    ∀ a b : G ⧸ Subgroup.center G, a * b = b * a := by
  intro a b
  -- First, $\forall x \in G \backslash \mathrm{Z}(G), x = x ^ {-1}$
  have h' : ∀ x : G ⧸ Subgroup.center G, x⁻¹ = x := by
    intro x
    calc
      _ = (x⁻¹) ^ 2 * x := by group
      _ = 1 * x := by rw [h x⁻¹]
      _ = _ := by group
  -- Second, $ab=ab(a^{-1}b^{-1})ba=(ab)²ba=1\cdot ba = ba$-/
  calc
    _ = a * b * (a⁻¹ * b⁻¹) * b * a := by group
    _ = (a * b) ^ 2 * b * a := by simp [h', pow_two (a * b)]
    _ = 1 * b * a := by rw [h (a * b)]
    _ = b * a := by rw [one_mul]
