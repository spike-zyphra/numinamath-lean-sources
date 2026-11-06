import Mathlib

/-- Problem 3.
    Show that if $H_{1}$ and $H_{2}$ are two subgroups of a group $(G, \cdot)$,
    such that $G=H_{1} \cup H_{2}$, then $H_{1}=G$ or $H_{2}=G$. -/
theorem algebra_117146 {G : Type*} [Group G] (H1 H2 : Subgroup G)
    (h : ∀ x : G, x ∈ H1 ∨ x ∈ H2) :
    H1 = ⊤ ∨ H2 = ⊤ := by
  rw[Subgroup.eq_top_iff', Subgroup.eq_top_iff']
  -- If neither of the subgroups equal $G$, there must be $x_i \notin H_i$.
  by_contra! h'
  obtain ⟨⟨x1, hx1⟩, ⟨x2,hx2⟩⟩ := h'
  -- By assumption, $x_1 \in H_2, x_2 \in H_1$.
  have hx1' : x1 ∈ H2 := by specialize h x1; tauto
  have hx2' : x2 ∈ H1 := by specialize h x2; tauto
  -- Consider the product $x_1 x_2$.
  cases h (x1 * x2) with
  | inl h =>
      -- If it is element of $H_1$, so must $x_1 = (x_1 x_2) x_2^{-1}$ be, since $x_2^{-1} \in H_1$.
      apply hx1
      -- But that is impossible by assumption.
      rwa[H1.mul_mem_cancel_right hx2'] at h
  | inr h =>
      -- If it is element of $H_2$, so must $x_2 = x_1^{-1} (x_1 x_2)$ be, since $x_1^{-1} \in H_2$.
      apply hx2
      -- But that is also impossible.
      rwa[H2.mul_mem_cancel_left hx1'] at h
  -- Yet one of the two cases must hold by assumption, hence we arrive at a contradiction.