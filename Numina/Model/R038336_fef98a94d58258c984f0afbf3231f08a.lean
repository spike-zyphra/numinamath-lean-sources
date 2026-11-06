import Mathlib

open Set

theorem number_theory_315819 (f : ℕ → ℕ)
    (h₀ : ∀ x, Even x → f x = x / 2)
    (h₁ : ∀ x, Odd x → f x = (x + 7) / 2) :
    {x | f (f (f x)) = x}.ncard = 8 := by

  have h2 : {x | f (f (f x)) = x} = {0, 1, 2, 3, 4, 5, 6, 7} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor
    · -- First, prove that if $f(f(f(x))) = x$, then $x \in \{ 0, 1, ..., 7 \}$.
      intro h
      have h3 : x ≤ 7 := by
        by_contra h4
        push_neg at h4
        have h5 : x ≥ 8 := by omega
        have h6 : f (f (f x)) < x := by
          by_cases h10 : x % 2 = 0
          · -- x is even
            have h11 : Even x := by
              refine ⟨x / 2, by omega⟩
            have hx1 : f x = x / 2 := h₀ x h11
            by_cases h12 : (x / 2) % 2 = 0
            · -- f(x) is even
              have h13 : Even (x / 2) := by
                refine ⟨(x / 2) / 2, by omega⟩
              have hx2 : f (f x) = (x / 2) / 2 := by
                rw [hx1]
                apply h₀
                exact h13
              by_cases h14 : ((x / 2) / 2) % 2 = 0
              · -- f(f(x)) is even
                have h15 : Even ((x / 2) / 2) := by
                  refine ⟨((x / 2) / 2) / 2, by omega⟩
                have hx3 : f (f (f x)) = ((x / 2) / 2) / 2 := by
                  rw [hx2]
                  apply h₀
                  exact h15
                omega
              · -- f(f(x)) is odd
                have h14' : Odd ((x / 2) / 2) := by
                  refine ⟨((x / 2) / 2) / 2, by omega⟩
                have hx3 : f (f (f x)) = ((x / 2) / 2 + 7) / 2 := by
                  rw [hx2]
                  apply h₁
                  exact h14'
                omega
            · -- f(x) is odd
              have h12' : Odd (x / 2) := by
                refine ⟨(x / 2) / 2, by omega⟩
              have hx2 : f (f x) = (x / 2 + 7) / 2 := by
                rw [hx1]
                apply h₁
                exact h12'
              by_cases h12 : (x / 2 + 7) / 2 % 2 = 0
              · -- f(f(x)) is even
                have h13 : Even ((x / 2 + 7) / 2) := by
                  refine ⟨((x / 2 + 7) / 2) / 2, by omega⟩
                have hx3 : f (f (f x)) = ((x / 2 + 7) / 2) / 2 := by
                  rw [hx2]
                  apply h₀
                  exact h13
                omega
              · -- f(f(x)) is odd
                have h14' : Odd ((x / 2 + 7) / 2) := by
                  refine ⟨((x / 2 + 7) / 2) / 2, by omega⟩
                have hx3 : f (f (f x)) = ((x / 2 + 7) / 2 + 7) / 2 := by
                  rw [hx2]
                  apply h₁
                  exact h14'
                omega
          · -- x is odd
            have h11 : Odd x := by
              refine ⟨x / 2, by omega⟩
            have hx1 : f x = (x + 7) / 2 := h₁ x h11
            by_cases h12 : (x + 7) / 2 % 2 = 0
            · -- f(x) is even
              have h13 : Even ((x + 7) / 2) := by
                refine ⟨((x + 7) / 2) / 2, by omega⟩
              have hx2 : f (f x) = ((x + 7) / 2) / 2 := by
                rw [hx1]
                apply h₀
                exact h13
              by_cases h14 : ((x + 7) / 2) / 2 % 2 = 0
              · -- f(f(x)) is even
                have h15 : Even (((x + 7) / 2) / 2) := by
                  refine ⟨(((x + 7) / 2) / 2) / 2, by omega⟩
                have hx3 : f (f (f x)) = (((x + 7) / 2) / 2) / 2 := by
                  rw [hx2]
                  apply h₀
                  exact h15
                omega
              · -- f(f(x)) is odd
                have h14' : Odd (((x + 7) / 2) / 2) := by
                  refine ⟨(((x + 7) / 2) / 2) / 2, by omega⟩
                have hx3 : f (f (f x)) = (((x + 7) / 2) / 2 + 7) / 2 := by
                  rw [hx2]
                  apply h₁
                  exact h14'
                omega
            · -- f(x) is odd
              have h12' : Odd ((x + 7) / 2) := by
                refine ⟨((x + 7) / 2) / 2, by omega⟩
              have hx2 : f (f x) = ((x + 7) / 2 + 7) / 2 := by
                rw [hx1]
                apply h₁
                exact h12'
              by_cases h12 : ((x + 7) / 2 + 7) / 2 % 2 = 0
              · -- f(f(x)) is even
                have h13 : Even (((x + 7) / 2 + 7) / 2) := by
                  refine ⟨(((x + 7) / 2 + 7) / 2) / 2, by omega⟩
                have hx3 : f (f (f x)) = (((x + 7) / 2 + 7) / 2) / 2 := by
                  rw [hx2]
                  apply h₀
                  exact h13
                omega
              · -- f(f(x)) is odd
                have h14' : Odd (((x + 7) / 2 + 7) / 2) := by
                  refine ⟨(((x + 7) / 2 + 7) / 2) / 2, by omega⟩
                have hx3 : f (f (f x)) = (((x + 7) / 2 + 7) / 2 + 7) / 2 := by
                  rw [hx2]
                  apply h₁
                  exact h14'
                omega
        omega
      interval_cases x <;> norm_num [Nat.even_iff, Nat.odd_iff, h₀, h₁] at h ⊢ <;> tauto
    · -- Now prove the reverse: if $x \in \{0, 1, 2, 3, 4, 5, 6, 7 \}$, then $f(f(f(x))) = x$.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        norm_num [Nat.even_iff, Nat.odd_iff, h₀, h₁]
  rw [h2]
  rw [Set.ncard_eq_toFinset_card']
  simp