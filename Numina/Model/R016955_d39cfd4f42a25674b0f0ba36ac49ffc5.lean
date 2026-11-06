import Mathlib

open Nat

theorem number_theory_273882 (f : ℕ → ℕ)
    (h₀ : ∀ x, Even x → f x = x / 2)
    (h₁ : ∀ x, Odd x → f x = (x + 7) / 2) :
    {x | f (f (f x)) = x}.ncard = 8 := by
  have h2 : {x | f (f (f x)) = x} = {0, 1, 2, 3, 4, 5, 6, 7} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume f(f(f x)) = x, prove x ∈ {0, 1, 2, 3, 4, 5, 6, 7}
      intro h_eq
      have h3 : x ≤ 7 := by
        by_contra h
        push_neg at h
        have h4 : x ≥ 8 := by omega
        have h5 : f (f (f x)) < x := by
          by_cases h8 : x % 2 = 0
          · -- x is even
            have h10 : Even x := by
              refine' ⟨x / 2, by omega⟩
            have h11 : f x = x / 2 := h₀ x h10
            by_cases h12 : (x / 2) % 2 = 0
            · -- x/2 is even
              have h13 : Even (x / 2) := by
                refine' ⟨(x / 2) / 2, by omega⟩
              have h14 : f (x / 2) = (x / 2) / 2 := h₀ (x / 2) h13
              by_cases h15 : ((x / 2) / 2) % 2 = 0
              · -- x/4 is even
                have h16 : Even ((x / 2) / 2) := by
                  refine' ⟨((x / 2) / 2) / 2, by omega⟩
                have h17 : f ((x / 2) / 2) = ((x / 2) / 2) / 2 := h₀ ((x / 2) / 2) h16
                have h18 : f (f (f x)) = ((x / 2) / 2) / 2 := by
                  rw [h11, h14, h17]
                have h19 : ((x / 2) / 2) / 2 < x := by
                  omega
                linarith
              · -- x/4 is odd
                have h16 : Odd ((x / 2) / 2) := by
                  have : ((x / 2) / 2) % 2 = 1 := by omega
                  exact Nat.odd_iff.mpr this
                have h17 : f ((x / 2) / 2) = ((x / 2) / 2 + 7) / 2 := h₁ ((x / 2) / 2) h16
                have h18 : f (f (f x)) = ((x / 2) / 2 + 7) / 2 := by
                  rw [h11, h14, h17]
                have h19 : ((x / 2) / 2 + 7) / 2 < x := by
                  omega
                linarith
            · -- x/2 is odd
              have h13 : Odd (x / 2) := by
                have : (x / 2) % 2 = 1 := by omega
                exact Nat.odd_iff.mpr this
              have h14 : f (x / 2) = (x / 2 + 7) / 2 := h₁ (x / 2) h13
              by_cases h15 : ((x / 2 + 7) / 2) % 2 = 0
              · -- (x/2 + 7)/2 is even
                have h16 : Even ((x / 2 + 7) / 2) := by
                  refine' ⟨((x / 2 + 7) / 2) / 2, by omega⟩
                have h17 : f ((x / 2 + 7) / 2) = ((x / 2 + 7) / 2) / 2 := h₀ ((x / 2 + 7) / 2) h16
                have h18 : f (f (f x)) = ((x / 2 + 7) / 2) / 2 := by
                  rw [h11, h14, h17]
                have h19 : ((x / 2 + 7) / 2) / 2 < x := by
                  omega
                linarith
              · -- (x/2 + 7)/2 is odd
                have h16 : Odd ((x / 2 + 7) / 2) := by
                  have : ((x / 2 + 7) / 2) % 2 = 1 := by omega
                  exact Nat.odd_iff.mpr this
                have h17 : f ((x / 2 + 7) / 2) = ((x / 2 + 7) / 2 + 7) / 2 := h₁ ((x / 2 + 7) / 2) h16
                have h18 : f (f (f x)) = ((x / 2 + 7) / 2 + 7) / 2 := by
                  rw [h11, h14, h17]
                have h19 : ((x / 2 + 7) / 2 + 7) / 2 < x := by
                  omega
                linarith
          · -- x is odd
            have h10 : Odd x := by
              have : x % 2 = 1 := by omega
              exact Nat.odd_iff.mpr this
            have h11 : f x = (x + 7) / 2 := h₁ x h10
            by_cases h12 : ((x + 7) / 2) % 2 = 0
            · -- (x + 7)/2 is even
              have h13 : Even ((x + 7) / 2) := by
                refine' ⟨((x + 7) / 2) / 2, by omega⟩
              have h14 : f ((x + 7) / 2) = ((x + 7) / 2) / 2 := h₀ ((x + 7) / 2) h13
              by_cases h15 : (((x + 7) / 2) / 2) % 2 = 0
              · -- ((x + 7)/2)/2 is even
                have h16 : Even (((x + 7) / 2) / 2) := by
                  refine' ⟨(((x + 7) / 2) / 2) / 2, by omega⟩
                have h17 : f (((x + 7) / 2) / 2) = (((x + 7) / 2) / 2) / 2 := h₀ (((x + 7) / 2) / 2) h16
                have h18 : f (f (f x)) = (((x + 7) / 2) / 2) / 2 := by
                  rw [h11, h14, h17]
                have h19 : (((x + 7) / 2) / 2) / 2 < x := by
                  omega
                linarith
              · -- ((x + 7)/2)/2 is odd
                have h16 : Odd (((x + 7) / 2) / 2) := by
                  have : (((x + 7) / 2) / 2) % 2 = 1 := by omega
                  exact Nat.odd_iff.mpr this
                have h17 : f (((x + 7) / 2) / 2) = (((x + 7) / 2) / 2 + 7) / 2 := h₁ (((x + 7) / 2) / 2) h16
                have h18 : f (f (f x)) = (((x + 7) / 2) / 2 + 7) / 2 := by
                  rw [h11, h14, h17]
                have h19 : (((x + 7) / 2) / 2 + 7) / 2 < x := by
                  omega
                linarith
            · -- (x + 7)/2 is odd
              have h13 : Odd ((x + 7) / 2) := by
                have : ((x + 7) / 2) % 2 = 1 := by omega
                exact Nat.odd_iff.mpr this
              have h14 : f ((x + 7) / 2) = ((x + 7) / 2 + 7) / 2 := h₁ ((x + 7) / 2) h13
              by_cases h15 : (((x + 7) / 2 + 7) / 2) % 2 = 0
              · -- ((x + 7)/2 + 7)/2 is even
                have h16 : Even (((x + 7) / 2 + 7) / 2) := by
                  refine' ⟨(((x + 7) / 2 + 7) / 2) / 2, by omega⟩
                have h17 : f (((x + 7) / 2 + 7) / 2) = (((x + 7) / 2 + 7) / 2) / 2 := h₀ (((x + 7) / 2 + 7) / 2) h16
                have h18 : f (f (f x)) = (((x + 7) / 2 + 7) / 2) / 2 := by
                  rw [h11, h14, h17]
                have h19 : (((x + 7) / 2 + 7) / 2) / 2 < x := by
                  omega
                linarith
              · -- ((x + 7)/2 + 7)/2 is odd
                have h16 : Odd (((x + 7) / 2 + 7) / 2) := by
                  have : (((x + 7) / 2 + 7) / 2) % 2 = 1 := by omega
                  exact Nat.odd_iff.mpr this
                have h17 : f (((x + 7) / 2 + 7) / 2) = (((x + 7) / 2 + 7) / 2 + 7) / 2 := h₁ (((x + 7) / 2 + 7) / 2) h16
                have h18 : f (f (f x)) = (((x + 7) / 2 + 7) / 2 + 7) / 2 := by
                  rw [h11, h14, h17]
                have h19 : (((x + 7) / 2 + 7) / 2 + 7) / 2 < x := by
                  omega
                linarith
        omega
      interval_cases x <;> norm_num at h_eq ⊢ <;> tauto
    · -- Show that if x ∈ {0, 1, 2, 3, 4, 5, 6, 7}, then f(f(f x)) = x
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
      norm_num [h₀, h₁, Nat.even_iff, Nat.odd_iff]
  rw [h2]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  all_goals try { native_decide }