import Mathlib

open Finset

/-
Problem: What is the probability that exactly 6 out of 7 letters are placed in their correct envelopes?Step-by-Step Explanation 
-/
theorem Combinatorics_610909
    (σ : Equiv.Perm (Fin 7)) 
    (h₁ : #(Finset.filter (fun x => σ x = x) Finset.univ) = 6) : False := by
    
  have h₂ : Finset.card (Finset.filter (fun x => σ x = x) Finset.univ) = 6 := by simpa using h₁

  -- Since σ is a permutation, ∃ one element such that σ x ≠ x
  have h₃ : ∃ x : Fin 7, σ x ≠ x := by
    by_contra! h₄

    -- If all elements are fixed, then σ is the identity permutation
    have h₅ : σ = 1 := by
      apply Equiv.ext
      intro x
      simp_all [Equiv.Perm.one_apply]

    -- If σ is the identity, then the number of fixed points is 7, not 6
    have h₆ : Finset.card (Finset.filter (fun x => σ x = x) Finset.univ) = 7 := by
      simp [h₅]

    -- Contradiction with h₂
    linarith
  
  obtain ⟨x, h₇⟩ := h₃

  -- For all elements y ≠ x, σ y = y (because only x is not fixed)
  have h₈ : ∀ y : Fin 7, y ≠ x → σ y = y := by
    intro y hy
    have h₉ : σ y = y := by
      by_contra h₁₀

      -- If σ y ≠ y, then y must be x (but y ≠ x)
      have h₁₁ : y = x := by
        by_contra h₁₂

        -- If y ≠ x, then σ y = y (but assumed σ y ≠ y)
        have h₁₃ : σ y = y := by
          have h₁₄ : y ∈ Finset.filter (fun x => σ x = x) Finset.univ := by

            -- Show that y is fixed if y ≠ x
            have h₁₅ : σ y = y := by
              by_cases h₁₆ : σ y = y
              · exact h₁₆
              · exfalso

                -- Use the fact that the number of non-fixed points is 1.
                have h₁₇ : y ∈ Finset.filter (fun x => σ x ≠ x) Finset.univ := by
                  simp_all [Finset.mem_filter, Finset.mem_univ, true_and] -- y is a non-fixed point
                  
                -- Derive contradiction by showing there are at least two non-fixed points (x and y)
                have h₁₈ : Finset.card (Finset.filter (fun x => σ x ≠ x) Finset.univ) ≥ 2 := by
                  have h₁₉ : y ≠ x := by
                    intro h₂₀
                    simp_all
                  have h₂₁ : Finset.card (Finset.filter (fun x => σ x ≠ x) Finset.univ) ≥ 2 := by
                    have h₂₂ : Finset.card (Finset.filter (fun x => σ x ≠ x) Finset.univ) ≥ Finset.card ({y, x} : Finset (Fin 7)) := by
                      apply Finset.card_le_card
                      intro a h₂₃
                      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and] at h₂₃ ⊢
                      aesop
                      
                    -- The set {x, y} has cardinality 2 since x ≠ y
                    have h₂₄ : Finset.card ({y, x} : Finset (Fin 7)) ≥ 2 := by
                      by_cases h₂₅ : y = x
                      · contradiction
                      · simp [h₂₅, Finset.card_insert_of_not_mem, Finset.mem_singleton]
                    linarith
                  exact h₂₁
                  
                -- However, total non-fixed points must be 7 - 6 = 1 (from h₂)
                have h₂₆ : Finset.card (Finset.filter (fun x => σ x ≠ x) Finset.univ) = 1 := by
                  have h₂₇ : Finset.card (Finset.filter (fun x => σ x ≠ x) Finset.univ) = 7 - Finset.card (Finset.filter (fun x => σ x = x) Finset.univ) := by

                    -- Non-fixed points are the complement of fixed points in the universal set
                    have h₂₈ : Finset.filter (fun x => σ x ≠ x) Finset.univ = Finset.univ \ Finset.filter (fun x => σ x = x) Finset.univ := by
                      ext x
                      simp [Finset.mem_filter, Finset.mem_univ, true_and]
                    rw [h₂₈]
                    rw [Finset.card_sdiff (show Finset.filter (fun x => σ x = x) Finset.univ ⊆ Finset.univ by simp [Finset.filter_subset])]
                    simp [h₂]
                  rw [h₂₇]

                 -- Arithmetic solver to show 7 - 6 = 1
                  omega 
                  
                -- Contradiction: 2 ≥ 1 is false
                omega 
            simp_all [Finset.mem_filter]
          simp_all [Finset.mem_filter]
        contradiction
      contradiction
    simp_all


  -- Now, we have σ x ≠ x and σ y = y for all y ≠ x
  have h₂₉ : σ (σ x) = σ x := by
    by_cases h₃₀ : σ x = x
    · exfalso; apply h₇; exact h₃₀
    · have h₃₁ : σ (σ x) = σ x := by
        have h₃₂ : σ x ≠ x := h₃₀
        have h₃₃ : σ (σ x) = σ x := by
          by_cases h₃₄ : σ x = x
          · contradiction
          · have h₃₅ : σ (σ x) = σ x := h₈ (σ x) (by aesop)
            exact h₃₅
        exact h₃₃
      exact h₃₁
  
  have h₃₆ : σ x = x := by
    apply σ.injective
    have h₃₇ : σ (σ x) = σ x := h₂₉
    simpa using h₃₇
  
  exact h₇ h₃₆