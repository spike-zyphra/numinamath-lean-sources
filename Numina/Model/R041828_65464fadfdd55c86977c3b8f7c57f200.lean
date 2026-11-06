import Mathlib

theorem number_theory_266359 (a : ℕ → ℕ) (ha : ∀ i, a i ∈ Finset.Icc 10 99)
    (h : ∀ i, (Nat.digits 10 (a i)).sum ≠ 6 ∧ (Nat.digits 10 (a i)).sum ≠ 9)
    (h' : ∀ i, ∀ j, a i = a j → i = j) :
    IsGreatest {x | ¬∃ n, a n = x} 10 := by 
  exfalso
  -- Show that the function a is injective
  have h_inj : Function.Injective a := by
    intro i j heq
    -- h' : ∀ i, ∀ j, a i = a j → i = j
    -- applying injective at indices i and j 
    specialize h' i j 
    -- hypothesis heq: a i = a j
    exact_mod_cast h' heq 
  -- Show that the image of a is subset of a finite set
  have h5 : Set.Finite (Set.range a) := by
    have h6 : Set.range a ⊆ (Finset.Icc 10 99 : Set ℕ) := by 
      intro x hx 
      rcases hx with ⟨i, hi⟩ 
      have h7 : a i ∈ Finset.Icc 10 99 := by 
        apply ha i 
      have h8 : a i ∈ (Finset.Icc 10 99 : Set ℕ) := by 
        exact Finset.mem_coe.mpr (show a i ∈ Finset.Icc 10 99 by 
          simpa using h7 
        )
      rw [show x = a i by linarith] 
      exact h8 
    have h7 : Set.Finite ((Finset.Icc 10 99 : Set ℕ)) := by 
      exact Finset.finite_toSet (Finset.Icc 10 99)
    exact Set.Finite.subset h7 h6 
  -- Show contradiction since Set.range a is infinite
  have h6 : Set.Infinite (Set.range a) := by
    apply Set.infinite_range_of_injective h_inj 
  exfalso 
  have h7 : ¬ Set.Finite (Set.range a) := h6 
  exact h7 h5