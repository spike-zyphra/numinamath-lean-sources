import Mathlib

open Finset

theorem inequalities_39698 (x : Fin 2018 → ℕ) (hx : ∀ i, x i > 0)
    (hxi : Antitone x) (hxe : x 0 = 1)
    (hA : Set.ncard {y | ∃ i ∈ Icc 1 2017, x i = y} = 25) :
    ∑ i ∈ Icc 2 2017, (x i - x (i - 2)) * x i ≥ 623 ∧
    {x : Fin 2018 → ℕ | (∀ i, x i > 0) ∧
      (Antitone x) ∧ x 0 = 1 ∧
      Set.ncard {y | ∃ i ∈ Icc 1 2017, x i = y} = 25}.ncard = Nat.choose 1992 23 := by

  -- Since x is antitone, x i ≤ x 0.
  have h2 : ∀ i : Fin 2018, x i ≤ 1 := by
    intro i
    have h3 : x i ≤ x 0 := by 
      apply hxi 
      simp
      all_goals simp
      all_goals tauto
    have h4 : x 0 = 1 := hxe
    have h5 : x i ≤ 1 := by
      linarith [h3, h4]
    linarith

  -- Since all x i > 0, we must have x i = 1 for all i.
  have h3 : ∀ i : Fin 2018, x i = 1 := by 
    intro i 
    have h4 : x i > 0 := hx i
    have h5 : x i ≤ 1 := h2 i
    omega

  have h4 : Set.ncard {y | ∃ i ∈ Icc 1 2017, x i = y} = 1 := by
    have h9 : {y | ∃ i ∈ Icc 1 2017, x i = y} = {1} := by 
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor 
      · -- Assume y in left side
        rintro ⟨i, hi, heq⟩
        rw [h3 i] at heq 
        omega 
      · -- Assume y = 1
        intro hy 
        rw [hy] 
        use 1 
        constructor 
        · -- Show 1 in [1, 2017]
          native_decide 
        · -- Show x 1 = 1
          apply h3 
    rw [h9] 
    simp

  -- Now contradiction here since we claimed the set has card 1 but required 25
  have h5 : 25 = 1 := by 
    linarith [h4, hA] 
  all_goals omega