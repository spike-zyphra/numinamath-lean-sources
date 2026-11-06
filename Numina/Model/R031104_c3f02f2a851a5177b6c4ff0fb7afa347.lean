import Mathlib

open Set Real

theorem algebra_108400 :
  {a : ℝ | ∃ A : Set ℝ , A = {x | (a * x - 1) * (a - x) > 0} ∧ 2 ∈ A ∧ 3 ∉ A} = 
  {a | (2 < a ∧ a ≤ 3) ∨ (1/3 ≤ a ∧ a < 1/2)} := by

  ext a
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume h, prove the goal
    rintro ⟨A, hA, h2, h3⟩
    
    have h1 : (a * 2 - 1) * (a - 2) > 0 := by
      have h2' : 2 ∈ A := h2
      rw [hA] at h2'
      simpa using h2'

    have h4 : (a * 3 - 1) * (a - 3) ≤ 0 := by
      have h3' : 3 ∉ A := h3
      have h5 : 3 ∉ ( {x | (a * x - 1) * (a - x) > 0} ) := by
        simpa [hA] using h3'
      simp at h5 ⊢
      all_goals nlinarith

    by_cases h5 : a < 1/2

    · -- case a < 1/2
      have ha3 : 1 / 3 ≤ a := by
        nlinarith

      right
      constructor
      · -- Show 1/3 ≤ a
        linarith
      · -- Show a < 1/2
        linarith
    · -- case a ≥ 1/2
      have ha6 : a ≥ 1 / 2 := by
        linarith

      have ha7 : a ≤ 3 := by
        nlinarith

      have ha8 : a > 2 := by
        nlinarith

      left
      constructor
      · -- Show 2 < a
        linarith
      · -- Show a ≤ 3
        linarith
  · -- Now the reverse direction
    rintro (h | h)
    · -- Case 1: 2 < a ∧ a ≤ 3
      rcases h with ⟨ha1, ha2⟩
      use {x | (a * x - 1) * (a - x) > 0}
      constructor
      · -- Show that A is defined as given
        rfl
      constructor
      · -- Show 2 ∈ A
        have h1 : (a * 2 - 1) * (a - 2) > 0 := by
          nlinarith
        simpa using h1
      · -- Show 3 ∉ A
        have h2 : (a * 3 - 1) * (a - 3) ≤ 0 := by
          nlinarith
        simpa using h2
    · -- Case 2: 1/3 ≤ a ∧ a < 1/2
      rcases h with ⟨ha1, ha2⟩
      use {x | (a * x - 1) * (a - x) > 0}
      constructor
      · -- Show that A is defined as given
        rfl
      constructor
      · -- Show 2 ∈ A
        have h1 : (a * 2 - 1) * (a - 2) > 0 := by
          nlinarith
        simpa using h1
      · -- Show 3 ∉ A
        have h2 : (a * 3 - 1) * (a - 3) ≤ 0 := by
          nlinarith
        simpa using h2