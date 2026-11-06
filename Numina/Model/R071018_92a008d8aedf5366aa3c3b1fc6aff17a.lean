import Mathlib

theorem algebra_235354 (a : ℤ) :
    Set.ncard {x : ℤ | a * x ^ 2 + 6 = 0} = 0 ∨ Set.ncard {x : ℤ | a * x ^ 2 + 6 = 0} = 2 := by

  have h1 : {x : ℤ | a * x ^ 2 + 6 = 0} = (∅ : Set ℤ) ∨ {x : ℤ | a * x ^ 2 + 6 = 0} = {1, -1} := by
    by_cases h : a = -6
    · -- case a = -6
      have eq : {x : ℤ | a * x ^ 2 + 6 = 0} = {1, -1} := by
        ext x
        simp [h]
        constructor
        · intro h_eq
          have h1 : x^2 = 1 := by linarith
          have : x = 1 ∨ x = -1 := by
            rw [sq_eq_one_iff] at h1
            exact h1
          tauto
        · rintro (rfl | rfl)
          · norm_num
          · norm_num
      right
      exact eq
    · -- a ≠ -6
      have h2 : ∀ x : ℤ, ¬ (a * x ^ 2 + 6 = 0) := by
        intro x
        intro h_eq
        have h3 : a * x ^ 2 = -6 := by linarith
        have h4 : x^2 ≥ 0 := by nlinarith
        have h5 : a < 0 := by nlinarith
        have h6 : x^2 ≤ 6 := by
          nlinarith [show a * x ^ 2 > -7 by omega]
        have h9 : x ≤ 2 := by nlinarith [show x^2 ≥ 0 by nlinarith]
        have h10 : x ≥ -2 := by nlinarith [show x^2 ≥ 0 by nlinarith]
        interval_cases x <;> omega
      have eq1 : {x : ℤ | a * x ^ 2 + 6 = 0} = ∅ := by
        ext x
        simp [h2]
      left
      exact eq1

  rcases h1 with (h_eq | h_eq)
  · -- case empty set
    rw [h_eq]
    simp
  · -- case {1, -1}
    rw [h_eq]
    simp [Set.ncard_pair]
    <;> try { try omega }