import Mathlib

theorem algebra_300221 {A : Set ℝ} (hA : ∀ a ∈ A, 1 / (1 - a) ∈ A)
    (h2 : 2 ∈ A) :
    IsLeast {x | x ⊆ A ∧ (∀ a ∈ x, 1 / (1 - a) ∈ x) ∧ 2 ∈ x} {2, -1, 1 / 2} := by
  constructor
  · -- Show {2, -1, 1/2} is in the collection
    constructor
    · -- Show {2, -1, 1/2} ⊆ A
      intro x hx
      have h3 : x = 2 ∨ x = -1 ∨ x = 1 / 2 := by
        simpa using hx
      rcases h3 with (rfl | rfl | rfl)
      · -- Case x = 2
        exact h2
      · -- Case x = -1
        have h4 : -1 ∈ A := by
          specialize hA 2 h2
          norm_num at hA ⊢
          <;> tauto
        exact h4
      · -- Case x = 1/2
        have h5 : (1/2 : ℝ) ∈ A := by
          have h4 : -1 ∈ A := by
            specialize hA 2 h2
            norm_num at hA ⊢
            <;> tauto
          specialize hA (-1) h4
          norm_num at hA ⊢
          <;> tauto
        exact h5
    constructor
    · -- Show {2, -1, 1/2} is closed under the operation
      intro a ha
      have h3 : a = 2 ∨ a = -1 ∨ a = 1 / 2 := by
        simpa using ha
      rcases h3 with (rfl | rfl | rfl)
      · -- Case a = 2
        norm_num
      · -- Case a = -1
        norm_num
      · -- Case a = 1/2
        norm_num
    · -- Show 2 ∈ {2, -1, 1/2}
      norm_num
  · -- Show {2, -1, 1/2} is the minimum such set
    intro B h
    rcases h with ⟨hB1, hB2, hB3⟩
    intro x hx
    have h1 : x = 2 ∨ x = -1 ∨ x = 1/2 := by
      simpa using hx
    rcases h1 with (rfl | rfl | rfl)
    · -- Case x = 2
      have h4 : 2 ∈ B := hB3
      exact h4
    · -- Case x = -1
      have h4 : -1 ∈ B := by
        have h5 : (2 : ℝ) ∈ B := hB3
        have h6 : 1 / (1 - (2 : ℝ)) ∈ B := hB2 2 h5
        norm_num at h6 ⊢
        all_goals try tauto
      exact h4
    · -- Case x = 1/2
      have h7 : (1/2 : ℝ) ∈ B := by
        have h4 : -1 ∈ B := by
          have h5 : (2 : ℝ) ∈ B := hB3
          have h6 : 1 / (1 - (2 : ℝ)) ∈ B := hB2 2 h5
          norm_num at h6 ⊢
          all_goals try tauto
        have h8 : 1 / (1 - (-1 : ℝ)) ∈ B := hB2 (-1) h4
        norm_num at h8 ⊢
        all_goals try tauto
      exact h7