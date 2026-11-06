import Mathlib

noncomputable def J: ℝ → ℝ := fun x => if x ≤ -2 then 4 + x else -x


lemma lemma_1: ∀ x, J x = 0 → x = 0 ∨ x = -4 := by
  intro x h
  simp [J] at h
  by_cases l: x ≤ -2
  .
    simp [l] at h
    right
    linarith
  .
    simp [l] at h
    left
    linarith


lemma lemma_2: ∀ x, J x = -4 → x = -8 ∨ x = 4 := by
  intro x h
  simp [J] at h
  by_cases l: x ≤ -2
  .
    simp [l] at h
    left
    linarith
  .
    simp [l] at h
    right
    linarith


theorem algebra_241734: {x: ℝ | J (J (J x)) = 0}.encard = 6 := by
  have h_eq: {x: ℝ | J (J (J x)) = 0} = {0,4,-4,-8,8,-12} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Show that if J(J(J(x))) = 0, then x is in the set
      intro h
      have h1 : J (J (J x)) = 0 := h
      have h2 : J (J x) = 0 ∨ J (J x) = -4 := by
        have h3 : J (J (J x)) = 0 := h1
        have h4 : J (J x) = 0 ∨ J (J x) = -4 := by
          apply lemma_1 
          exact h3
        tauto
      rcases h2 with (h2 | h2)
      · -- Case where J(J x) = 0 
        have h3 : J x = 0 ∨ J x = -4 := by
          have h3 : J (J x) = 0 := h2
          have h4 : J x = 0 ∨ J x = -4 := by
            apply lemma_1 
            exact h3
          tauto
        rcases h3 with (h3 | h3)
        · -- Case where J x = 0
          have h4 : x = 0 ∨ x = -4 := by
            have h4 : J x = 0 := h3
            have h5 : x = 0 ∨ x = -4 := by
              apply lemma_1 
              exact h4
            tauto
          rcases h4 with (h4 | h4)
          · -- x=0 
            simp [h4]
          · -- x=-4 
            simp [h4]
        · -- Case where J x = -4 
          have h4 : x = -8 ∨ x = 4 := by
            have h4 : J x = -4 := h3
            have h5 : x = -8 ∨ x = 4 := by
              apply lemma_2 
              exact h4
            tauto
          rcases h4 with (h4 | h4)
          · -- x=-8 
            simp [h4]
          · -- x=4 
            simp [h4]
      · -- Case where J(J x) = -4 
        have h3 : J x = -8 ∨ J x = 4 := by
          have h3 : J (J x) = -4 := h2
          have h4 : J x = -8 ∨ J x = 4 := by
            apply lemma_2 
            exact h3
          tauto
        rcases h3 with (h3 | h3)
        · -- Case where J x = -8
          have h4 : x = -12 ∨ x = 8 := by 
            have h4 : J x = -8 := h3
            by_cases l: x ≤ -2 
            · 
              simp [J, l] at h4 
              left
              linarith
            · 
              simp [J, l] at h4 
              right
              linarith
          rcases h4 with (h4 | h4)
          · -- x=-12 
            simp [h4]
          · -- x=8 
            simp [h4]
        · -- Case where J x = 4 
          exfalso 
          have h4 : J x = 4 := h3
          by_cases l: x ≤ -2
          · 
            simp [J, l] at h4 
            all_goals linarith 
          · 
            simp [J, l] at h4 
            all_goals linarith
    · -- Show that if x is in the set, then J(J(J x)) = 0
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x=0 
        norm_num [J]
      · -- x=4 
        norm_num [J]
      · -- x=-4 
        norm_num [J]
      · -- x=-8 
        norm_num [J]
      · -- x=8 
        norm_num [J]
      · -- x=-12 
        norm_num [J]
  rw [h_eq]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals norm_num