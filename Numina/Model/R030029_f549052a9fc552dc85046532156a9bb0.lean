import Mathlib


theorem algebra_231488 :
  {f : ℝ → ℝ | ∀ x y : ℝ, x * (f y) + y * (f x) = (x + y) * (f x) * (f y)} =
  {f : ℝ → ℝ | (∀ x : ℝ, f x = 0) ∨ 
               (∃ c : ℝ, f 0 = c ∧ ∀ x : ℝ, x ≠ 0 → f x = 1)} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume f satisfies the functional equation, prove it is either zero everywhere or the second case
    intro h
    by_cases h1 : ∀ x : ℝ, f x = 0
    · left
      exact h1
    · -- Assume f is not zero everywhere, prove the second case
      right
      have h2 : ∃ x : ℝ, f x ≠ 0 := by 
        by_contra h3
        push_neg at h3
        have h3' : ∀ x : ℝ, f x = 0 := by 
          intro x
          specialize h3 x
          tauto
        contradiction
      rcases h2 with ⟨a, ha⟩
      have h3 : f 1 = 1 := by
        have eq1 := h 1 1
        norm_num at eq1
        have eq2 : f 1 * (f 1 - 1) = 0 := by 
          nlinarith
        cases' (mul_eq_zero.mp eq2) with h4 h5
        · -- f 1 = 0
          have h6 : ∀ x : ℝ, f x = 0 := by
            intro x
            have eq3 := h x 1
            simp [h4] at eq3
            linarith
          have h7 : f a = 0 := h6 a
          contradiction
        · -- f 1 - 1 = 0
          linarith
      have h4 : ∀ x : ℝ, x ≠ 0 → f x = 1 := by
        intro x hx
        have eq1 := h x 1
        simp [h3] at eq1
        have eq2 : x * (f x) = x := by
          linarith
        have eq3 : f x = 1 := by
          apply (mul_left_inj' hx).mp
          linarith
        linarith
      have h5 : ∃ c : ℝ, f 0 = c ∧ ∀ x : ℝ, x ≠ 0 → f x = 1 := by
        refine ⟨f 0, rfl, h4⟩
      exact h5
  · -- Assume f is either zero everywhere or the second case, prove it satisfies the functional equation
    rintro (h1 | ⟨c, hc1, hc2⟩)
    · -- Case where f is zero everywhere
      intro x y
      simp [h1]
    · -- Case where f is 1 at all non-zero points
      intro x y
      by_cases h9 : x = 0
      · -- x = 0
        rw [h9]
        by_cases h10 : y = 0
        · -- y = 0
          rw [h10]
          simp [hc1]
        · -- y ≠ 0
          have h11 : f y = 1 := hc2 y (by
            intro h
            apply h10
            linarith
          )
          simp [hc1, h11]
      · -- x ≠ 0
        by_cases h10 : y = 0
        · -- y = 0
          rw [h10]
          have h11 : f x = 1 := hc2 x (by
            intro h
            apply h9
            linarith
          )
          simp [hc1, h11]
        · -- y ≠ 0
          have h11 : f x = 1 := hc2 x (by 
            intro h
            apply h9
            linarith
          )
          have h12 : f y = 1 := hc2 y (by 
            intro h
            apply h10
            linarith
          )
          simp [h11, h12]
          all_goals
            nlinarith