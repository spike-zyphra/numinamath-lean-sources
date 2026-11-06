import Mathlib

/- How many unique values can be created by forming the fraction $\frac{x}{y}$ where $x$ is either 4, 8, or 12 and $y$ is either 4, 8, or 12? -/
theorem algebra_19713 : Set.ncard {x : ℚ | ∃ a b, x = a / b ∧ (a = 4 ∨ a = 8 ∨ a = 12) ∧ (b = 4 ∨ b = 8 ∨ b = 12)} = 7 := by
  have h₀ : {x : ℚ | ∃ a b, x = a / b ∧ (a = 4 ∨ a = 8 ∨ a = 12) ∧ (b = 4 ∨ b = 8 ∨ b = 12)} = {1 / 3, 1 / 2, 2 / 3, 1, 3 / 2, 2, 3} := by
    ext x
    -- Simplify the goal into two parts.
    simp [-one_div]
    apply Iff.intro <;> intro h
    . obtain ⟨a, b, h₀, h₁ | h₁ | h₁, h₂ | h₂ | h₂⟩ := h
      all_goals
        rw [h₀, h₁, h₂]
        norm_num
    . obtain h | h | h | h | h | h | h := h
      . use 4
        use 12
        norm_num
        exact h
      . use 4
        use 8
        norm_num
        exact h
      . use 8
        use 12
        norm_num
        exact h
      . use 4
        use 4
        norm_num
        exact h
      . use 12
        use 8
        norm_num
        exact h
      . use 8
        use 4
        norm_num
        exact h
      . use 12
        use 4
        norm_num
        exact h
  rw [h₀]
  -- Show that {1 / 3, 1 / 2, 2 / 3, 1, 3 / 2, 2, 3} has cardinality 7.
  rw [show ({1 / 3, 1 / 2, 2 / 3, 1, 3 / 2, 2, 3} : Set ℚ) = ({1 / 3, 1 / 2, 2 / 3, 1, 3 / 2, 2, 3} : Finset ℚ) by simp]
  rw [Set.ncard_coe_Finset]
  repeat
    rw [Finset.card_insert_of_not_mem]
  all_goals
    norm_num
