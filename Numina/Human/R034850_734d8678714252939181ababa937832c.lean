import Mathlib

/- Ten numbers are written around a circle, the sum of which is 100. It is known that the sum of any three consecutive numbers is not less than 29.

Indicate the smallest number $A$ such that in any such set of numbers, each number does not exceed $A$. -/
theorem inequalities_191591  : IsLeast {x | ∀ a : Fin 10 → ℝ, (∑ i, a i = 100)
    ∧ (∀ i, a i + a (i + 1) + a (i + 2) ≥ 29) → (∀ i, a i ≤ x)} 13 := by

  -- It is convenient to write the sum explicitly
  have (a : Fin 10 → ℝ) : ∑ i, a i = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 + a 9 := by
        rw [Finset.sum_fin_eq_sum_range]; repeat rw [Finset.sum_range_succ]; simp

  constructor
  -- We need to show that all numbers must be at most 13
  · rw [Set.mem_setOf_eq]
    intro a ⟨hsum, h3⟩ i
    -- We collect the sum to have a i plus three groups of three consecutive numbers
    have cycle : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 + a 9
      = a i + (a (i+1) + a (i+1+1) + a (i+1+2)) + (a (i+4) + a (i+4+1) + a (i+4+2)) + (a (i+7) + a (i+7+1) + a (i+7+2)) := by
      fin_cases i <;> dsimp
      all_goals ring
    rw [this a, cycle] at hsum -- The whole sum is 100
    have hi1 := h3 (i+1) -- First block is at least 29
    have hi4 := h3 (i+4) -- Second block is at least 29
    have hi7 := h3 (i+7) -- Third block is at least 29
    linarith -- So a i must be at least 100 - 3*29 = 13
  -- Now we exhibit a set of numbers that satisfies the conditions and has a maximum of 13
  · intro x hx
    rw [Set.mem_setOf_eq] at hx
    let a : Fin 10 → ℝ := fun i => match i with
      | 0 => 13
      | 1 => 9
      | 2 => 10
      | 3 => 10
      | 4 => 9
      | 5 => 10
      | 6 => 10
      | 7 => 9
      | 8 => 10
      | 9 => 10
    -- The sum is 100
    have hsum : ∑ i, a i = 100 := by rw [this]; norm_num
    -- The sum of any three consecutive numbers is at least 29
    have h3 : ∀ i, a i + a (i + 1) + a (i + 2) ≥ 29 := by
      intro i
      fin_cases i <;> dsimp
      all_goals norm_num
    -- a 0 is 13, and the thesis follows
    exact (hx a) ⟨hsum, h3⟩ 0