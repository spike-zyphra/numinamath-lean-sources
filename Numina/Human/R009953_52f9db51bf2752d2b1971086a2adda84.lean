import Mathlib

/- How many distinct solutions are there to the equation $|x-7| = |x+1|$? -/
theorem algebra_10229 : Set.ncard {(x : ℝ) | |x - 7| = |x + 1|} = 1 := by
  simp

  -- Prove that the set of solutions is equal to the singleton set {3}.
  have h3 : {(x : ℝ) | |x - 7| = |x + 1|} = {3} := by
    -- Use set extensionality to show that two sets are equal if they contain the same elements.
    refine Eq.symm (Set.ext ?h)
    -- Introduce a variable x to work with in the proof.
    intro x
    -- Construct a proof of equivalence between the membership in the original set and the singleton set.
    constructor

    -- Forward direction: Assume x = 3, prove |x - 7| = |x + 1|
    . intro h
      rw [h]
      norm_num

    -- Backward direction: Assume |x - 7| = |x + 1|, prove x = 3
    . intro h
      simp_all

      -- Unfold the definition of equality of absolute values and consider both cases.
      rw [abs_eq] at h
      cases h with
      | inl h₀ => -- Case where x - 7 = x + 1
        rw [eq_comm, abs_eq] at h₀
        swap
        rw [← h₀]
        norm_num

        -- Handle the subcases of the equality x - 7 = -(x + 1).
        cases h₀ with
        | inl h₁ => linarith
        | inr h₁ => linarith

      | inr h₀ => -- Case where x - 7 = -(x + 1)
        -- Show that 7 - x equals the absolute value of x + 1 through calculation.
        have h₁ : 7 - x = |x + 1| := by
          calc
            7 - x = - (x - 7) := by ring
            _ = -(-|x + 1|) := by rw [h₀]
            _ = |x + 1| := by ring
        -- Handle the subcases of the equality 7 - x = |x + 1|.
        rw [eq_comm, abs_eq] at h₁
        swap
        rw [← h₁]
        norm_num

        -- Handle the subcases of the equality 7 - x = -(x + 1).
        cases h₁ with
        | inl h₂ => linarith
        | inr h₂ => linarith

      rw [← h]
      norm_num

  exact ⟨3, h3⟩
