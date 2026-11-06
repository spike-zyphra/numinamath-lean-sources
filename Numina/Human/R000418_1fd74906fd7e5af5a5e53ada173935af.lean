import Mathlib

/- The square root of $x$ is greater than 2 and less than 4. How many integer values of $x$ satisfy this condition? -/
theorem algebra_10441 :
    Set.ncard {x : ℤ | (x : ℝ) ≥ 0 ∧ 2 < √x ∧ √x < 4} = 11 := by
  -- We simplify the set to {x : ℤ | 4 < x < 16}
  have H : {x : ℤ | (x : ℝ) ≥ 0 ∧ 2 < √x ∧ √x < 4} = {x : ℤ | 4 < x ∧ x < 16} := by
    -- Mutual inclusion
    ext x
    constructor

    all_goals
      simp
      -- Rewrite the inequality about square roots
      rw [Real.lt_sqrt (by norm_num)]
      rw [Real.sqrt_lt' (by norm_num)]
      -- Simplify
      norm_num
      norm_cast
    -- Trivial logic
    . intro _ h2 h3
      exact ⟨h2, h3⟩
    . intro h1 h2
      exact ⟨by linarith, h1, h2⟩

  -- Use the lemma
  rw [H]
  -- Use the finset version of the set
  rw [show {x : ℤ | 4 < x ∧ x < 16} = Finset.Ioo (4 : ℤ) 16 by simp [Set.Ioo]]
  rw [Set.ncard_coe_Finset]
  simp
