import Mathlib

/-How many integers $n$ satisfy both of the inequalities $4n + 3 < 25$ and $-7n + 5 < 24$?-/
theorem algebra_20443 :
    Set.ncard {n : ℤ | 4 * n + 3 < 25 ∧ -7 * n + 5 < 24} = 8 := by
  -- show that the target is [−2, 5]
  have set_eq : {n : ℤ | 4 * n + 3 < 25 ∧ -7 * n + 5 < 24} = Finset.Icc (-2) 5 := by
    ext n
    simp
    -- divide into two parts
    apply Iff.intro <;> intro h
    -- show that n is in [−2, 5]
    . obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_⟩
      . linarith
      . linarith
    -- show that n satisfies the inequalities
    . refine ⟨?_, ?_⟩
      . linarith
      . linarith
  -- show that the target is 8
  rw [set_eq]
  rw [Set.ncard_coe_Finset]
  norm_num
  norm_cast