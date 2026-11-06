import Mathlib

noncomputable def J: ℝ → ℝ := fun x => if x ≤ -2 then 4 + x else -x

-- we write the solution of J x = 0 as a lemma
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

-- write the solution of J x = -4 as a lemma
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

/- The function J is defined by
J x = 4 + x for x ≤ -2
J x = - x for -2 ≤ x
How many distinct real solutions has the equation J (J (J x)) = 0 ? -/

theorem algebra_241734: {x: ℝ | J (J (J x)) = 0}.encard = 6 := by

  -- we directly compute all solutions
  have h_eq: {x: ℝ | J (J (J x)) = 0} = {0, 4, -4, -8, 8, -12} := by
    ext x
    constructor

    -- the forward direction
    .
      intro h
      simp at h
      simp

      -- then we apply the lemma_1 to J (J x)
      replace h: J (J x) = 0 ∨ J (J x) = -4 := lemma_1 (J (J x)) h
      rcases h with h | h

      -- case 1: J (J x) = 0
      .
        -- apply lemma 1 again
        replace h: J x = 0 ∨ J x = -4 := lemma_1 (J x) h
        rcases h with h | h

        -- case 1.1: J x = 0
        .
          -- apply lemma 1 again
          replace h: x = 0 ∨ x = -4 := lemma_1 x h
          rcases h with h | h
          all_goals simp [h]

        -- case 1.2: J x = -4
        .
          have i:= lemma_2 x h -- apply lemma 2
          rcases i with i | i
          .
            simp [i]
          .
            simp [i]

      -- case 2: J (J x) = -4
      .
        have i:= lemma_2 (J x) h -- apply lemma 2
        rcases i with i | i

        -- case 2.1: J x = -8
        .
          clear h
          by_cases l: x ≤ -2
          .
            simp [l, J] at i
            replace i: x = -12 := by linarith
            simp [i]
          .
            simp [l, J] at i
            replace i: x = 8 := by linarith
            simp [i]

        -- case 2.2: J x = 4
        .
          clear h
          by_cases l: x ≤ -2
          .
            simp [l, J] at i
            replace i: x = -8 := by linarith
            simp [i]
          .
            simp [l, J] at i
            replace i: x = 4 := by linarith
            simp [i]


    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h | h | h | h | h
      all_goals simp [h, J]; norm_num

  -- then we can count the number of solutions
  rw [h_eq]
  repeat rw [Set.encard_insert_of_not_mem]
  norm_num
  simp
  norm_num
  simp
  norm_num
  simp
  norm_num
  simp
  norm_num
  simp
