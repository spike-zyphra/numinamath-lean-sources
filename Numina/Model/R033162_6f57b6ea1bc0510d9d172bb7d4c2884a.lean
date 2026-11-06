import Mathlib

theorem algebra_201059 (f g : ℝ → ℝ) (t : ℝ) (hf : f = fun x => t * x ^ 2 - x + 1)
    (hg : g = fun x => 2 * t * x - 1) :
    Set.ncard {x | f x = g x} = 1 ∨ Set.ncard {x | f x = g x} = 2 := by
  have h1 : {x | f x = g x} = {x | t * x ^ 2 - (1 + 2 * t) * x + 2 = 0} := by
    ext x
    simp [hf, hg]
    constructor
    · intro h
      linarith
    · intro h
      linarith

  rw [h1]

  by_cases ht : t = 0
  · -- When t = 0, the equation becomes -x + 2 = 0, so x = 2.
    rw [ht]
    have h4 : {x | (0 : ℝ) * x ^ 2 - (1 + 2 * (0 : ℝ)) * x + 2 = 0} = {2} := by
      ext x
      simp
      all_goals
        constructor
        · intro h
          linarith
        · intro h
          rw [h]
          norm_num
    rw [h4]
    left
    simp

  · -- When t ≠ 0.
    have h3 : {x | t * x ^ 2 - (1 + 2 * t) * x + 2 = 0} = {1 / t, 2} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · -- Assume t x^2 - (1 + 2t)x + 2 = 0, prove x = 1/t or x = 2.
        intro h
        have h4 : t * x^2 - (1 + 2 * t) * x + 2 = 0 := by
          nlinarith
        -- Factor the quadratic.
        have h3 : (t * x - 1) * (x - 2) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 h3) with h2 h1
        · -- Assume t x - 1 = 0, prove x = 1/t.
          have h4 : t * x = 1 := by linarith
          have h5 : x = 1 / t := by
            have ht2 : t ≠ 0 := by
              intro h0
              apply ht
              all_goals
                linarith
            field_simp [ht2]
            all_goals
              nlinarith
          left
          exact h5
        · -- Assume x - 2 = 0, prove x = 2.
          right
          linarith
      · -- Assume x = 1/t or x = 2, prove t x^2 - (1 + 2t)x + 2 = 0.
        rintro (h | h)
        · -- Case x = 1/t.
          rw [h]
          have ht2 : t ≠ 0 := by
            intro h0
            apply ht
            all_goals
              linarith
          field_simp [ht2]
          all_goals
            nlinarith
        · -- Case x = 2.
          rw [h]
          nlinarith
    rw [h3]

    have h7 : (1 / t = (2 : ℝ)) ↔ t = 1/2 := by
      constructor
      · -- If 1/t = 2, then t = 1/2.
        intro h
        have ht2 : t ≠ 0 := by
          by_contra h0
          rw [h0] at h
          norm_num at h
        field_simp [ht2] at h
        linarith
      · -- If t = 1/2, then 1/t = 2.
        intro h
        rw [h]
        norm_num

    by_cases ht4 : 1 / t = (2 : ℝ)
    · -- If 1/t = 2, then {1/t, 2} = {2}, which has cardinality 1.
      have ht3 : t = 1/2 := by
        apply h7.1
        exact ht4
      have ht5 : (Set.ncard ({1 / t, 2} : Set ℝ) = 1) := by
        have ht8 : (1 / t : ℝ) = (2 : ℝ) := by exact ht4
        rw [ht8]
        simp
      left
      exact ht5
    · -- If 1/t ≠ 2, then the set {1/t, 2} has cardinality 2.
      have ht7 : (1 / t : ℝ) ≠ (2 : ℝ) := by
        intro h
        apply ht4
        all_goals
          tauto
      have ht6 : (Set.ncard ({1 / t, 2} : Set ℝ) = 2) := by
        have ht11 : (1 / t : ℝ) ≠ (2 : ℝ) := ht7
        rw [Set.ncard_pair]
        all_goals
          try { tauto }
      right
      exact ht6