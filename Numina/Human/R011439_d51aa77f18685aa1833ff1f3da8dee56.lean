import Mathlib

/- if x and √(x ^ 2 +24) are both positive instegers,
find the sum of all possible values of x.-/

theorem algebra_633731:
    ∑ᶠ x ∈ {x: ℤ | 0 < x ∧ ∃ m: ℤ, √(x ^ 2 + 24) = m}, x = 6 := by

    -- we directly compute the set
    have h_eq: {x: ℤ | 0 < x ∧ ∃ m: ℤ, √(x ^ 2 + 24) = m} = {5, 1} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor

      -- the forward direction
      .
        intro h
        rcases h with ⟨hx, h⟩
        simp
        obtain ⟨m, h⟩ := h
        have lm: 0 ≤ m := by
          rify
          rw [← h]
          apply Real.sqrt_nonneg
        rw [Real.sqrt_eq_iff_eq_sq] at h
        .
          norm_cast at h
          replace h: (m - x) * (m + x) = 24 := by
            nlinarith
          have d: (m + x).natAbs ∈ Nat.divisors 24 := by
            simp
            zify
            rw [show |m + x| = m + x by apply abs_of_nonneg; linarith]
            rw [← h]
            simp
          rw [show Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} by rfl] at d
          simp at d
          zify at d
          rw [show |m + x| = m + x by apply abs_of_nonneg; linarith] at d
          rcases d with d | d  | d | d | d | d | d | d
          all_goals simp [d] at h; omega
        .
          rify at hx
          nlinarith
        .
          rify at lm
          exact lm


      -- the backward direction
      .
        intro h
        simp at h
        rcases h with h | h
        all_goals simp [h]
        .
          use 7
          rw [Real.sqrt_eq_iff_eq_sq]
          norm_num
          norm_num
          simp
        .
          use 5
          rw [Real.sqrt_eq_iff_eq_sq]
          norm_num
          norm_num
          simp

    -- then we can count the card
    rw [h_eq]
    rw [finsum_mem_eq_toFinset_sum]
    simp