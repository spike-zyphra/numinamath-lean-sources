import Mathlib

theorem algebra_5420 : 
    {s : ℝ | ∃ z : ℂ, (s : ℂ) = Complex.abs z ∧ s^2002 = s} = {0, 1} := by
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Introduce hypothesis: ∃ z : ℂ, (s : ℂ) = Complex.abs z ∧ s^2002 = s
    rintro ⟨z, hs, heq⟩
    have h1 : s ≥ 0 := by
      have h2 : (s : ℝ) = Complex.abs z := by
        exact_mod_cast hs
      have h3 : Complex.abs z ≥ 0 := by
        simp [Complex.abs]
        <;> positivity
      linarith [h2, h3]
    have h2 : s ^ 2002 = s := by
      simpa using heq
    have h3 : s * (s ^ 2001 - 1) = 0 := by
      ring_nf at h2 ⊢
      linarith
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case where h4 is true, i.e., s = 0
      have hs0 : s = 0 := by
        linarith
      left
      simp [hs0]
    · -- Case where h5 is true, i.e., s^2001 - 1 = 0
      have h4 : s ^ 2001 = 1 := by
        linarith
      have h6 : s = 1 := by
        have h10 : s ≥ 0 := h1
        have h11 : s ^ 2001 = 1 := h4
        have h7 : s ≤ 1 := by
          by_contra h
          push_neg at h
          have h8 : s > 1 := by
            linarith
          have h9 : s ^ 2001 > 1 := by
            have h10 : s > 1 := h8
            have h11 : s ^ 2001 > (1 : ℝ) ^ 2001 := by
              apply pow_lt_pow_left
              all_goals
                linarith
            have h12 : (1 : ℝ) ^ 2001 = 1 := by
              norm_num
            linarith
          nlinarith
        have h8 : s ≥ 1 := by
          by_contra h
          push_neg at h
          have h9 : s < 1 := by
            linarith
          have h10 : s ^ 2001 < 1 := by
            have h11 : s ≥ 0 := h1
            have h12 : s < (1 : ℝ) := by
              linarith
            have h13 : s ^ 2001 < (1 : ℝ) ^ 2001 := by
              apply pow_lt_pow_left
              all_goals
                linarith
            have h14 : (1 : ℝ) ^ 2001 = 1 := by
              norm_num
            linarith
          nlinarith
        have h12 : s = 1 := by
          linarith
        linarith
      right
      simp [h6]
  · -- Show the reverse direction: 0 and 1 satisfy the equation
    rintro (rfl | rfl)
    · -- Show s = 0 is in the set
      use (0 : ℂ)
      simp
      all_goals
        norm_num
    · -- Show s = 1 is in the set
      use (1 : ℂ)
      simp [Complex.abs, Complex.normSq]
      all_goals
        norm_num