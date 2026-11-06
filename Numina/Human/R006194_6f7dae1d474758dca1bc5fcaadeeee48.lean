import Mathlib

open Real

/-Given α∈R, if the set sinα,cos2α=cosα,sin2α,
then the set of all angles α that satisfy the condition is-/

theorem algebra_633379:
  {a: ℝ | sin a = cos a ∧ cos (2 * a) = sin (2 * a) ∨ sin a = sin (2 * a) ∧ cos (2 * a) = cos a}
    = {a: ℝ | ∃ k: ℤ, a = 2 * k * π} := by

  ext a
  constructor

  -- the first direction
  .
    intro h
    simp at h
    simp
    rcases h with h | h
    .
    -- show contradiction
      rcases h with ⟨h1, h2⟩
      rw [Real.cos_two_mul] at h2
      rw [Real.sin_two_mul] at h2
      set x:= sin a
      rw [← h1] at h2
      nlinarith
    .
    -- give the solution
      rcases h with ⟨h1, h2⟩
      rw [Real.cos_two_mul] at h2
      rw [Real.sin_two_mul] at h1
      replace h1: sin a * (2 * cos a - 1) = 0 := by
        nlinarith
      simp at h1
      rcases h1 with h1 | h1
      .
        rw [Real.sin_eq_zero_iff] at h1
        obtain ⟨n, h1⟩ := h1

        -- then we show that n is even
        have u: Even n := by
          by_contra! u
          simp at u
          apply Odd.exists_bit1 at u
          obtain ⟨s, u⟩ := u
          simp [u] at h1
          have o: cos a = -1 := by
            rw [Real.cos_eq_neg_one_iff]
            use s
            rw [← h1]
            ring
          simp [o] at h2
        rw [even_iff_exists_two_mul] at u
        obtain ⟨k, u⟩ := u
        use k
        simp [u] at h1
        rw [← h1]
      .
        set p:= cos a
        nlinarith

  -- the second direction
  .
    intro h
    simp at h
    obtain ⟨k, h⟩ := h
    simp only [Set.mem_setOf_eq]
    right
    constructor
    .
      have o1: sin a = 0 := by
        rw [Real.sin_eq_zero_iff]
        use 2 * k
        rw [h]
        simp
      have o2: sin (2 * a) = 0 := by
        rw [Real.sin_two_mul]
        simp [o1]
      simp [o1, o2]
    .
      have o1: cos a = 1 := by
        rw [Real.cos_eq_one_iff]
        use k
        rw [h]
        ring
      rw [Real.cos_two_mul]
      simp [o1]
      norm_num