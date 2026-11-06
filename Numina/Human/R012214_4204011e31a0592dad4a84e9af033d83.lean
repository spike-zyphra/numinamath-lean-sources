import Mathlib

open Real

lemma lemma_1 {x: ℝ}: sin x = 0 ∧ cos x = 1 ∨ sin x = 1 ∧ cos x = 0 ↔
    ∃ n: ℤ, x = 2 * n * π ∨ x = 2 * n * π + π / 2 := by

  constructor
  -- the first direction
  .
    intro h
    rcases h with h | h
    .
      rcases h with ⟨h1, h2⟩
      rw [Real.cos_eq_one_iff] at h2
      obtain ⟨l, hl⟩ := h2
      use l
      left
      rw [← hl]
      ring
    .
      rcases h with ⟨h1, h2⟩
      rw [Real.sin_eq_one_iff] at h1
      obtain ⟨l, hl⟩ := h1
      use l
      right
      rw [← hl]
      ring

  -- the second direction
  .
    intro h
    obtain ⟨n, h⟩ := h
    rcases h with h | h
    .
      left
      have o: cos x = 1 := by
        rw [Real.cos_eq_one_iff]
        use n
        rw [h]
        ring
      simp [o]
      have i:= Real.sin_sq_add_cos_sq x
      simp [o] at i
      exact i
    .
      right
      have o: sin x = 1 := by
        rw [Real.sin_eq_one_iff]
        use n
        rw [h]
        ring
      simp [o]
      have i:= Real.sin_sq_add_cos_sq x
      simp [o] at i
      exact i

/-Determine all solutions of the equation sinx ^ 3 + cosx ^ 3 = 1 -/

theorem algebra_194040: {x: ℝ | sin x ^ 3 + cos x ^ 3 = 1} =
  {x: ℝ | ∃ n: ℤ, x = 2 * n * π ∨ x = 2 * n * π + π / 2} := by

  ext x
  simp only [Set.mem_setOf_eq]

  -- use lemma_1 to simplify the right side
  rw [← lemma_1]
  constructor

  -- the first direction
  .
    intro h
    rw [← Real.sin_sq_add_cos_sq x] at h

    -- then we factorize h
    replace h: sin x ^ 2 * (sin x - 1) = cos x ^ 2 * (1 - cos x) := by
      nlinarith

    -- for convenience, prove by contradiction
    by_contra! l
    rcases l with ⟨l1, l2⟩
    by_cases s: sin x = 1

    -- case sin x = 1
    .
      simp [s] at l2
      simp [s] at h
      simp [l2] at h
      replace h: cos x = 1 := by linarith
      have i:= Real.sin_sq_add_cos_sq x
      simp [s, h] at i

    -- case sin x ≠ 1
    .
      have ls:= Real.sin_le_one x
      have lc:= Real.cos_le_one x
      replace s: sin x < 1 := by
        by_contra! o
        replace o: sin x = 1 := by
          linarith
        simp [o] at s
      by_cases c: sin x = 0
      -- case sin x = 0
      .
        simp [c] at l1
        simp [c] at h
        replace l1: ¬ 1 - cos x = 0 := by
          by_contra! o
          replace o: cos x = 1 := by
            linarith
          simp [o] at l1
        simp [l1] at h
        have i:= Real.sin_sq_add_cos_sq x
        simp [c, h] at i
      -- case sin x ≠ 0
      .
        clear l1 ls

        -- note that left side of h is negative, while right side is positive
        have u: sin x ^ 2 * (sin x - 1) < 0 := by
          have o: 0 < sin x ^ 2 := by
            have v: 0 ≤ sin x ^ 2 := by
              apply sq_nonneg
            by_contra! o
            replace o: sin x ^ 2 = 0 := by
              linarith
            simp at o
            simp [o] at c
          nlinarith
        rw [h] at u
        absurd u
        simp
        nlinarith


  -- the second direction
  .
    intro h
    rcases h with h | h
    .
      simp [h]
    .
      simp [h]