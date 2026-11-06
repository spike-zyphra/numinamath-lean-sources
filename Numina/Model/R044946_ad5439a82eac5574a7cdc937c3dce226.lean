import Mathlib

theorem algebra_305833 (m : ℤ) :
    (∃ x : ℤ, m * x ^ 2 - (m - 2) * x + m - 3 = 0) ↔ m = 1 ∨ m = 3 := by
  constructor
  · -- Assume there's an integer solution x, prove m = 1 ∨ m = 3
    rintro ⟨x, heq⟩
    have h1 : m * x ^ 2 - (m - 2) * x + m - 3 = 0 := heq
    -- Rearrangement: m(x^2 -x +1) =3 -2x
    have h2 : m * (x ^ 2 - x + 1) = 3 - 2 * x := by
      linarith

    have h3 : x ≤ 3 := by
      by_contra h
      push_neg at h

      have h4 : x ^ 2 - x + 1 > 0 := by
        nlinarith

      have h7 : 3 - 2 * x < 0 := by
        nlinarith

      have h8 : m < 0 := by
        nlinarith [h7, h2, h4]

      nlinarith [sq_nonneg (x - 1), sq_nonneg (m + 1), sq_nonneg (x - 2), sq_nonneg (x + 1)]

    have h4 : x ≥ -3 := by
      by_contra h
      push_neg at h

      have h5 : x ^ 2 - x + 1 > 0 := by
        nlinarith

      have h7 : 3 - 2 * x > 0 := by
        nlinarith

      have h8 : m > 0 := by
        nlinarith [h7, h2, h5]

      nlinarith [sq_nonneg (x + 1), sq_nonneg (m - 1), sq_nonneg (x + 2), sq_nonneg (x - 1)]

    interval_cases x <;> omega

  · -- Assume m = 1 ∨ m = 3, prove there's an integer solution x
    rintro (h | h)
    · -- Case m = 1
      have hm : m = 1 := h
      use 1
      rw [hm]
      all_goals norm_num

    · -- Case m = 3
      have hm : m = 3 := h
      use 0
      rw [hm]
      all_goals norm_num