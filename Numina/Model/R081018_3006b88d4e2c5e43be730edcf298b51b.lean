import Mathlib

theorem algebra_241947 (x : ℝ) :
    (x - 1009)^3 + (2 * x - 1009)^3 + (2018 - 3 * x)^3 = 0 ↔
    x = 1009 ∨ x = 1009 / 2 ∨ x = 2018 / 3 := by
  constructor
  · -- Assume (x - 1009)^3 + (2 * x - 1009)^3 + (2018 - 3 * x)^3 = 0 prove x = 1009 ∨ x = 1009 / 2 ∨ x = 2018 / 3
    intro h
    -- First establish that the sum of the terms equals 0
    have h1 : (x - 1009) + (2 * x - 1009) + (2018 - 3 * x) = 0 := by
      linarith
    -- Then prove an equation identity: if a + b + c = 0, then a^3 + b^3 + c^3 = 3abc
    have eq1 : (x - 1009) * (2 * x - 1009) * (2018 - 3 * x) = 0 := by
      have h2 : (x - 1009)^3 + (2 * x - 1009)^3 + (2018 - 3 * x)^3 = 3 * ((x - 1009) * (2 * x - 1009) * (2018 - 3 * x)) := by
        -- Apply the identity since we know h1 that a + b + c = 0
        have h3 : (x - 1009) + (2 * x - 1009) + (2018 - 3 * x) = 0 := by linarith
        have h4 : (x - 1009)^3 + (2 * x - 1009)^3 + (2018 - 3 * x)^3 - 3 * ((x - 1009) * (2 * x - 1009) * (2018 - 3 * x)) = ((x - 1009) + (2 * x - 1009) + (2018 - 3 * x)) * ((x - 1009)^2 + (2 * x - 1009)^2 + (2018 - 3 * x)^2 - ((x - 1009) * (2 * x - 1009) + (2 * x - 1009) * (2018 - 3 * x) + (2018 - 3 * x) * (x - 1009)))
          := by ring
        rw [h3] at h4
        linarith
      -- Use h2 with the hypothesis to rewrite
      rw [h] at h2
      -- Therefore 0 = 3abc
      linarith
    -- With eq1: (x - 1009) * (2 * x - 1009) * (2018 - 3 * x) = 0, apply the zero product property.
    cases' (mul_eq_zero.mp eq1) with h2 h3
    cases' (mul_eq_zero.mp h2) with h4 h5
    · -- Case $x - 1009 = 0$
      left
      linarith
    · -- Case $2x - 1009 = 0$
      right
      left
      linarith
    · -- Case $2018 - 3x = 0$
      right
      right
      linarith
  · -- Assume x = 1009 ∨ x = 1009/2 ∨ x = 2018/3 prove (x - 1009)^3 + (2 * x - 1009)^3 + (2018 - 3 * x)^3 = 0
    rintro (hx | hx | hx)
    · -- Case x = 1009
      rw [hx]
      norm_num
    · -- Case x = 1009/2
      rw [hx]
      norm_num
    · -- Case x = 2018/3
      rw [hx]
      norm_num