import Mathlib

theorem algebra_56369 (x y a : ℝ) (hxy : x + y = a) (h1 : x ^ 3 + y ^ 3 = a) (h2 : x ^ 5 + y ^ 5 = a) :
    a = -2 ∨ a = -1 ∨ a = 0 ∨ a = 1 ∨ a = 2 := by

  have eq1 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * x * y * (x + y) := by 
    ring
  rw [eq1] at h1 
  rw [hxy] at h1
  have eq2 : a * (a ^ 2 - 1 - 3 * x * y) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq2) with ha1 ha2
  · -- Case a = 0
    have ha0 : a = 0 := by 
      linarith 
    simp [ha0]
  · -- Case a^2 - 1 - 3 * x * y = 0 
    -- Now we need to use h2: x^5 + y^5 = a
    have eq3 : 3 * x * y = a^2 - 1 := by
      linarith 
    have eq4 : x * y = (a^2 - 1) / 3 := by 
      linarith 
    have eq8 : x^5 + y^5 = (x + y)^5 - 5 * (x * y) * (x + y)^3 + 5 * (x * y)^2 * (x + y) := by
      ring 
    rw [eq8, hxy, eq4] at h2 
    have eq9 : a * (a^2 - 1) * (a^2 - 4) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp eq9) with eq10 eq11
    cases' (mul_eq_zero.mp eq10) with eq12 eq13 
    · -- Case a = 0 
      have ha0 : a = 0 := by 
        linarith 
      simp [ha0]
    · -- Case a^2 - 1 = 0 
      -- Now, we deduce values of a
      have eq14 : a^2 - 1 = 0 := by 
        nlinarith 
      have eq15 : a^2 = 1 := by 
        linarith 
      have eq16 : a = 1 ∨ a = -1 := by 
        rw [sq_eq_one_iff] at eq15 
        tauto 
      cases' eq16 with eq17 eq18
      · -- Case a = 1 
        have : a = 1 := by 
          linarith 
        simp [this]
      · -- Case a = -1 
        have : a = -1 := by 
          linarith 
        simp [this]
    · -- Case a^2 - 4 = 0 
      -- Now, we deduce values of a
      have eq18 : a^2 - 4 = 0 := by 
        nlinarith 
      have eq19 : a^2 = 4 := by 
        linarith 
      have eq20 : a = 2 ∨ a = -2 := by 
        have h4 : a^2 = 4 := eq19 
        have : a = 2 ∨ a = -2 := by 
          apply eq_or_eq_neg_of_sq_eq_sq 
          norm_num 
          linarith 
        assumption 
      cases' eq20 with eq21 eq22 
      · -- Case a = 2 
        have : a = 2 := by 
          linarith 
        simp [this]
      · -- Case a = -2 
        have : a = -2 := by 
          linarith 
        simp [this]