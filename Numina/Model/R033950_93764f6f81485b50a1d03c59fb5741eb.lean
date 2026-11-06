import Mathlib

theorem algebra_290903 (a : ℕ → ℝ) (h₀ : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (h₁ : a 2 = Real.sqrt 2) (h₂ : a 3 = 3 ^ ((1 : ℝ) / 3)) :
    (a 1 + a 2011) / (a 7 + a 2017) = 8 / 9 := by
  rcases h₀ with ⟨r, hr⟩
  have ha2 : a 2 = a 0 * r ^ 2 := hr 2
  have ha3 : a 3 = a 0 * r ^ 3 := hr 3
  rw [ha2] at h₁
  rw [ha3] at h₂
  have ha0_ne_zero : a 0 ≠ 0 := by
    by_contra h
    rw [h] at h₁
    have h11 : Real.sqrt 2 = 0 := by
      nlinarith
    have h111 : Real.sqrt 2 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    nlinarith
  have hr_eq : r = (3 ^ ((1 : ℝ) / 3)) / Real.sqrt 2 := by
    have h3 : a 0 * r ^ 3 = 3 ^ ((1 : ℝ) / 3) := by
      linarith
    have h4 : a 0 * r ^ 2 = Real.sqrt 2 := by
      linarith
    have h5 : r = (3 ^ ((1 : ℝ) / 3)) / Real.sqrt 2 := by
      have h6 : a 0 * r ^ 3 = (a 0 * r ^ 2) * r := by ring
      rw [h6] at h3
      rw [h4] at h3
      have h7 : Real.sqrt 2 ≠ 0 := by
        have h111 : Real.sqrt 2 > 0 := by
          apply Real.sqrt_pos.mpr
          all_goals norm_num
        linarith
      field_simp at h3 ⊢
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    exact h5
  have ha1 : a 1 = a 0 * r ^ 1 := hr 1
  have ha7 : a 7 = a 0 * r ^ 7 := hr 7
  have ha2011 : a 2011 = a 0 * r ^ 2011 := hr 2011
  have ha2017 : a 2017 = a 0 * r ^ 2017 := hr 2017
  have eq1 : a 1 + a 2011 = a 0 * r * (1 + r ^ 2010) := by
    rw [ha1, ha2011]
    ring_nf
  have eq2 : a 7 + a 2017 = a 0 * r ^ 7 * (1 + r ^ 2010) := by
    rw [ha7, ha2017]
    ring_nf
  rw [eq1, eq2]
  have ha0_ne_zero' : a 0 ≠ 0 := ha0_ne_zero
  have hr_ne_zero : r ≠ 0 := by
    by_contra h
    rw [h] at h₁
    have h11 : Real.sqrt 2 = 0 := by
      nlinarith [ha0_ne_zero]
    have h111 : Real.sqrt 2 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    nlinarith
  have h10 : 1 + r ^ 2010 ≠ 0 := by
    have h11 : r ^ 2010 > 0 := by
      positivity
    have h12 : 1 + r ^ 2010 > 0 := by
      linarith
    linarith
  have h4 : r ^ 6 > 0 := by positivity
  have h5 : (a 0 * r * (1 + r ^ 2010)) / (a 0 * r ^ 7 * (1 + r ^ 2010)) = 1 / (r ^ 6) := by
    have h9 : a 0 ≠ 0 := ha0_ne_zero
    have h10' : 1 + r ^ 2010 ≠ 0 := h10
    have h14 : r ≠ 0 := hr_ne_zero
    field_simp [h9, h14, h10']
    all_goals ring
  rw [h5]
  have hr6 : r ^ 6 = 9 / 8 := by
    have hr_eq' : r = (3 ^ ((1 : ℝ) / 3)) / Real.sqrt 2 := hr_eq
    rw [hr_eq']
    have h7 : ((3 ^ ((1 : ℝ) / 3)) / Real.sqrt 2) ^ 6 = (9 / 8 : ℝ) := by
      calc
        ((3 ^ ((1 : ℝ) / 3)) / Real.sqrt 2) ^ 6 = (3 ^ ((1 : ℝ) / 3)) ^ 6 / (Real.sqrt 2) ^ 6 := by
          field_simp
        _ = (9 : ℝ) / (8 : ℝ) := by
          have h8 : (3 ^ ((1 : ℝ) / 3)) ^ 6 = (9 : ℝ) := by
            have h33 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = (3 : ℝ) ^ (2 : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              norm_num
              all_goals linarith
            have h34 : (3 : ℝ) ^ (2 : ℝ) = (9 : ℝ) := by
              norm_num
            linarith [h33, h34]
          have h9 : (Real.sqrt 2 : ℝ) ^ 6 = (8 : ℝ) := by
            calc
              (Real.sqrt 2 : ℝ) ^ 6 = ((Real.sqrt 2 : ℝ) ^ 2) ^ 3 := by ring
              _ = (2 : ℝ) ^ 3 := by rw [Real.sq_sqrt]; positivity
              _ = (8 : ℝ) := by norm_num
          rw [h8, h9]
          all_goals norm_num
    linarith
  rw [hr6]
  all_goals norm_num