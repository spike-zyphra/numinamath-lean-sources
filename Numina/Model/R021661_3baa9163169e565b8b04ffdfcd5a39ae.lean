import Mathlib

theorem algebra_71877 (f : ℝ → ℝ) (hf : f = fun x => x^2 + 9 * x^2 / (x + 3)^2 - 40) :
    Set.ncard {x | f x = 0} = 2 := by

  have h1 : {x | f x = 0} = {-2, 6} := by
    ext x
    simp [hf]
    constructor
    · -- Assume f x = 0, prove x ∈ {-2, 6}
      intro h_eq
      by_cases hne : x + 3 = 0
      · -- x + 3 = 0, so x = -3
        have hx : x = -3 := by linarith
        rw [hx] at h_eq
        norm_num at h_eq
      · -- x + 3 ≠ 0
        have h2 : x ≠ -3 := by
          by_contra h
          have : x + 3 = 0 := by linarith
          contradiction
        have h3 : x^2 + 9 * x^2 / (x + 3)^2 - 40 = 0 := h_eq
        have h4 : x^4 + 6 * x^3 - 22 * x^2 - 240 * x - 360 = 0 := by
          have h5 : (x + 3) ≠ 0 := by
            intro h6
            apply hne
            linarith
          have h6 : x^2 + 9 * x^2 / (x + 3) ^ 2 - 40 = 0 := h3
          have h7 : (x^2 + 9 * x^2 / (x + 3) ^ 2 - 40) * (x + 3) ^ 2 = 0 := by
            rw [h6]
            all_goals
            norm_num
          field_simp [(show (x + 3 : ℝ) ≠ 0 by intro h6; apply hne; linarith)] at h7 ⊢
          nlinarith
        have h6 : (x + 2) * (x - 6) * (x^2 + 10 * x + 30) = 0 := by 
          nlinarith [sq_pos_of_ne_zero (show (x + 3 : ℝ) ≠ 0 by intro h6; apply hne; linarith)]
        cases' (mul_eq_zero.mp h6) with h7 h8
        cases' (mul_eq_zero.mp h7) with h8 h9
        · -- Case h8 : x + 2 = 0
          have hx : x = -2 := by linarith
          simp [hx]
        · -- Case h9 : x - 6 = 0
          have hx : x = 6 := by linarith
          simp [hx]
        · -- Case h8 : x^2 + 10 * x + 30 = 0
          have h8 : (x^2 + 10 * x + 30) = 0 := by linarith
          nlinarith [sq_nonneg (x + 5)]
    · -- Assume x ∈ {-2, 6}, prove f x = 0
      rintro (hx | hx)
      · -- Case x = -2
        rw [hx]
        norm_num
      · -- Case x = 6
        rw [hx]
        norm_num
  rw [h1]
  rw [Set.ncard_pair (by norm_num)]