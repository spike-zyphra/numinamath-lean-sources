import Mathlib

theorem algebra_4967 :
  IsLeast {c : ℝ | ∃ a b, c = a * b ∧ a^2 + b^2 = 15 ∧ a^4 + b^4 = 153} (-6) := by 
  constructor
  · -- Let's find specific values of a and b such that a * b = -6, a^2 + b^2 = 15, and a^4 + b^4 = 153 
    use 2 * Real.sqrt 3, -Real.sqrt 3
    constructor
    · -- Verify that (2 * √3) * (-√3) = -6
      have h1 : (2 * Real.sqrt 3) * (-Real.sqrt 3) = -6 := by
        calc
          (2 * Real.sqrt 3) * (-Real.sqrt 3) = -2 * (Real.sqrt 3 * Real.sqrt 3) := by ring
          _ = -2 * (Real.sqrt 3 ^ 2) := by ring
          _ = -2 * 3 := by rw [Real.sq_sqrt (by norm_num)]
          _ = -6 := by norm_num
      linarith [h1]
    constructor
    · -- Verify that (2 * √3) ^ 2 + (-√3) ^ 2 = 15
      have h21 : (2 * Real.sqrt 3) ^ 2 + (-Real.sqrt 3) ^ 2 = 15 := by
        have h21_a : (2 * Real.sqrt 3) ^ 2 = 12 := by
          calc
            (2 * Real.sqrt 3) ^ 2 = 4 * (Real.sqrt 3 ^ 2) := by ring
            _ = 4 * 3 := by rw [Real.sq_sqrt (by norm_num)]
            _ = 12 := by norm_num
        have h21_b : (-Real.sqrt 3) ^ 2 = 3 := by
          rw [neg_sq, Real.sq_sqrt (by norm_num)]
        linarith [h21_a, h21_b]
      linarith [h21]
    · -- Verify that (2 * √3) ^ 4 + (-√3) ^ 4 = 153
      have h31 : (2 * Real.sqrt 3) ^ 4 + (-Real.sqrt 3) ^ 4 = 153 := by
        have h4_a : (2 * Real.sqrt 3) ^ 4 = 144 := by
          calc 
            (2 * Real.sqrt 3) ^ 4 = ((2 * Real.sqrt 3) ^ 2) ^ 2 := by ring
            _ = (12) ^ 2 := by 
              have : (2 * Real.sqrt 3) ^ 2 = 12 := by 
                calc
                  (2 * Real.sqrt 3) ^ 2 = 4 * (Real.sqrt 3 ^ 2) := by ring
                  _ = 4 * 3 := by rw [Real.sq_sqrt (by norm_num)]
                  _ = 12 := by norm_num
              rw [this]
            _ = 144 := by norm_num
        have h4_b : (-Real.sqrt 3) ^ 4 = 9 := by
          calc 
            (-Real.sqrt 3) ^ 4 = (Real.sqrt 3 ^ 4 : ℝ) := by ring 
            _ = (Real.sqrt 3 ^ 2) ^ 2 := by ring 
            _ = (3) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]
            _ = 9 := by norm_num
        linarith [h4_a, h4_b]
      linarith [h31]
  · -- Show that -6 is indeed the least value
    intro c hc
    rcases hc with ⟨a, b, h1, h2, h3⟩
    have h4 : (a^2 + b^2)^2 = a^4 + b^4 + 2 * (a * b)^2 := by
      ring
    rw [show a^2 + b^2 = (15 : ℝ) by linarith] at h4
    rw [show a^4 + b^4 = (153 : ℝ) by linarith] at h4
    have h5 : (a * b) ^ 2 = 36 := by
      nlinarith
    nlinarith [sq_nonneg (a * b), sq_nonneg (a * b - 6), sq_nonneg (a * b + 6)]