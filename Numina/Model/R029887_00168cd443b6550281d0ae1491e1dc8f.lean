import Mathlib

theorem algebra_324864 :
    IsLeast {m : ℝ | ∃ x y z, x + y + z = 0 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 1 ∧ m = max (max (x ^ 2) (y ^ 2)) (z ^ 2)} (1 / 2) := by
  constructor
  · -- Show 1/2 is in the set
    use 0, Real.sqrt 2 / 2, -Real.sqrt 2 / 2
    constructor
    · -- Check x + y + z = 0
      ring
    constructor
    · -- Check x^2 + y^2 + z^2 = 1
      have h1 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by linarith)
      nlinarith [Real.sqrt_nonneg 2]
    · -- Check m = max (max (x ^ 2) (y ^ 2)) (z ^ 2)
      have h1 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by linarith)
      have h2 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
        calc
          (Real.sqrt 2 / 2 : ℝ) ^ 2 = (Real.sqrt 2 ^ 2) / 4 := by ring
          _ = 2 / 4 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)]
          _ = 1 / 2 := by norm_num
      have h3 : ((-Real.sqrt 2 / 2 : ℝ) ) ^ 2 = 1 / 2 := by
        calc
          ((-Real.sqrt 2 / 2 : ℝ) ) ^ 2 = (Real.sqrt 2 / 2 : ℝ) ^ 2 := by ring
          _ = 1 / 2 := by linarith [h2]
      rw [show max (max (0 ^ 2) ((Real.sqrt 2 / 2) ^ 2)) ((-Real.sqrt 2 / 2) ^ 2) = 1 / 2 by
        rw [show (0 ^ 2 : ℝ) = (0 : ℝ) by norm_num, h2, h3]
        norm_num [max_eq_right, max_eq_left]
      ]
  · -- Show that 1/2 is the minimum
    intro m hm
    rcases hm with ⟨x, y, z, h1, h2, hm⟩
    by_contra h
    push_neg at h
    have h3 : x ^ 2 < 1 / 2 := by
      have h4 : max (max (x ^ 2) (y ^ 2)) (z ^ 2) < 1 / 2 := by linarith [h, hm]
      have h5 : x ^ 2 ≤ max (max (x ^ 2) (y ^ 2)) (z ^ 2) := by
        simp
      linarith
    have h4 : y ^ 2 < 1 / 2 := by
      have h5 : max (max (x ^ 2) (y ^ 2)) (z ^ 2) < 1 / 2 := by linarith [h, hm]
      have h6 : y ^ 2 ≤ max (max (x ^ 2) (y ^ 2)) (z ^ 2) := by
        simp
      linarith
    have h5 : z ^ 2 < 1 / 2 := by
      have h6 : max (max (x ^ 2) (y ^ 2)) (z ^ 2) < 1 / 2 := by linarith [h, hm]
      have h7 : z ^ 2 ≤ max (max (x ^ 2) (y ^ 2)) (z ^ 2) := by
        simp
      linarith
    have h6 : z = - (x + y) := by linarith
    have h7 : x ^ 2 + y ^ 2 + z ^ 2 = 1 := h2
    rw [show z = - (x + y) by linarith] at h7
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - y + 1), sq_nonneg (x + y - 1)]