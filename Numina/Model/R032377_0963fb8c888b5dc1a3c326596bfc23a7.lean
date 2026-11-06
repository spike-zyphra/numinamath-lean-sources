import Mathlib

theorem algebra_255914 :
  { x : ℝ | x * (x + 2) * (x + 3) * (x + 5) + 8 = 0 } =
  { (Real.sqrt 17 - 5) / 2, (-Real.sqrt 17 - 5) / 2, -1, -4 } := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume x * (x + 2) * (x + 3) * (x + 5) + 8 = 0, prove x in right-hand side set
    intro h
    have h1 : x * (x + 2) * (x + 3) * (x + 5) + 8 = 0 := h
    have h5 : (x * (x + 5)) * ((x + 2) * (x + 3)) + 8 = 0 := by
      ring_nf at h1 ⊢
      linarith
    have h6 : (x^2 + 5 * x) * (x^2 + 5 * x + 6) + 8 = 0 := by
      have h3 : x * (x + 5) = x^2 + 5 * x := by
        nlinarith
      have h4 : (x + 2) * (x + 3) = x^2 + 5 * x + 6 := by
        nlinarith
      rw [h3, h4] at h5
      linarith
    have h7 : (x^2 + 5 * x) ^ 2 + 6 * (x^2 + 5 * x) + 8 = 0 := by
      nlinarith
    have h9 : (x^2 + 5 * x + 2) * (x^2 + 5 * x + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- Case where x^2 + 5 * x + 2 = 0
      have h12 : x^2 + 5 * x + 2 = 0 := by
        linarith
      have h14 : (x - (Real.sqrt 17 - 5) / 2) * (x - (-Real.sqrt 17 - 5) / 2) = 0 := by
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h14) with h15 h16
      · -- Case where x = (sqrt 17 - 5)/2
        left
        linarith
      · -- Case where x = (-sqrt 17 - 5)/2
        right
        left
        linarith
    · -- Case where x^2 + 5 * x + 4 = 0
      have h17 : x^2 + 5 * x + 4 = 0 := by
        linarith
      have h19 : (x + 1) * (x + 4) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h19) with h20 h21
      · -- Case x = -1
        right
        right
        left
        linarith
      · -- Case x = -4
        right
        right
        right
        linarith
  · -- Show that the right-hand side set is contained in the left-hand side set
    rintro (h | h | h | h)
    · -- Case x = (Real.sqrt 17 - 5) / 2
      rw [h]
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
    · -- Case x = (-Real.sqrt 17 - 5) / 2
      rw [h]
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
    · -- Case x = -1
      rw [h]
      norm_num
    · -- Case x = -4
      rw [h]
      norm_num