import Mathlib

theorem algebra_13790 :
  IsGreatest {k | ∃ x y : ℝ, x ^ 2 - y ^ 2 = 1 / 22 ∧ x ≠ 0 ∧ k = (1 - 22 * x * y) / x ^ 2} (55 / 2) := by
  constructor
  · -- Let's prove that 55/2 is attainable
    use Real.sqrt (2 / 33), - (Real.sqrt (2 / 33)) / 2
    have h1 : (Real.sqrt (2 / 33 : ℝ)) ^ 2 = 2 / 33 := Real.sq_sqrt (by norm_num)
    have h2 : (- (Real.sqrt (2 / 33 : ℝ)) / 2 : ℝ) ^ 2 = (1 / 66 : ℝ) := by
      calc
        (- (Real.sqrt (2 / 33 : ℝ)) / 2 : ℝ) ^ 2 = (Real.sqrt (2 / 33 : ℝ) ^ 2) / 4 := by ring
        _ = (2 / 33) / 4 := by rw [h1]
        _ = 1 / 66 := by norm_num
    constructor
    · -- Show that x^2 - y^2 = 1/22
      linarith [h1, h2]
    constructor
    · -- Show that x ≠ 0
      have h3 : Real.sqrt (2 / 33 : ℝ) > 0 := Real.sqrt_pos.2 (by norm_num)
      linarith
    · -- Show that (1 - 22 * x * y) / x^2 = 55 / 2
      have h3 : Real.sqrt (2 / 33 : ℝ) > 0 := Real.sqrt_pos.2 (by norm_num)
      have h4 : (Real.sqrt (2 / 33 : ℝ)) ^ 2 = 2 / 33 := Real.sq_sqrt (by norm_num)
      field_simp [h4]
      ring_nf
      <;> norm_num [h1]
  · -- Prove that 55/2 is an upper bound
    intro k hk
    rcases hk with ⟨x, y, h1, hx, h2⟩
    have h3 : x ^ 2 - y ^ 2 = 1 / 22 := h1
    have h4 : k = (1 - 22 * x * y) / x ^ 2 := h2
    have h5 : x ^ 2 ≠ 0 := by
      intro h
      apply hx
      nlinarith
    have h6 : k = (1 / x ^ 2) - 22 * (y / x) := by
      rw [h4]
      field_simp [h5]
      ring
    let t := y / x
    have h7 : t = y / x := rfl
    have h8 : x ^ 2 * (1 - t ^ 2) = 1 / 22 := by
      have h9 : y = t * x := by
        rw [h7]
        field_simp [h5]
      rw [h9] at h3
      nlinarith [sq_nonneg (x * t + y), sq_nonneg (x - y), sq_nonneg (x + y)]
    have h9 : 1 - t - t^2 ≤ 5 / 4 := by
      nlinarith [sq_nonneg (t + 1 / 2)]
    have h10 : k ≤ 55 / 2 := by
      have h10 : (1 / x ^ 2) = 22 * (1 - t^2) := by
        have h11 : x^2 ≠ 0 := h5
        have h12 : 1 - t^2 ≠ 0 := by
          by_contra h
          nlinarith [h8, h]
        have h13 : x^2 * (1 - t^2) = 1 / 22 := h8
        have h14 : (1 - t^2) = 1 / (22 * x^2) := by
          field_simp [h11]
          nlinarith
        field_simp at h14 ⊢
        nlinarith
      have h11 : k = 22 * (1 - t - t^2) := by 
        have h12 : (1 / x ^ 2) = 22 * (1 - t^2) := h10
        linarith [h6, h12]
      nlinarith [h11, h9]
    linarith [h10]