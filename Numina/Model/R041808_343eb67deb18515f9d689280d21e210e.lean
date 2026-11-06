import Mathlib


theorem algebra_286426 {a b : ℝ} :
    (∃ x y : ℂ, x + y = 2 * a ∧ x * y * (x ^ 2 + y ^ 2) = 2 * b ^ 4 ∧ x.im = 0 ∧ y.im = 0 → a ^ 2 ≥ b ^ 2) ∧ {(x, y) : ℝ × ℝ | x + y = 2 * 10 ∧ x * y * (x ^ 2 + y ^ 2) = 2 * 9375} = {(15, 5), (5, 15)} := by
  constructor
  · -- Show that there exists complex numbers x,y such that if they satisfy the system of equations and have zero imaginary parts (i.e., they are real numbers), then a^2 ≥ b^2 must hold.
    use 0, 0
    intro h
    rcases h with ⟨h0, h1, hx0, hy0⟩
    norm_num [Complex.ext_iff, pow_two, pow_zero, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at h0 h1
    nlinarith [sq_nonneg ( (0 : ℝ) ), sq_nonneg ( (0 : ℝ) ) ]
  · -- Show that the set of real pairs (x,y) satisfying the system with a=10 and b^4=9375 is exactly the set {(15,5), (5,15)}.
    ext ⟨x, y⟩
    simp
    constructor
    · -- If (x,y) is in the left side, then it's in the right side
      rintro ⟨h0, h1⟩
      have h2 : x + y = 20 := by
        linarith
      have h3 : x * y * (x ^ 2 + y ^ 2) = 18750 := by
        nlinarith
      have h4 : x ^ 2 + y ^ 2 = 400 - 2 * (x * y) := by
        have h_eq : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
          nlinarith
        rw [show x + y = 20 by linarith] at h_eq
        linarith
      rw [h4] at h3
      have h5 : (x * y - 125) * (x * y - 75) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- When x*y = 125
        have h8 : x * y = 125 := by linarith
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 20), sq_nonneg (x - 10), sq_nonneg (y - 10) ]
      · -- When x*y = 75
        have h9 : x * y = 75 := by linarith
        have h10 : (x - 15) * (x - 5) = 0 := by
          have h11 : y = 20 - x := by linarith
          rw [h11] at h9
          nlinarith
        cases' (mul_eq_zero.mp h10) with h12 h13
        · -- When x = 15
          have hx15 : x = 15 := by linarith
          have hy5 : y = 5 := by linarith
          simp [hx15, hy5]
        · -- When x = 5
          have hx5 : x = 5 := by linarith
          have hy15 : y = 15 := by linarith
          simp [hx5, hy15]
    · -- If (x,y) is in the right side, then it's in the left side
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (15, 5)
        constructor
        · norm_num
        · norm_num
      · -- (5, 15)
        constructor
        · norm_num
        · norm_num