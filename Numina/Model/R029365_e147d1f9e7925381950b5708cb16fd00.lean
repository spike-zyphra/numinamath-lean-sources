import Mathlib

theorem algebra_178059 {p q : ℝ} (hroots : ∃ x y, x ≠ y ∧ x^2 + p * x + q = 0 ∧ y^2 + p * y + q = 0 ∧ |x - y| = 5 ∧ |x^3 - y^3| = 35) :
    p = 1 ∧ q = -6 ∨ p = -1 ∧ q = -6 := by
  rcases hroots with ⟨x, y, hxy, hx, hy, h1, h2⟩
  have h3 : x^3 - y^3 = (x - y) * (x^2 + x * y + y^2) := by
    ring
  have h4 : |x^3 - y^3| = |x - y| * |x^2 + x * y + y^2| := by
    rw [h3]
    rw [abs_mul]
  rw [h4] at h2
  rw [h1] at h2
  have h4' : |x^2 + x * y + y^2| = 7 := by
    linarith [h2]

  have h5 : x + y = -p := by
    have h5 : (x - y) * (x + y + p) = 0 := by
      nlinarith [hx, hy]
    cases (mul_eq_zero.mp h5) with
    | inl h6 =>
      -- case where x - y = 0
      exfalso
      apply hxy
      linarith
    | inr h7 =>
      -- case where x + y + p = 0
      linarith
  have h6 : x * y = q := by
    have hx' : x^2 + p * x + q = 0 := hx
    rw [show p = -x - y by linarith [h5]] at hx'
    nlinarith [hx']
  have h7 : x^2 + x * y + y^2 = p^2 - q := by
    calc
      x^2 + x * y + y^2 = (x + y) ^ 2 - x * y := by
        linarith
      _ = (-p) ^ 2 - q := by
        rw [h5, h6]
      _ = p^2 - q := by
        ring
  rw [h7] at h4'
  have h8 : (x - y) ^ 2 = p ^ 2 - 4 * q := by
    calc
      (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by
        linarith
      _ = (-p) ^ 2 - 4 * (q) := by
        rw [h5, h6]
      _ = p ^ 2 - 4 * q := by
        ring
  have h9 : (x - y) ^ 2 = 25 := by 
    have h : (x - y) ^ 2 = 25 := by
      calc
        (x - y) ^ 2 = (|x - y|) ^ 2 := by
          rw [sq_abs]
        _ = (5 : ℝ) ^ 2 := by
          rw [h1]
        _ = (25 : ℝ) := by
          norm_num
    linarith
  have h10 : p ^ 2 - 4 * q = 25 := by
    nlinarith [h9, h8]
  cases eq_or_eq_neg_of_abs_eq h4' with
  | inl h11 =>
    have h12 : q = p^2 - 7 := by
      linarith [h11]
    rw [h12] at h10
    have h13 : p ^ 2 = 1 := by
      nlinarith
    have hp : p = 1 ∨ p = -1 := by
      rw [sq_eq_one_iff] at h13
      tauto
    have hq : q = -6 := by
      nlinarith [h12, h13]
    cases hp with
    | inl hp1 =>
      left 
      exact ⟨hp1, hq⟩
    | inr hp2 =>
      right 
      exact ⟨hp2, hq⟩ 
  | inr h12 =>
    have h13 : q = p^2 + 7 := by
      linarith [h12]
    rw [h13] at h10
    nlinarith [sq_nonneg p, sq_nonneg (q - p^2), sq_nonneg (x - y), sq_nonneg (x - (-p - y)), sq_nonneg (x * y - q)]