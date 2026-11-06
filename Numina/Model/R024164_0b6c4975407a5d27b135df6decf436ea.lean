import Mathlib

theorem algebra_322495 (x : ℝ) (hx : x ≠ -1) :
    ((19 * x - x ^ 2) / (x + 1)) * (x + (19 - x) / (x + 1)) = 84 ↔
    x = 3 ∨ x = 4 ∨ x = 6 + Real.sqrt 29 ∨ x = 6 - Real.sqrt 29 := by
  constructor
  · -- Forward direction: original equation to solutions
    intro h
    have h1 : x + 1 ≠ 0 := by
      intro h2
      apply hx
      linarith
    have eq1 : ((19 * x - x ^ 2) / (x + 1)) * (x + (19 - x) / (x + 1)) =
      ((19 * x - x ^ 2) * (x ^ 2 + 19)) / ((x + 1) ^ 2) := by
      have eq2 : x + (19 - x) / (x + 1) = (x ^ 2 + 19) / (x + 1) := by
        field_simp [h1]
        <;> ring
      rw [eq2]
      field_simp [h1]
      <;> ring_nf
      <;> field_simp [h1]
      <;> ring_nf
    rw [eq1] at h
    have eq2 : ((19 * x - x ^ 2) * (x ^ 2 + 19)) = 84 * ((x + 1) ^ 2) := by
      field_simp [h1] at h ⊢
      nlinarith
    have eq3 : (x - 3) * (x - 4) * (x ^ 2 - 12 * x + 7) = 0 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg ((x + 1) ^ 2), sq_nonneg (x - 3), sq_nonneg (x - 4), Real.sqrt_nonneg 29, Real.sq_sqrt (show (0 : ℝ) ≤ (29 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp eq3) with eq4 eq5
    cases' (mul_eq_zero.mp eq4) with eq6 eq7
    · -- x - 3 = 0
      left
      linarith
    · -- x - 4 = 0
      right
      left
      linarith
    · -- x^2 -12 x +7 =0
      have eq8 : x ^ 2 - 12 * x + 7 = 0 := by
        linarith
      have h_eq9 : (x - (6 + Real.sqrt 29)) * (x - (6 - Real.sqrt 29)) = 0 := by
        nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (0 : ℝ) ≤ (29 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h_eq9) with h_eq10 h_eq11
      · -- x =6 + sqrt(29)
        right
        right
        left
        linarith
      · -- x =6 - sqrt(29)
        right
        right
        right
        linarith
  · -- Backward direction: solutions satisfy the original equation
    rintro (h | h | h | h)
    · -- x =3
      rw [h]
      norm_num
      <;> field_simp <;> norm_num
    · -- x =4
      rw [h]
      norm_num
      <;> field_simp <;> norm_num
    · --x = 6 + Real.sqrt 29
      rw [h]
      have h1 : (6 + Real.sqrt 29 : ℝ) + 1 ≠ 0 := by
        nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num)]
      field_simp [h1]
      ring_nf
      nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num), sq_nonneg (6 + Real.sqrt 29 + 1)]
    · --x = 6 - Real.sqrt 29
      rw [h]
      have h1 : (6 - Real.sqrt 29 : ℝ) + 1 ≠ 0 := by
        nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num)]
      field_simp [h1]
      ring_nf
      nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num), sq_nonneg (6 - Real.sqrt 29 + 1)]