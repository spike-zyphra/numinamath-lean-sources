import Mathlib

/- Given $\frac{a+b-c}{c}=\frac{b+c-a}{a}=\frac{c+a-b}{b}$, and $abc\ne 0$, the value of $\frac{(a+b)(b+c)(c+a)}{abc}$ is ___          ___. -/
theorem algebra_4353 {a b c : ℝ} (h : a ≠ 0) (h1 : b ≠ 0) (h2 : c ≠ 0)
    (h3 : (a + b - c) / c = (b + c - a) / a) (h4 : (b + c - a) / a = (c + a - b) / b) :
    ((a + b) * (b + c) * (c + a)) / (a * b * c) = 8 ∨ ((a + b) * (b + c) * (c + a)) / (a * b * c) = -1 := by
  have h5 : a * (a + b - c) = c * (b + c - a) := by
    have h5 : (a + b - c) / c = (b + c - a) / a := by
      linarith [h3]
    field_simp [h2, h] at h5 ⊢
    all_goals linarith
  have h6 : b * (b + c - a) = a * (c + a - b) := by
    have h6 : (b + c - a) / a = (c + a - b) / b := by
      linarith [h4]
    field_simp [h, h1] at h6 ⊢
    all_goals linarith
  have eq1 : (a - c) * (a + b + c) = 0 := by
    linarith [h5]
  have eq2 : (b - a) * (a + b + c) = 0 := by
    linarith [h6]
  by_cases h7 : a + b + c = 0
  · -- Case where a + b + c = 0
    right
    have eq3 : (a + b) * (b + c) * (c + a) = - (a * b * c) := by
      have h8 : a + b = -c := by linarith
      have h9 : b + c = -a := by linarith
      have h10 : c + a = -b := by linarith
      rw [h8, h9, h10]
      ring
    rw [eq3]
    field_simp [h, h1, h2]
    <;> nlinarith
  · -- Case where a + b + c ≠ 0
    have h8 : a - c = 0 := by
      apply (mul_left_inj' (show a + b + c ≠ 0 by assumption)).mp
      linarith [eq1]
    have h9 : b - a = 0 := by
      apply (mul_left_inj' (show a + b + c ≠ 0 by assumption)).mp
      linarith [eq2]
    have h10 : a = c := by linarith
    have h11 : b = a := by linarith
    left
    have eq3 : (a + b) * (b + c) * (c + a) = 8 * (a * b * c) := by
      rw [show c = a by linarith [h10, h11], show b = a by linarith [h11]]
      ring_nf
    rw [eq3]
    field_simp [h, h1, h2]
    <;> nlinarith