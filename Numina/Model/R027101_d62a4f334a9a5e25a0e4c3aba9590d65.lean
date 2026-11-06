import Mathlib

theorem inequalities_224758 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1 / a + 1 / b + 1 / c) :
    3 / a / b / c ≤ a + b + c := by
  have h1 : a * b * c > 0 := by
    apply mul_pos
    apply mul_pos
    all_goals nlinarith

  have h2 : (a + b + c) * (a * b * c) = a * b + a * c + b * c := by
    have eq1 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
      field_simp [show a ≠ 0 by linarith, show b ≠ 0 by linarith, show c ≠ 0 by linarith]
      <;> ring_nf
      <;> field_simp [show a ≠ 0 by linarith, show b ≠ 0 by linarith, show c ≠ 0 by linarith]
      <;> nlinarith
    rw [eq1] at h
    have pos1 : a * b * c > 0 := h1
    field_simp [show a * b * c ≠ 0 by positivity] at h ⊢
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h3 : 3 ≤ (a + b + c) * (a * b * c) := by
    have h4 : (a + b + c) * (a * b * c) = a * b + a * c + b * c := h2
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have pos1 : a * b * c > 0 := h1
  have h4 : (3 : ℝ) / a / b / c ≤ a + b + c := by
    have pos3 : (3 : ℝ) / a / b / c = 3 / (a * b * c) := by
      field_simp [show a ≠ 0 by linarith, show b ≠ 0 by linarith, show c ≠ 0 by linarith]
      <;> ring
    rw [pos3]
    have pos4 : a * b * c > 0 := pos1
    have h5 : 3 ≤ (a + b + c) * (a * b * c) := h3
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
    all_goals nlinarith
  exact h4