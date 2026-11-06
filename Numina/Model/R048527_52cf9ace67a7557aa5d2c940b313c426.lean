import Mathlib

theorem algebra_223914 {a b c : ℝ} (h : a ≠ b ∧ b ≠ c ∧ c ≠ a)
    (h' : a / (b - c) + b / (c - a) + c / (a - b) = 0) :
    a / (b - c)^2 + b / (c - a)^2 + c / (a - b)^2 = 0 := by
  have h1 : a / (b - c) + b / (c - a) + c / (a - b) = 0 := h'
  have ha1 : a - b ≠ 0 := by
    intro h_eq
    apply h.1
    linarith
  have hb1 : b - c ≠ 0 := by
    intro h_eq
    apply h.2.1
    linarith
  have hc1 : c - a ≠ 0 := by
    intro h_eq
    apply h.2.2
    linarith
  have h2 : a / (b - c)^2 + b / (c - a)^2 + c / (a - b)^2 =
      (a / (b - c) + b / (c - a) + c / (a - b)) *
      (1 / (b - c) + 1 / (c - a) + 1 / (a - b)) := by
    field_simp [hb1, hc1, ha1, pow_two]
    ring
  rw [h2, h']
  try field_simp [hb1, hc1, ha1, pow_two]
  <;> ring
  <;> field_simp [hb1, hc1, ha1, pow_two]
  <;> ring