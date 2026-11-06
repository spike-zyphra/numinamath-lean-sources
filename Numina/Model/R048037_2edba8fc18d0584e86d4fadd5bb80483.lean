import Mathlib

open Real

theorem inequalities_318248 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) :
    (1 + 1 / x) * (1 + 1 / y) ≥ 9 := by
  have h1 : x * y > 0 := by
    apply mul_pos
    exact hx
    exact hy
  have h2 : (1 + 1 / x) * (1 + 1 / y) = 1 + (1/x) + (1/y) + 1/(x * y) := by
    field_simp
    <;> nlinarith
  have h4 : (1/x) + (1/y) = 1/(x * y) := by
    have h5 : x + y = 1 := hxy
    field_simp at *
    nlinarith

  have h7 : 1 + (1/x) + (1/y) + 1/(x * y) = 1 + 2/(x * y) := by
    have h8 : (1/x) + (1/y) = 1/(x * y) := h4
    calc
      1 + (1/x) + (1/y) + 1/(x * y) = 1 + ((1/x) + (1/y)) + 1/(x * y) := by ring
      _ = 1 + (1/(x * y)) + 1/(x * y) := by rw [h8]
      _ = 1 + 2/(x * y) := by
        field_simp
        <;> ring

  have h8 : x * y ≤ 1 / 4 := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), hxy, mul_pos hx hy]

  have h9 : x * y > 0 := h1
  rw [h2, h7]
  have h10 : 1 + 2/(x * y) ≥ 9 := by
    have h11 : x * y > 0 := h9
    have h12 : x * y ≤ 1 / 4 := h8
    have h14 : 2 / (x * y) ≥ 8 := by
      have h15 : x * y ≤ (1 / 4) := h12
      have h16 : x * y > 0 := h11
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
      all_goals linarith
    linarith
  linarith