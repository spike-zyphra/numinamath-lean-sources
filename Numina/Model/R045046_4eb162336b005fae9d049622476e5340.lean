import Mathlib

theorem algebra_10463 : IsLeast { (y) | (x : ℝ) (y : ℝ) (h : x ^ 2 + y ^ 2 = 14 * x + 48 * y) } (-1) := by
  constructor
  · -- Show that -1 is indeed in the set.
    use 7, -1
    norm_num
  · -- Show that -1 is a lower bound
    intro y
    rintro ⟨x, hx, hy, h⟩ 
    have h_eq : x ^ 2 + y ^ 2 = 14 * x + 48 * y := by
      rw [show hx = y by tauto] at hy
      linarith
    have eq : (x - 7) ^ 2 + y ^ 2 = x ^ 2 + (y) ^ 2 - 14 * x + 49 := by
      ring
    have h1 : (x - 7) ^ 2 + (y - 24) ^ 2 = 625 := by
      have eq2 : (x - 7) ^ 2 + (y - 24) ^ 2 = x ^ 2 + y ^ 2 - 14 * x - 48 * y + 625 := by
        ring
      have eq3 : x ^ 2 + y ^ 2 = 14 * x + 48 * y := h_eq
      linarith [eq2, eq3]
    nlinarith [sq_nonneg (x - 7), sq_nonneg (y - 24 - 25)]