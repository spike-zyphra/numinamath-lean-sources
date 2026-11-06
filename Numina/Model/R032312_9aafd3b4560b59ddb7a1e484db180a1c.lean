import Mathlib

theorem algebra_21342 : IsLeast {n : ℝ | ∃ x y, n = 2*x^2 + 3*y^2 + 8*x - 24*y + 62} 6 := by
  constructor
  · -- Show that 6 is in the set
    use -2, 4
    norm_num
  · -- Show that no value less than 6 is in the set
    intro n hn
    rcases hn with ⟨x, y, h_eq⟩
    have h1 : 2*x^2 + 3*y^2 + 8*x - 24*y + 62 ≥ 6 := by
      have h2 : 2*x^2 + 3*y^2 + 8*x - 24*y + 62 = 2*(x + 2)^2 + 3*(y - 4)^2 + 6 := by
        ring
      rw [h2]
      have h3 : 2*(x + 2)^2 ≥ 0 := by
        nlinarith [sq_nonneg (x + 2)]
      have h4 : 3*(y - 4)^2 ≥ 0 := by
        nlinarith [sq_nonneg (y - 4)]
      have h5 : 2*(x + 2)^2 + 3*(y - 4)^2 ≥ 0 := by
        linarith [h3, h4]
      linarith
    linarith [h_eq, h1]