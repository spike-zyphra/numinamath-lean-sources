import Mathlib

theorem algebra_22276 :
    IsLeast {p | ∃(x y : ℝ), 0 < x ∧ 0 < y ∧ 2 * x + 3 * y = 5 ∧ p = 3 / x + 2 / y} (24 / 5) := by
  constructor
  · -- Show that 24 / 5 is indeed achievable with x = 5 / 4 and y = 5 / 6
    use 5 / 4, 5 / 6
    constructor
    · -- Show x is positive
      norm_num
    constructor
    · -- Show y is positive
      norm_num
    constructor
    · -- Show 2 * x + 3 * y = 5
      norm_num
    · -- Show p = 3 / x + 2 / y
      norm_num
  · -- Show that 24 / 5 is the minimum value in the set
    intro p hp
    rcases hp with ⟨x, y, hx, hy, h, hp⟩
    have h1 : 0 < x * y := by
      apply mul_pos
      exact hx
      exact hy
    have h2 : 3 / x + 2 / y ≥ 24 / 5 := by
      have h3 : 2 * x + 3 * y = 5 := h
      have h4 : 0 < x * y := h1
      have h5 : (3 / x + 2 / y) = (3 * y + 2 * x) / (x * y) := by
        field_simp
        <;> nlinarith
      have h7 : (3 * y + 2 * x) = 5 := by linarith
      have h8 : x * y ≤ 25 / 24 := by
        nlinarith [sq_nonneg (x - 5 / 4), sq_nonneg (y - 5 / 6), 
          mul_pos hx hy, 
          sq_nonneg (2 * x - 5), sq_nonneg (3 * y - 5), 
          h
        ]
      have h9 : (3 * y + 2 * x) = 5 := h7
      have h10 : (3 / x + 2 / y) = (3 * y + 2 * x) / (x * y) := h5
      rw [h10]
      rw [h9]
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    linarith [hp, h2]