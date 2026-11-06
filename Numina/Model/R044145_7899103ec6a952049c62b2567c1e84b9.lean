import Mathlib

open Real Set

theorem algebra_224186 :
    IsLeast {x : ℝ | 0 < x ∧ ∃ y : ℝ, x^2 - 3 * x + 2.5 = sin y - 0.75} (3 / 2) ∧
    IsLeast {y : ℝ | 0 < y ∧ ∃ x : ℝ, x^2 - 3 * x + 2.5 = sin y - 0.75} (Real.pi / 2) := by
  constructor
  · -- First part: proving 3/2 is the least element in the set of positive x satisfying the equation.
    constructor
    · -- Show that 3/2 is in the set.
      constructor
      · norm_num
      · -- Show existence of y = π/2
        use Real.pi / 2
        have h1 : sin (Real.pi / 2 : ℝ) = 1 := by
          exact sin_pi_div_two
        rw [h1]
        norm_num
    · -- Show that 3/2 is the least element in the set.
      intro x hx
      rcases hx with ⟨hx_pos, ⟨y, hy⟩⟩
      have h1 : -1 ≤ sin y := by apply neg_one_le_sin
      have h2 : sin y ≤ 1 := by apply sin_le_one
      nlinarith [sq_nonneg (x - 3 / 2), sq_nonneg (y - Real.pi / 2), 
        Real.sin_sq_add_cos_sq y, sq_nonneg (sin y - 1),
        Real.sin_pi_div_two]
  · -- Second part: proving π/2 is the least element in the set of positive y satisfying the equation.
    constructor
    · -- Show that π/2 is in the set.
      constructor
      · -- Show that π/2 > 0
        linarith [Real.pi_pos]
      · -- Show existence of x = 3/2
        use 3 / 2
        have h1 : sin (Real.pi / 2 : ℝ) = 1 := by
          exact sin_pi_div_two
        rw [h1]
        norm_num
    · -- Show that π/2 is the least element in the set.
      intro y hy
      rcases hy with ⟨y_pos, ⟨x, hx⟩⟩
      have h1 : -1 ≤ sin y := by apply neg_one_le_sin
      have h2 : sin y ≤ 1 := by apply sin_le_one
      have h3 : (x - 3 / 2) ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg (x - 3 / 2), Real.sin_sq_add_cos_sq y, sq_nonneg (y - Real.pi / 2)]
      have hx_eq : x = 3 / 2 := by
        nlinarith [sq_nonneg (x - 3 / 2)]
      have h4 : sin y = 1 := by
        nlinarith [hx_eq, Real.sin_sq_add_cos_sq y]
      by_contra h
      push_neg at h
      have h5 : sin y < 1 := by
        have h6 : y < Real.pi / 2 := by linarith
        have h7 : sin y < sin (Real.pi / 2) := by
          apply sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals
            linarith [Real.pi_pos]
        have h8 : sin (Real.pi / 2) = 1 := sin_pi_div_two
        nlinarith [h7, h8]
      linarith [h4, h5]