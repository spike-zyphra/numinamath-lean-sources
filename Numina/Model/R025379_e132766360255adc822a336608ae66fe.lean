import Mathlib

theorem algebra_95904 : {(x, y) : ℝ × ℝ | (x - y + 2) * (3 * x + y - 4) = 0 ∧ (x + y - 2) * (2 * x - 5 * y + 7) = 0}.ncard = 4 := by

  have h : {(x, y) : ℝ × ℝ | (x - y + 2) * (3 * x + y - 4) = 0 ∧ (x + y - 2) * (2 * x - 5 * y + 7) = 0} = {(-1, 1), (0, 2), (1, 1), (13/17, 29/17)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- First directions: if (x,y) satisfies both equations, then (x,y) ∈ {(-1, 1), (0, 2), (1, 1), (13/17, 29/17)}
      rintro ⟨h₁, h₂⟩

      have h3 : (x - y + 2) = 0 ∨ (3 * x + y - 4) = 0 := by
        apply mul_eq_zero.mp
        simpa using h₁

      have h4 : (x + y - 2) = 0 ∨ (2 * x - 5 * y + 7) = 0 := by
        apply mul_eq_zero.mp
        simpa using h₂

      rcases h3 with h3 | h3
      · -- If $x - y + 2 = 0$.
        rcases h4 with h4 | h4
        · -- If $x + y - 2 = 0$.
          have hx : x = (0 : ℝ) := by
            linarith
          have hy : y = (2 : ℝ) := by
            linarith
          simp [hx, hy]
        · -- If $2x - 5y + 7 = 0$.
          have hx : x = (-1 : ℝ) := by
            linarith
          have hy : y = (1 : ℝ) := by
            linarith
          simp [hx, hy]
      · -- If $3x + y - 4 = 0$.
        rcases h4 with h4 | h4
        · -- If $x + y - 2 = 0$.
          have hx : x = (1 : ℝ) := by
            linarith
          have hy : y = (1 : ℝ) := by
            linarith
          simp [hx, hy]
        · -- If $2x - 5y + 7 = 0$.
          have hx : x = (13 / 17 : ℝ) := by
            linarith
          have hy : y = (29 / 17 : ℝ) := by
            linarith
          simp [hx, hy]

    · -- Second direction: if (x,y) ∈ {(-1, 1), (0, 2), (1, 1), (13/17, 29/17)}, then (x,y) satisfies both equations.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (-1, 1)
        constructor
        · norm_num
        · norm_num
      · -- Check (0, 2)
        constructor
        · norm_num
        · norm_num
      · -- Check (1, 1)
        constructor
        · norm_num
        · norm_num
      · -- Check (13/17, 29/17)
        constructor
        · norm_num
        · norm_num

  rw [h]
  rw [Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals
    norm_num [Prod.ext_iff]