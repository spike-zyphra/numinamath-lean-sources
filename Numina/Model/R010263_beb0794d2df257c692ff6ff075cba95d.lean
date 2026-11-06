import Mathlib

theorem algebra_9409 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 - 6 * x + 8) : IsGreatest (Set.image f (Set.Icc 2 6)) 8 ∧ IsLeast (Set.image f (Set.Icc 2 6)) (-1) := by
  constructor
  · -- Show that 8 is the greatest value of f on [2,6]
    constructor
    · -- Show that 8 belongs to f([2,6])
      rw [hf]
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc]
      use 6
      norm_num
      all_goals norm_num
    · -- Show that 8 is an upper bound for f([2,6])
      intro y hy
      rw [hf] at hy
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc] at hy
      rcases hy with ⟨x, hx, rfl, hx'⟩
      have h1 : x ≥ 2 := by linarith [hx.1]
      have h2 : x ≤ 6 := by linarith [hx.2]
      nlinarith [sq_nonneg (x - 6)]
  · -- Show that -1 is the least value of f on [2,6]
    constructor
    · -- Show that -1 belongs to f([2,6])
      rw [hf]
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc]
      use 3
      constructor
      · -- Show that 3 is in [2,6]
        norm_num
      · -- Show that f(3) = -1
        norm_num
    · -- Show that -1 is a lower bound for f([2,6])
      intro y hy
      rw [hf] at hy
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc] at hy
      rcases hy with ⟨x, hx, rfl, hx'⟩
      have h1 : x ≥ 2 := by linarith [hx.1]
      have h2 : x ≤ 6 := by linarith [hx.2]
      nlinarith [sq_nonneg (x - 3)]