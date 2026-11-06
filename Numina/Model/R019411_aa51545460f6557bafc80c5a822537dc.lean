import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_197462 : IsGreatest {y | ∃ x : ℝ, y = cos (2 * x) + 2 * abs (sin x)} (3 / 2) := by
  constructor
  · -- Show 3/2 is in the set
    use Real.pi / 6
    have h1 : sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
    have h2 : abs (sin (Real.pi / 6)) = 1 / 2 := by
      rw [h1]
      norm_num
    have h3 : cos (2 * (Real.pi / 6)) = 1 / 2 := by
      have h3a : 2 * (Real.pi / 6) = Real.pi / 3 := by ring_nf
      rw [h3a]
      exact Real.cos_pi_div_three
    rw [h3, h2]
    all_goals norm_num
  · -- Show that 3/2 is the greatest element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : cos (2 * x) = 1 - 2 * (sin x) ^ 2 := by
      rw [cos_two_mul, sin_sq]
      ring_nf
    have h11 : -1 ≤ sin x ∧ sin x ≤ 1 := sin_mem_Icc x
    have h4 : cos (2 * x) + 2 * abs (sin x) ≤ 3 / 2 := by
      have h14 : cos (2 * x) + 2 * abs (sin x) = 1 - 2 * (sin x) ^ 2 + 2 * abs (sin x) := by
        rw [h1]
      rw [h14] at *
      by_cases h : sin x ≥ 0
      · -- sin x ≥ 0
        have habs : abs (sin x) = sin x := abs_of_nonneg h
        rw [habs]
        nlinarith [sq_nonneg (sin x - 1 / 2), sq_nonneg (sin x + 1 / 2), h11.1, h11.2]
      · -- sin x < 0
        have habs : abs (sin x) = -sin x := abs_of_neg (lt_of_not_ge h)
        rw [habs]
        nlinarith [sq_nonneg (sin x - 1 / 2), sq_nonneg (sin x + 1 / 2), h11.1, h11.2]
    linarith [hx, h4]