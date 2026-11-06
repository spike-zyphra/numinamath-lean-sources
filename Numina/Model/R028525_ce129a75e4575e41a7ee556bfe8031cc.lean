import Mathlib

open Real Set
open scoped Real

theorem algebra_258535 (x : ℝ) (hx : x ∈ Ioo 0 (π/2)) :
    IsGreatest {y | ∃ x : ℝ, x ∈ Ioo 0 (π/2) ∧ y = 2 * (cos x)^3 + 3 * (cos x)^2 - 6 * (cos x) - 2 * (cos (3*x))} (1/9) := by
  constructor
  · -- Show that 1/9 is in the set
    use Real.arccos (1 / 3)
    constructor
    · -- Show that arccos(1/3) is in (0, π/2)
      have h1 : 0 < Real.arccos (1 / 3) := by
        apply Real.arccos_pos.2
        norm_num
      have h2 : Real.arccos (1 / 3) < π / 2 := by
        have h3 : Real.cos (π / 2) = 0 := Real.cos_pi_div_two
        have h4 : Real.cos (Real.arccos (1 / 3)) = 1 / 3 := by
          apply Real.cos_arccos
          all_goals norm_num
        by_contra h
        push_neg at h
        have h5 : Real.cos (Real.arccos (1 / 3)) ≤ Real.cos (π / 2) := by
          apply Real.cos_le_cos_of_nonneg_of_le_pi
          all_goals
            nlinarith [Real.pi_pos, Real.arccos_nonneg (1 / 3), Real.arccos_le_pi (1 / 3), h]
        nlinarith [h4, h3, h5]
      exact ⟨h1, h2⟩
    · -- Show that f(arccos(1/3)) = 1/9
      have hcos : cos (Real.arccos (1 / 3)) = 1 / 3 := by
        apply Real.cos_arccos
        all_goals norm_num
      have hcos3 : cos (3 * Real.arccos (1 / 3)) = 4 * (cos (Real.arccos (1 / 3))) ^ 3 - 3 * (cos (Real.arccos (1 / 3)) ) := by
        rw [cos_three_mul]
      rw [hcos3, hcos]
      nlinarith
  · -- Show that 1/9 is the greatest
    intro y hy
    rcases hy with ⟨x, hx, h_eq⟩
    rcases hx with ⟨hx1, hx2⟩
    have hcos3x : cos (3 * x) = 4 * (cos x) ^ 3 - 3 * (cos x) := by
      rw [cos_three_mul]
    have eq1 : 2 * (cos x)^3 + 3 * (cos x)^2 - 6 * (cos x) - 2 * (cos (3*x)) = 3 * (cos x) ^ 2 - 6 * (cos x) ^ 3 := by
      rw [hcos3x]
      ring
    have h1 : 0 < cos x := by
      apply cos_pos_of_mem_Ioo
      constructor
      linarith [hx1, Real.pi_pos]
      linarith [hx2, Real.pi_pos]
    have h2 : cos x < 1 := by
      have h3 : cos x < cos (0 : ℝ) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals
          nlinarith [hx1, hx2, Real.pi_pos]
      have h4 : cos (0 : ℝ) = 1 := by
        simp
      nlinarith [h3, h4]
    have eq2 : 3 * (cos x) ^ 2 - 6 * (cos x) ^ 3 ≤ 1 / 9 := by
      nlinarith [sq_nonneg (cos x - 1 / 3), sq_nonneg (cos x), sq_nonneg (cos x - 3 / 9), sq_nonneg (cos x * (cos x - 1 / 3)), sq_nonneg ((cos x - 1 / 3) * (cos x - 1 / 3))]
    have eq3 : 2 * (cos x)^3 + 3 * (cos x)^2 - 6 * (cos x) - 2 * (cos (3*x)) ≤ 1 / 9 := by
      rw [eq1]
      linarith [eq2]
    linarith [h_eq, eq3]