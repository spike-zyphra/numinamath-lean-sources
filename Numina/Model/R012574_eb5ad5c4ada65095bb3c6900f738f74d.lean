import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_216420 (f : ℝ → ℝ) (hf : f = λ x => sin x ^ 2 * cos (2 * x)) :
    IsLeast {y | ∃ x ∈ Icc 0 (π/2), f x = y} (-1) ∧
    IsGreatest {y | ∃ x ∈ Icc 0 (π/2), f x = y} (1/8) := by

  constructor
  · -- First part: proving that -1 is the minimum
    constructor
    · -- Show that -1 is in the image
      use Real.pi / 2
      constructor
      · -- Show that π/2 ∈ Icc 0 (π/2)
        exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      · -- Show that f(π/2) = -1
        rw [hf]
        have h1 : sin (Real.pi / 2) = 1 := by
          exact sin_pi_div_two
        have h2 : cos (2 * (Real.pi / 2)) = -1 := by
          have h3 : 2 * (Real.pi / 2) = Real.pi := by
            ring
          rw [h3]
          norm_num
        simp [h1, h2]
        all_goals nlinarith
    · -- Show that -1 is indeed the smallest
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      rw [hf] at hfx
      have h1 : 0 ≤ x := by
        linarith [hx.1]
      have h2 : x ≤ Real.pi / 2 := by
        linarith [hx.2]
      have hx3 : sin x ≥ 0 := by
        apply sin_nonneg_of_nonneg_of_le_pi
        linarith [Real.pi_pos]
        linarith [Real.pi_pos]
      have h3 : sin x ^ 2 * cos (2 * x) ≥ -1 := by
        have h4 : cos (2 * x) ≥ -1 := by
          nlinarith [neg_one_le_cos (2 * x), cos_le_one (2 * x)]
        nlinarith [sq_nonneg (sin x ^ 2 - 1), sq_nonneg (cos (2 * x) + 1),
            Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - 1 / 4), sq_nonneg (cos (2 * x) + 1),
              Real.sin_sq_add_cos_sq x, sin_le_one x, cos_le_one (2 * x), neg_one_le_cos (2 * x)]
      have h4 : sin x ^ 2 * cos (2 * x) = y := by
        have eq5 : (fun (x0 : ℝ) => sin x0 ^ 2 * cos (2 * x0)) x = sin x ^ 2 * cos (2 * x) := by
          simp
        rw [eq5] at hfx
        linarith
      linarith [h3, h4]

  · -- Now for the maximum: 1/8
    constructor
    · -- Show that 1/8 is in the image
      use Real.pi / 6
      constructor
      · -- Show that π/6 ∈ Icc 0 (π/2)
        exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      · -- Show that f(π/6) = 1/8
        rw [hf]
        have h1 : sin (Real.pi / 6) = 1 / 2 := by
          exact sin_pi_div_six
        have h2 : cos (2 * (Real.pi / 6)) = 1 / 2 := by
          have h3 : 2 * (Real.pi / 6) = Real.pi / 3 := by
            ring
          rw [h3]
          exact cos_pi_div_three
        simp [h1, h2]
        all_goals nlinarith
    · -- Show that 1/8 is the greatest
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      rw [hf] at hfx
      have h1 : 0 ≤ x := by
        linarith [hx.1]
      have h2 : x ≤ Real.pi / 2 := by
        linarith [hx.2]
      have hx3 : sin x ≥ 0 := by
        apply sin_nonneg_of_nonneg_of_le_pi
        linarith [Real.pi_pos]
        linarith [Real.pi_pos]
      have h3 : sin x ^ 2 * cos (2 * x) ≤ 1 / 8 := by
        have h4 : cos (2 * x) = 1 - 2 * sin x ^ 2 := by
          rw [cos_two_mul]
          rw [sin_sq]
          all_goals ring
        rw [h4]
        nlinarith [sq_nonneg (sin x ^ 2 - 1 / 4), sq_nonneg (cos (2 * x) - 1 / 2),
            Real.sin_sq_add_cos_sq x, sq_nonneg (sin x - 1 / 2), sq_nonneg (cos (2 * x) + 1), Real.sin_sq_add_cos_sq x, sin_le_one x, cos_le_one (2 * x)]
      have h4 : sin x ^ 2 * cos (2 * x) = y := by
        have eq52 : (fun (x0 : ℝ) => sin x0 ^ 2 * cos (2 * x0)) x = sin x ^ 2 * cos (2 * x) := by
          simp
        rw [eq52] at hfx
        linarith
      linarith [h3, h4]