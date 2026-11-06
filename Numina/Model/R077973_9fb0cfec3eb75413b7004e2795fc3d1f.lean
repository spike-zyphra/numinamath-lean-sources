import Mathlib
open Real

theorem algebra_7521 {x : ℝ} (hx : x ≠ 0) :
    (x + 1 / x) ^ 2 * abs (sin x) + (25 / 4) * sin x = 0 ↔
    x = -2 ∨ x = -1 / 2 ∨ ∃ k : ℤ, x = k * π := by
  constructor
  · -- Assume the equation holds, prove the equivalence
    intro h
    have h1 : (x + 1 / x) ^ 2 ≥ 0 := by positivity
    by_cases h2 : sin x ≥ 0
    · -- Case 1: $\sin x \geq 0$
      have h3 : abs (sin x) = sin x := abs_of_nonneg h2
      have h4 : sin x * ((x + 1 / x) ^ 2 + 25 / 4) = 0 := by
        nlinarith [h, h3, h1]
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- $\sin x = 0$
        have h7 : sin x = 0 := h5
        obtain ⟨k, hk⟩ := sin_eq_zero_iff.1 h7
        right
        right
        exact ⟨k, by linarith [hk]⟩
      · -- $(x + 1 / x) ^ 2 + 25 / 4 = 0$
        have h8 : (x + 1 / x) ^ 2 + 25 / 4 = 0 := by linarith [h6]
        have h9 : (x + 1 / x) ^ 2 ≥ 0 := by positivity
        have h10 : 25 / 4 > 0 := by norm_num
        have h11 : (x + 1 / x) ^ 2 + 25 / 4 > 0 := by linarith [h9, h10]
        linarith [h8, h11]
    · -- Case 2: $\sin x < 0$
      have h3 : abs (sin x) = - (sin x) := abs_of_neg (lt_of_not_ge h2)
      have h4 : sin x * (-(x + 1 / x) ^ 2 + 25 / 4) = 0 := by
        nlinarith [h, h3, h1]
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- $\sin x = 0$
        linarith
      · -- $-(x + 1 / x) ^ 2 + 25 / 4 = 0$
        have h8 : (x + 1 / x) ^ 2 = 25 / 4 := by linarith [h6]
        have h9 : x + 1 / x = 5 / 2 ∨ x + 1 / x = -5 / 2 := by
          have h10 : (x + 1 / x) ^ 2 - 25 / 4 = 0 := by linarith
          have h11 : ((x + 1 / x) - 5 / 2) * ((x + 1 / x) + 5 / 2) = 0 := by nlinarith
          cases' (mul_eq_zero.mp h11) with h12 h13
          · -- $(x + 1 / x) - 5 / 2 = 0$
            left
            linarith
          · -- $(x + 1 / x) + 5 / 2 = 0$
            right
            linarith
        cases' h9 with h9 h9
        · -- $x + 1 / x = 5 / 2$
          have h10 : x ^ 2 - (5 / 2) * x + 1 = 0 := by
            field_simp at h9
            nlinarith
          have h11 : (x - 2) * (x - 1 / 2) = 0 := by
            nlinarith
          cases' (mul_eq_zero.mp h11) with h12 h13
          · -- $x = 2$
            have h14 : x = 2 := by linarith
            have h15 : sin x > 0 := by
              rw [h14]
              apply sin_pos_of_pos_of_lt_pi
              all_goals linarith [Real.pi_gt_314]
            linarith
          · -- $x = 1 / 2$
            have h14 : x = 1 / 2 := by linarith
            have h15 : sin x > 0 := by
              rw [h14]
              apply sin_pos_of_pos_of_lt_pi
              all_goals linarith [Real.pi_gt_314]
            linarith
        · -- $x + 1 / x = -5 / 2$
          have h10 : x ^ 2 + (5 / 2) * x + 1 = 0 := by
            field_simp at h9
            nlinarith
          have h11 : (x + 2) * (x + 1 / 2) = 0 := by
            nlinarith
          cases' (mul_eq_zero.mp h11) with h12 h13
          · -- $x = -2$
            have h14 : x = -2 := by linarith
            left
            exact h14
          · -- $x = -1 / 2$
            have h14 : x = -1 / 2 := by linarith
            right
            left
            exact h14
  · -- Proof of reverse implication
    rintro (h | h | ⟨k, hk⟩)
    · -- $x = -2$
      rw [h]
      have h1 : sin (-2 : ℝ) < 0 := by
        have h2 : sin (-2 : ℝ) = -sin (2 : ℝ) := by rw [show (-2 : ℝ) = - (2 : ℝ) by ring]; simp
        have h3 : sin (2 : ℝ) > 0 := by
          apply sin_pos_of_pos_of_lt_pi
          all_goals linarith [Real.pi_gt_314]
        linarith
      have h4 : abs (sin (-2 : ℝ)) = - (sin (-2 : ℝ)) := by rw [abs_of_neg h1]
      nlinarith [Real.sin_sq_add_cos_sq (-2), Real.sin_sq_add_cos_sq (2), Real.pi_pos]
    · -- $x = -1 / 2$
      rw [h]
      have h1 : sin (-1 / 2 : ℝ) < 0 := by
        have h2 : sin (-1 / 2 : ℝ) = -sin (1 / 2 : ℝ) := by rw [show (-1 / 2 : ℝ) = - (1 / 2 : ℝ) by ring]; simp
        have h3 : sin (1 / 2 : ℝ) > 0 := by
          apply sin_pos_of_pos_of_lt_pi
          all_goals linarith [Real.pi_gt_314]
        linarith
      have h4 : abs (sin (-1 / 2 : ℝ)) = - (sin (-1 / 2 : ℝ)) := by rw [abs_of_neg h1]
      nlinarith [Real.sin_sq_add_cos_sq (-1 / 2), Real.sin_sq_add_cos_sq (1 / 2), Real.pi_pos]
    · -- $x = k * π$ where $k \in \mathbb{Z}$
      rw [hk]
      have h1 : sin (k * π : ℝ) = 0 := by
        have hk2 : (k * π : ℝ) = (k : ℝ) * π := by ring
        rw [hk2]
        simp [Real.sin_int_mul_pi]
      rw [h1]
      norm_num