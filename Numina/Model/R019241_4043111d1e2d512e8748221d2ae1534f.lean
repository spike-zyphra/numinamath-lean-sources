import Mathlib

theorem algebra_153800 (x : ℝ) (hx : x ∈ Set.Ioo (3 * Real.pi / 2) (2 * Real.pi)) (ht : Real.tan x = -8 / 15) :
    Real.sin x = -8 / 17 ∧ Real.cos x = 15 / 17 ∧ 1 / Real.tan x = -15 / 8 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : Real.cos x ≠ 0 := by
    by_contra h
    have htan : Real.tan x = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h]
    rw [htan] at ht
    norm_num at ht
  have htan : Real.sin x / Real.cos x = -8 / 15 := by
    rw [Real.tan_eq_sin_div_cos] at ht
    linarith
  have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h3 : Real.sin x = -8 / 15 * Real.cos x := by
    have h4 : Real.cos x ≠ 0 := h1
    have h5 : Real.sin x / Real.cos x = -8 / 15 := htan
    field_simp [h4] at h5 ⊢
    linarith
  have h7 : Real.cos x = 15 / 17 := by
    have h13 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := h2
    rw [show Real.sin x = -8 / 15 * Real.cos x by linarith [h3]] at h13
    have h71 : Real.cos x ^ 2 = 225 / 289 := by
      nlinarith
    have h8 : (Real.cos x - 15 / 17) * (Real.cos x + 15 / 17) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case where $\cos x = 15/17$
      linarith
    · -- If `cos x = -15/17`, then $\sin x >0$ which is a contradiction
      have h5 : Real.cos x = -15 / 17 := by
        nlinarith
      have h13 : Real.sin x = 8 / 17 := by 
        rw [show Real.sin x = -8 / 15 * Real.cos x by linarith [h3]]
        nlinarith
      -- Contradiction because in the 4th quadrant $\sin x < 0$.
      have h14 : Real.sin x < 0 := by
        have h9 : 0 < 2 * Real.pi - x := by 
          linarith
        have h14 : Real.sin x = - Real.sin (2 * Real.pi - x) := by
          rw [show 2 * Real.pi - x = 2 * Real.pi - x by ring]
          rw [Real.sin_two_pi_sub]
          <;> ring_nf <;> linarith 
        have h15 : Real.sin (2 * Real.pi - x) > 0 := by 
          apply Real.sin_pos_of_pos_of_lt_pi
          all_goals
          nlinarith [Real.pi_gt_three, Real.pi_pos, Real.pi_pos]
        nlinarith
      linarith
  -- Now solving $\sin x = -8/17$
  have h8 : Real.sin x = -8 / 17 := by
    rw [h3]
    nlinarith [h7]
  -- Now solving reciprocal of tangent.
  have h9 : 1 / Real.tan x = -15 / 8 := by
    rw [ht]
    norm_num
  constructor
  · linarith [h8]
  constructor 
  · linarith [h7]
  · linarith [h9]