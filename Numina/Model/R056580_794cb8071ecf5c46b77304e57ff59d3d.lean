import Mathlib

open Real

theorem algebra_2864 (x : Real) (hx : x ∈ Set.Ioo 0 (π / 2)) (h : tan x = 3) :
    17 * sin x - 11 * cos x = 4 * sqrt 10 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : cos x ≠ 0 := by
    by_contra hcos
    have htan : tan x = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [hcos]
      all_goals linarith
    rw [htan] at h
    all_goals linarith
  have h2 : sin x = 3 * cos x := by
    have htan : tan x = sin x / cos x := by
      rw [tan_eq_sin_div_cos]
    rw [htan] at h
    field_simp [h1] at h ⊢
    all_goals linarith
  have h3 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h4 : cos x ^ 2 = 1 / 10 := by
    rw [show sin x = 3 * cos x by linarith [h2]] at h3
    nlinarith
    all_goals nlinarith
  have hcos_pos : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [hx1, hx2, Real.pi_pos]
    · linarith [hx1, hx2, Real.pi_pos]
  have hcos_val : cos x = Real.sqrt (1 / 10) := by
    have h5 : cos x ^ 2 = 1 / 10 := by
      nlinarith
    have h6 : cos x = Real.sqrt (1 / 10) := by
      have hsq : (Real.sqrt (1 / 10)) ^ 2 = (1 / 10 : ℝ) := Real.sq_sqrt (by norm_num)
      have h7 : cos x = Real.sqrt (1 / 10) := by
        have h8 : 0 ≤ Real.sqrt (1 / 10) := by positivity
        have h9 : 0 < cos x := by linarith
        nlinarith [Real.sqrt_nonneg (1 / 10), Real.sq_sqrt (show 0 ≤ (1 / 10 : ℝ) by norm_num)]
      exact h7
    exact h6
  have hsin_val : sin x = 3 * Real.sqrt (1 / 10) := by 
    rw [show sin x = 3 * cos x by linarith [h2]]
    rw [hcos_val]
    all_goals nlinarith [Real.sqrt_nonneg (1 / 10)]
  have h6 : Real.sqrt (1 / 10) = Real.sqrt 10 / 10 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [hsin_val, hcos_val]
  rw [h6]
  ring_nf
  <;> norm_num
  <;> ring_nf <;> norm_num