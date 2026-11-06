import Mathlib

theorem algebra_300275 (θ : Real) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (h : Real.cos θ * Real.cos (θ - Real.pi / 4) = 3 * Real.sqrt 2 / 10) :
    Real.sin θ = 2 * Real.sqrt 5 / 5 := by
  rcases hθ with ⟨hθ1, hθ2⟩
  have hcos_pos : 0 < Real.cos θ := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [hθ1, hθ2, Real.pi_pos]
    · linarith [hθ1, hθ2, Real.pi_pos]
  have hsin_pos : 0 < Real.sin θ := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hθ1, hθ2, Real.pi_pos]
    · linarith [hθ1, hθ2, Real.pi_pos]
  have h1 : Real.cos (θ - Real.pi / 4) = Real.cos θ * Real.cos (Real.pi / 4) + Real.sin θ * Real.sin (Real.pi / 4) := by
    rw [Real.cos_sub]
  have h2 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [Real.cos_pi_div_four]
  have h3 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [Real.sin_pi_div_four]
  rw [h1, h2, h3] at h
  have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h_eq1 : Real.cos θ ^ 2 + Real.cos θ * Real.sin θ = 3 / 5 := by
    nlinarith [h, Real.sqrt_pos.mpr (show 0 < (2 : Real) by norm_num), h4]
  have h5 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h6 : Real.sin θ > 0 := by linarith [hsin_pos]
  have h7 : Real.cos θ > 0 := by linarith [hcos_pos]
  have h8 : Real.sin θ ^ 2 = 4 / 5 := by
    nlinarith [sq_nonneg (Real.cos θ - Real.sqrt 5 / 5), sq_nonneg (Real.sin θ - 2 * Real.sqrt 5 / 5), Real.sqrt_pos.mpr (show (0 : Real) < 5 by norm_num), Real.sq_sqrt (show (0 : Real) ≤ (5 : Real) by norm_num), sq_nonneg (Real.cos θ - Real.sin θ), Real.sqrt_nonneg 2, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : Real) ≤ (2 : Real) by norm_num)]
  have h9 : Real.sin θ = 2 * Real.sqrt 5 / 5 := by
    have h10 : Real.sin θ = Real.sqrt (4 / 5) := by
      have h11 : Real.sin θ ^ 2 = 4 / 5 := h8
      have h12 : Real.sin θ > 0 := h6
      have h13 : Real.sin θ = Real.sqrt (Real.sin θ ^ 2) := by
        rw [Real.sqrt_sq (by linarith)]
      rw [h11] at h13
      linarith
    have h14 : Real.sqrt (4 / 5) = 2 * Real.sqrt 5 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    rw [h14] at h10
    linarith
  linarith [h9]