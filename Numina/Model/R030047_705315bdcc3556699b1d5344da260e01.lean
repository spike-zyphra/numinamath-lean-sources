import Mathlib

theorem algebra_3503 (θ : Real) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (h : 3 * Real.sin θ ^ 2 + 5 * Real.sin θ * Real.cos θ - 4 * Real.cos θ ^ 2 = 2) :
    θ = Real.pi / 4 := by
  rcases hθ with ⟨hθ1, hθ2⟩
  have h1 : Real.sin θ > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : Real.cos θ > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h_eq : Real.sin θ ^ 2 + 5 * Real.sin θ * Real.cos θ - 6 * Real.cos θ ^ 2 = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, h]
  have h_eq2 : (Real.sin θ - Real.cos θ) * (Real.sin θ + 6 * Real.cos θ) = 0 := by
    nlinarith [h_eq, Real.sin_sq_add_cos_sq θ]
  cases' (mul_eq_zero.mp h_eq2) with h_eq3 h_eq4
  · -- Case $\sin \theta - \cos \theta = 0$, so $\sin \theta = \cos \theta$
    have h_eq5 : Real.sin θ = Real.cos θ := by linarith
    have h_eq6 : Real.sin θ = Real.cos θ := h_eq5
    have h_eq7 : Real.sin θ > 0 := h1
    have h_eq8 : Real.sin θ = Real.cos θ := h_eq6
    have h_eq9 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    have h_eq10 : Real.sin θ ^ 2 = 1 / 2 := by
      have h_eq11 : Real.cos θ = Real.sin θ := by linarith [h_eq8]
      rw [h_eq11] at h_eq9
      nlinarith
    have h_eq13 : Real.sin θ = Real.sqrt (1 / 2) := by
      have h_eq14 : Real.sin θ ^ 2 = 1 / 2 := h_eq10
      have h_eq15 : Real.sin θ > 0 := h1
      have h_eq16 : Real.sin θ = Real.sqrt (1 / 2) := by
        have h_eq17 : Real.sin θ ^ 2 = 1 / 2 := h_eq14
        have h_eq18 : Real.sin θ ≥ 0 := by linarith
        have h_eq19 : Real.sqrt (Real.sin θ ^ 2) = Real.sqrt (1 / 2) := by
          rw [h_eq17]
        have h_eq20 : Real.sqrt (Real.sin θ ^ 2) = Real.sin θ := by
          rw [Real.sqrt_sq (by linarith)]
        have h_eq21 : Real.sin θ = Real.sqrt (1 / 2) := by
          nlinarith [h_eq19, h_eq20]
        linarith
      linarith
    have h_eq12 : θ = Real.arcsin (Real.sin θ) := by
      rw [Real.arcsin_sin]
      all_goals
        nlinarith [Real.pi_pos]
    rw [h_eq13] at h_eq12
    have h_eq14 : Real.arcsin (Real.sqrt (1 / 2)) = Real.pi / 4 := by
      have h_eq15 : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h_eq15]
      have h_eq16 : Real.arcsin (Real.sqrt 2 / 2) = Real.pi / 4 := by
        have h_eq17 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
        have h_eq18 : Real.pi / 4 ≥ -Real.pi / 2 := by
          nlinarith [Real.pi_pos]
        have h_eq19 : Real.pi / 4 ≤ Real.pi / 2 := by
          nlinarith [Real.pi_pos]
        have h_eq20 : Real.arcsin (Real.sin (Real.pi / 4)) = Real.pi / 4 := by
          apply Real.arcsin_sin
          all_goals
            nlinarith [Real.pi_pos]
        rw [h_eq17] at h_eq20
        linarith
      linarith
    linarith [h_eq12, h_eq14]
  · -- Case $\sin \theta + 6 \cos \theta = 0$ is impossible
    nlinarith [h_eq4, Real.sin_sq_add_cos_sq θ, h1, h2]