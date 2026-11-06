import Mathlib


open Complex


theorem algebra_111880 (z : Fin 3 → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (hsum : ∑ i, (z i)^2 = 0) (hne : ∑ i, z i ≠ 0) :
    ‖∑ i, z i * z ((i + 1) % 3)‖ = 2 := by

  have h1 : ∀ i, (z i).re ^ 2 + (z i).im ^ 2 = 1 := by
    intro i
    have h2 : ‖z i‖ = 1 := hz i
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq] at h2 ⊢
    nlinarith
  have h2 : (z 0)^2 + (z 1)^2 + (z 2)^2 = 0 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hsum ⊢
    exact hsum

  have h3 : ∑ i, z i * z ((i + 1) % 3) = z 0 * z 1 + z 1 * z 2 + z 2 * z 0 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Fin.sum_univ_three]
    all_goals ring

  rw [h3]

  have h4 : ‖z 0 * z 1 + z 1 * z 2 + z 2 * z 0‖ = ‖z 0 + z 1 + z 2‖ := by
    have h3 : ‖z 0 * z 1 + z 1 * z 2 + z 2 * z 0‖ = ‖z 0 + z 1 + z 2‖ := by
      have h10 : ‖z 0 * z 1 + z 1 * z 2 + z 2 * z 0‖ = Real.sqrt ((z 0 * z 1 + z 1 * z 2 + z 2 * z 0).re ^ 2 + (z 0 * z 1 + z 1 * z 2 + z 2 * z 0).im ^ 2) := by
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        all_goals ring
      have h11 : ‖z 0 + z 1 + z 2‖ = Real.sqrt ((z 0 + z 1 + z 2).re ^ 2 + (z 0 + z 1 + z 2).im ^ 2) := by
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        all_goals ring
      rw [h10, h11]
      have h5 : (z 0 * z 1 + z 1 * z 2 + z 2 * z 0).re ^ 2 + (z 0 * z 1 + z 1 * z 2 + z 2 * z 0).im ^ 2 = (z 0 + z 1 + z 2).re ^ 2 + (z 0 + z 1 + z 2).im ^ 2 := by
        have h01 : (z 0).re ^ 2 + (z 0).im ^ 2 = 1 := h1 0
        have h02 : (z 1).re ^ 2 + (z 1).im ^ 2 = 1 := h1 1
        have h03 : (z 2).re ^ 2 + (z 2).im ^ 2 = 1 := h1 2
        simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im, pow_two]
        ring_nf at *
        nlinarith [sq_nonneg ((z 0).re * (z 1).im - (z 0).im * (z 1).re), sq_nonneg ((z 1).re * (z 2).im - (z 1).im * (z 2).re), sq_nonneg ((z 2).re * (z 0).im - (z 2).im * (z 0).re),
          sq_nonneg ((z 0).re - (z 1).re), sq_nonneg ((z 0).im - (z 1).im),
          sq_nonneg ((z 1).re - (z 2).re), sq_nonneg ((z 1).im - (z 2).im),
          sq_nonneg ((z 0).re - (z 2).re), sq_nonneg ((z 0).im - (z 2).im)]
      rw [h5]
    exact h3

  have h5 : ‖z 0 + z 1 + z 2‖ = 2 := by
    have h16 : (z 0 + z 1 + z 2) ^ 2 = 2 * (z 0 * z 1 + z 1 * z 2 + z 2 * z 0) := by
      have h20 : (z 0 + z 1 + z 2) ^ 2 = z 0^2 + z 1^2 + z 2^2 + 2 * (z 0 * z 1 + z 1 * z 2 + z 2 * z 0) := by
        ring
      rw [h20]
      have h21 : z 0^2 + z 1^2 + z 2^2 = 0 := by
        simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h2 ⊢
        exact h2
      rw [h21]
      all_goals ring
    have h17 : ‖(z 0 + z 1 + z 2) ^ 2‖ = ‖2 * (z 0 * z 1 + z 1 * z 2 + z 2 * z 0)‖ := by
      rw [h16]
    have h18 : ‖(z 0 + z 1 + z 2) ^ 2‖ = ‖z 0 + z 1 + z 2‖ ^ 2 := by
      simp [norm_pow]
    have h19 : ‖2 * (z 0 * z 1 + z 1 * z 2 + z 2 * z 0)‖ = 2 * ‖z 0 * z 1 + z 1 * z 2 + z 2 * z 0‖ := by
      simp [norm_mul]
    rw [h18, h19] at h17
    have h20 : ‖z 0 * z 1 + z 1 * z 2 + z 2 * z 0‖ = ‖z 0 + z 1 + z 2‖ := by
      linarith [h4]
    rw [h20] at h17
    have h21 : ‖z 0 + z 1 + z 2‖ ^ 2 = 2 * ‖z 0 + z 1 + z 2‖ := by
      nlinarith
    have h22 : ‖z 0 + z 1 + z 2‖ = 0 ∨ ‖z 0 + z 1 + z 2‖ = 2 := by
      have h10 : ‖z 0 + z 1 + z 2‖ ^ 2 - 2 * ‖z 0 + z 1 + z 2‖ = 0 := by
        linarith
      have h11 : ‖z 0 + z 1 + z 2‖ * (‖z 0 + z 1 + z 2‖ - 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h11) with h12 h13
      · left
        linarith
      · right
        linarith
    cases h22 with
    | inl h0 =>
      have h00 : z 0 + z 1 + z 2 = 0 := by
        have h10 : ‖z 0 + z 1 + z 2‖ = 0 := by
          linarith
        simpa using h10
      have h11 : ∑ i, z i = 0 := by
        simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at *
        exact h00
      contradiction
    | inr h2 =>
      linarith

  linarith [h4, h5]