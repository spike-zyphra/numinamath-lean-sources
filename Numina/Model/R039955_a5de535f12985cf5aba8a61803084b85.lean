import Mathlib

open BigOperators Real Set

theorem algebra_231984 {f : ℝ → ℝ} (hf : f = λ x => (cos x)^10 + (sin x)^10) :
    IsLeast {T | 0 < T ∧ f = f ∘ (λ x => x + T)} (π/2) := by
  constructor
  · -- Show that π/2 is in the set
    constructor
    · -- Show that 0 < π/2
      linarith [Real.pi_pos]
    · -- Show that f = f ∘ (λ x => x + π/2)
      funext x
      have h1 : f x = f (x + π / 2) := by
        simp [hf]
        have h2 : cos (x + π / 2) = -sin x := by
          rw [cos_add_pi_div_two]
        have h3 : sin (x + π / 2) = cos x := by
          rw [sin_add_pi_div_two]
        have h4 : (cos (x + π / 2) : ℝ) ^ 10 + (sin (x + π / 2) : ℝ) ^ 10 = (cos x : ℝ) ^ 10 + (sin x : ℝ) ^ 10 := by
          rw [h2, h3]
          have h4 : (-sin x : ℝ) ^ 10 = (sin x : ℝ) ^ 10 := by
            ring_nf
          nlinarith [h4]
        linarith [h4]
      simpa using h1
  · -- Show that π/2 is the least element in the set
    intro T hT
    rcases hT with ⟨hT_pos, h_eq⟩
    by_contra h
    push_neg at h
    have h1 : f = f ∘ (λ x => x + T) := h_eq
    have h2 : ∀ x : ℝ, f x = f (x + T) := by
      intro x
      simpa using congr_fun h1 x
    have h3 : f (Real.pi / 4) = f (Real.pi / 4 + T) := by
      apply h2
    have h4 : f (Real.pi / 4) = (cos (Real.pi / 4)) ^ 10 + (sin (Real.pi / 4)) ^ 10 := by
      simp [hf]
    have h5 : f (Real.pi / 4 + T) = (cos (Real.pi / 4 + T)) ^ 10 + (sin (Real.pi / 4 + T) ) ^ 10 := by
      simp [hf]
    rw [h4] at h3
    rw [h5] at h3
    have h6 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h7 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    rw [h6, h7] at h3
    have h8 : (Real.sqrt 2 / 2 : ℝ) ^ 10 + (Real.sqrt 2 / 2 : ℝ) ^ 10 = (1 / 16 : ℝ) := by
      have h9 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
      have h10 : (Real.sqrt 2 / 2 : ℝ) ^ 10 = ((Real.sqrt 2 / 2 : ℝ) ^ 2) ^ 5 := by
        ring
      rw [h10, h9]
      norm_num
    have h9 : cos (Real.pi / 4 + T) ^ 10 + sin (Real.pi / 4 + T) ^ 10 > (1 / 16 : ℝ) := by
      have h14 : cos (Real.pi / 4 + T) ^ 2 + sin (Real.pi / 4 + T) ^ 2 = 1 := by
        exact Real.cos_sq_add_sin_sq (Real.pi / 4 + T)
      have h15 : cos (Real.pi / 4 + T) ^ 2 ≠ 1 / 2 := by
        by_contra h_eq2
        have h13 : cos (Real.pi / 4 + T) ^ 2 = 1 / 2 := by linarith
        have h14 : sin (Real.pi / 4 + T) ^ 2 = 1 / 2 := by
          nlinarith [Real.cos_sq_add_sin_sq (Real.pi / 4 + T)]
        have h17 : cos (2 * (Real.pi / 4 + T)) = 0 := by
          have h18 : cos (2 * (Real.pi / 4 + T)) = 2 * cos (Real.pi / 4 + T) ^ 2 - 1 := by
            rw [cos_two_mul]
          rw [h18, h13]
          norm_num
        have h18 : cos (2 * (Real.pi / 4 + T)) = - sin (2 * T) := by
          have h19 : 2 * (Real.pi / 4 + T) = Real.pi / 2 + 2 * T := by
            ring
          rw [h19]
          have h20 : cos (Real.pi / 2 + 2 * T) = - sin (2 * T) := by
            rw [cos_add, cos_pi_div_two, sin_pi_div_two]
            ring
          linarith [h20]
        have h19 : - sin (2 * T) = 0 := by
          linarith [h17, h18]
        have h20 : sin (2 * T) = 0 := by linarith
        have h21 : ∃ k : ℤ, 2 * T = (k : ℝ) * Real.pi := by
          rw [sin_eq_zero_iff] at h20
          rcases h20 with ⟨k, hk⟩
          use k
          linarith
        rcases h21 with ⟨k, hk⟩
        have h22 : k = 0 := by
          have h23 : (k : ℝ) * Real.pi > 0 := by
            nlinarith [Real.pi_pos, show 0 < T by linarith, hk]
          have h24 : (k : ℝ) * Real.pi < Real.pi := by
            nlinarith [Real.pi_pos, show T < Real.pi / 2 by linarith [h], hk]
          have h25 : k > 0 := by
            by_contra h
            push_neg at h
            have : k ≤ 0 := by omega
            have hk0 : (k : ℝ) ≤ 0 := by exact_mod_cast this
            nlinarith [Real.pi_pos, hk0, hk]
          have h26 : k < 1 := by
            by_contra h
            push_neg at h
            have : k ≥ 1 := by omega
            have hk1 : (k : ℝ) ≥ 1 := by exact_mod_cast this
            nlinarith [Real.pi_pos, hk1, hk]
          omega
        have h23 : (k : ℝ) = (0 : ℝ) := by
          have hk0 : k = 0 := h22
          exact_mod_cast hk0
        have h24 : 2 * T = (0 : ℝ) * Real.pi := by
          rw [show (k : ℝ) = (0 : ℝ) by linarith [h23]] at hk
          linarith
        have h25 : T = 0 := by
          nlinarith
        linarith [show T > 0 by linarith, h25]
      have h18 : cos (Real.pi / 4 + T) ^ 10 + sin (Real.pi / 4 + T) ^ 10 > (1 / 16 : ℝ) := by
        have h19 : cos (Real.pi / 4 + T) ^ 10 + sin (Real.pi / 4 + T) ^ 10 = (cos (Real.pi / 4 + T) ^ 2) ^ 5 + (sin (Real.pi / 4 + T) ^ 2) ^ 5 := by
          ring
        rw [h19]
        have h20 : cos (Real.pi / 4 + T) ^ 2 + sin (Real.pi / 4 + T) ^ 2 = 1 := by
          exact Real.cos_sq_add_sin_sq (Real.pi / 4 + T)
        have h21 : cos (Real.pi / 4 + T) ^ 2 ≠ 1 / 2 := h15
        have h22 : (cos (Real.pi / 4 + T) ^ 2) ^ 5 + (sin (Real.pi / 4 + T) ^ 2) ^ 5 > (1 / 16 : ℝ) := by
          have h23 : sin (Real.pi / 4 + T) ^ 2 = 1 - cos (Real.pi / 4 + T) ^ 2 := by
            linarith [Real.cos_sq_add_sin_sq (Real.pi / 4 + T)]
          rw [h23]
          have h24 : cos (Real.pi / 4 + T) ^ 2 ≠ 1 / 2 := h15
          have h25 : (cos (Real.pi / 4 + T) ^ 2) ^ 5 + (1 - cos (Real.pi / 4 + T) ^ 2) ^ 5 > (1 / 16 : ℝ) := by
            have h27 : cos (Real.pi / 4 + T) ^ 2 ≥ 0 := by nlinarith [sq_nonneg (cos (Real.pi / 4 + T)), sq_nonneg (sin (Real.pi / 4 + T)), Real.cos_sq_add_sin_sq (Real.pi / 4 + T)]
            have h28 : cos (Real.pi / 4 + T) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (cos (Real.pi / 4 + T)), sq_nonneg (sin (Real.pi / 4 + T)), Real.cos_sq_add_sin_sq (Real.pi / 4 + T)]
            have h29 : cos (Real.pi / 4 + T) ^ 2 ≠ 1 / 2 := h15
            nlinarith [sq_pos_of_ne_zero (show (cos (Real.pi / 4 + T) ^ 2 - 1 / 2) ≠ 0 by
              intro h
              apply h15
              nlinarith
            ), sq_nonneg (cos (Real.pi / 4 + T) ^ 2 - 1 / 2), sq_nonneg (cos (Real.pi / 4 + T) ^ 2 - 1), sq_nonneg (cos (Real.pi / 4 + T) ^ 2), sq_nonneg ((cos (Real.pi / 4 + T) ^ 2) ^ 2 - 1 / 4)]
          linarith
        linarith
      linarith
    linarith [h3, h8, h9]