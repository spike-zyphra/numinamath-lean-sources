import Mathlib

theorem algebra_311853 (x : ℝ) (hx : x ∈ Set.Icc 0 (Real.pi / 2)) :
    (2 - Real.sin (2 * x)) * Real.sin (x + Real.pi / 4) = 1 ↔ x = Real.pi / 4 := by
  constructor
  · -- Forward implication: if (2 - sin(2x)) * sin(x + π/4) = 1 for x in [0, π/2], then x = π/4
    intro h
    rcases hx with ⟨hx0, hx1⟩
    have h1 : Real.sin (x + Real.pi / 4) = (Real.sin x + Real.cos x) * (Real.sqrt 2 / 2) := by
      rw [Real.sin_add]
      have hsin : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      have hcos : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      rw [hsin, hcos]
      all_goals ring
    have h2 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
      rw [Real.sin_two_mul]
    rw [h1, h2] at h
    have h3 : Real.sin x ≥ 0 := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      linarith [Real.pi_pos, hx0, hx1]
      linarith [Real.pi_pos, hx0, hx1]
    have h4 : Real.cos x ≥ 0 := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · -- 0 ≤ x
        linarith [Real.pi_pos, hx0, hx1]
      · -- x ≤ π/2
        linarith [Real.pi_pos, hx0, hx1]
    have h5 : Real.sin x + Real.cos x ≥ 1 := by
      have h40 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      nlinarith [sq_nonneg (x - Real.pi / 4), sq_nonneg (Real.sin x - Real.cos x), Real.sin_sq_add_cos_sq x, sq_nonneg (x - 0), sq_nonneg (x - Real.pi / 2), Real.pi_pos]
    have h6 : Real.sin x + Real.cos x ≤ Real.sqrt 2 := by
      have h12 : (Real.sin x + Real.cos x) ^ 2 ≤ 2 := by
        have h7 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
        nlinarith [sq_nonneg (Real.sin x - Real.cos x), Real.sin_sq_add_cos_sq x, sq_nonneg (x - Real.pi / 4)]
      have h104 : (Real.sin x + Real.cos x) ≤ Real.sqrt 2 := by
        have h40 : (Real.sin x + Real.cos x) ^ 2 ≤ (2 : ℝ) := h12
        have h400 : Real.sin x + Real.cos x ≥ 0 := by
          nlinarith [h3, h4, Real.sin_sq_add_cos_sq x]
        have h104 : (Real.sin x + Real.cos x) ≤ Real.sqrt 2 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)]
        linarith
      linarith
    have h50 : Real.sin x * Real.cos x ≥ 0 := by
      nlinarith
    have h9 : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
      exact Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)
    have h100 : Real.sqrt 2 > 0 := by
      positivity
    have h11 : Real.sin x + Real.cos x = Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, sq_nonneg (Real.sin x + Real.cos x - Real.sqrt 2), sq_nonneg (Real.sin x - Real.cos x), Real.sin_sq_add_cos_sq x, h9, Real.sqrt_nonneg 2, sq_nonneg (x - Real.pi / 4)]
    have h90 : Real.sin x = Real.cos x := by
      nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x - Real.cos x), sq_nonneg (Real.sin x ^ 2 - Real.cos x ^ 2), Real.sin_sq_add_cos_sq x, Real.sqrt_nonneg 2, sq_nonneg (x - Real.pi / 4)]
    have h020 : x = Real.pi / 4 := by
      have eq7 : Real.sin x = Real.cos x := h90
      have h130 : Real.sin x = Real.sin (Real.pi / 4) := by
        have h400 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
        have h1200 : Real.sin x = Real.sqrt 2 / 2 := by
          nlinarith [Real.sin_sq_add_cos_sq x, Real.sqrt_nonneg 2, Real.sin_pi_div_four, h11, sq_nonneg (x - Real.pi / 4)]
        nlinarith
      have h131 : x ≤ Real.pi := by
        linarith [Real.pi_pos, hx0, hx1]
      have h124 : x = Real.pi / 4 := by
        have h126 : x ≤ Real.pi / 2 := by linarith [Real.pi_pos, hx0, hx1]
        have h1300 : Real.sin x = Real.sin (Real.pi / 4) := h130
        have h020 : x ≥ 0 := by nlinarith
        have h1005 : x ≤ Real.pi / 2 := by nlinarith
        -- Use the fact about arcsin
        have h1020 : x = Real.arcsin (Real.sin x) := by
          rw [Real.arcsin_sin]
          all_goals linarith [Real.pi_pos, hx0, hx1]
        have h1025 : Real.arcsin (Real.sin x) = Real.pi / 4 := by
          have h1040 : Real.sin x = Real.sin (Real.pi / 4) := h1300
          rw [h1040]
          apply Real.arcsin_sin
          all_goals linarith [Real.pi_pos, show Real.pi / 4 ≥ -Real.pi / 2 by linarith [Real.pi_pos], show Real.pi / 4 ≤ Real.pi / 2 by linarith [Real.pi_pos]]
        linarith
      linarith
    linarith
  · -- Backward implication: if x = π/4, then (2 - sin(2x)) * sin(x + π/4) = 1
    intro h
    rw [h]
    have h1 : Real.sin (2 * (Real.pi / 4)) = 1 := by
      have h2 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
      rw [h2]
      exact Real.sin_pi_div_two
    have h3 : Real.sin (Real.pi / 4 + Real.pi / 4) = 1 := by
      have h4 : Real.pi / 4 + Real.pi / 4 = Real.pi / 2 := by ring
      rw [h4]
      exact Real.sin_pi_div_two
    rw [h1, h3]
    all_goals norm_num