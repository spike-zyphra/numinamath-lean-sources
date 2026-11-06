import Mathlib

open Real Set
open scoped Real

theorem inequalities_327259 (p q : ℝ) :
  (∀ θ ∈ Icc 0 (π/2), |sin θ - p * cos θ - q| ≤ (sqrt 2 - 1)/2) ↔
  (p = -1 ∧ q = (1 + sqrt 2)/2) := by
  constructor
  · -- Assume the inequality holds for all θ in [0, π/2], prove (p, q) = (-1, (1 + sqrt 2)/2).
    intro h
    have h1 := h (Real.pi / 4) (by
      constructor
      · -- Show that 0 ≤ π/4
        linarith [Real.pi_pos]
      · -- Show that π/4 ≤ π/2
        linarith [Real.pi_pos]
    )
    have h2 := h 0 (by
      constructor
      · -- Show that 0 ≤ 0
        linarith
      · -- Show that 0 ≤ π/2
        linarith [Real.pi_pos]
    )
    have h3 := h (Real.pi / 2) (by
      constructor
      · -- Show that 0 ≤ π/2
        linarith [Real.pi_pos]
      · -- Show that π/2 ≤ π/2
        linarith
    )
    have h1' : |sin (Real.pi / 4) - p * cos (Real.pi / 4) - q| ≤ (sqrt 2 - 1)/2 := by linarith
    have h11 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h12 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    rw [h11, h12] at h1'
    have h2' : |sin (0 : ℝ) - p * cos (0 : ℝ) - q| ≤ (sqrt 2 - 1)/2 := by linarith
    have h21 : sin (0 : ℝ) = 0 := by
      simp
    have h22 : cos (0 : ℝ) = 1 := by
      simp
    rw [h21, h22] at h2'
    have h3' : |sin (Real.pi / 2 : ℝ) - p * cos (Real.pi / 2 : ℝ) - q| ≤ (sqrt 2 - 1)/2 := by linarith
    have h31 : sin (Real.pi / 2 : ℝ) = 1 := by
      rw [sin_pi_div_two]
    have h32 : cos (Real.pi / 2 : ℝ) = 0 := by
      rw [cos_pi_div_two]
    rw [h31, h32] at h3'
    -- Convert absolute value inequality to double-sided inequalities.
    have h1_a : - (sqrt 2 - 1) / 2 ≤ Real.sqrt 2 / 2 * (1 - p) - q := by
      linarith [abs_le.mp h1']
    have h1_b : Real.sqrt 2 / 2 * (1 - p) - q ≤ (sqrt 2 - 1) / 2 := by
      linarith [abs_le.mp h1']
    -- Convert absolute value inequality to double-sided inequalities.
    have h2_a : - (sqrt 2 - 1) / 2 ≤ -p - q := by
      linarith [abs_le.mp h2']
    have h2_b : -p - q ≤ (sqrt 2 - 1) / 2 := by
      linarith [abs_le.mp h2']
    -- Convert absolute value inequality to double-sided inequalities.
    have h3_a : - (sqrt 2 - 1) / 2 ≤ 1 - q := by
      linarith [abs_le.mp h3']
    have h3_b : 1 - q ≤ (sqrt 2 - 1) / 2 := by
      linarith [abs_le.mp h3']
    -- Solve the system of inequalities.
    have h16 : p = -1 := by
      nlinarith [Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by linarith),
                  Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by linarith), Real.sqrt_nonneg 2]
    have h17 : q = (1 + sqrt 2)/2 := by
      nlinarith [Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by linarith),
                  Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by linarith), Real.sqrt_nonneg 2]
    constructor
    · linarith
    · linarith
  · -- Assume (p, q) = (-1, (1 + sqrt 2)/2), prove the inequality holds for all θ in [0, π/2]
    intro h θ hθ
    rcases h with ⟨hp, hq⟩
    have h1 : θ ≥ 0 := by
      have h1 : θ ∈ Icc (0 : ℝ) (Real.pi / 2) := hθ
      simp at h1 ⊢
      linarith [Real.pi_pos]
    have h2 : θ ≤ Real.pi / 2 := by
      have h2 : θ ∈ Icc (0 : ℝ) (Real.pi / 2) := hθ
      simp at h2 ⊢
      linarith [Real.pi_pos]
    have h3 : sin θ ≥ 0 := by apply sin_nonneg_of_nonneg_of_le_pi; linarith [Real.pi_pos, h1, h2]; linarith [Real.pi_pos, h1, h2]
    have h4 : cos θ ≥ 0 := by apply cos_nonneg_of_mem_Icc; constructor; linarith [Real.pi_pos, h1, h2]; linarith [Real.pi_pos, h1, h2]
    have h5 : sin θ - p * cos θ - q = sin θ + cos θ - (1 + Real.sqrt 2)/2 := by
      rw [hp, hq]
      ring
    rw [h5]
    have h18 : 1 ≤ sin θ + cos θ := by
      have h20 : sin θ ^ 2 + cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
      nlinarith [sq_nonneg (sin θ - cos θ), sq_nonneg (sin θ + cos θ - 1), sq_nonneg (sin θ + cos θ - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by linarith)]
    have h19 : sin θ + cos θ ≤ Real.sqrt 2 := by
      have h20 : (sin θ + cos θ) ^ 2 ≤ 2 := by
        have h20 : (sin θ + cos θ) ^ 2 = 1 + 2 * (sin θ * cos θ) := by
          nlinarith [Real.sin_sq_add_cos_sq θ]
        have h22 : sin θ * cos θ ≤ 1 / 2 := by
          have h21 : sin (2 * θ) = 2 * sin θ * cos θ := by
            rw [sin_two_mul]
          have h23 : sin (2 * θ) ≤ 1 := by
            apply Real.sin_le_one
          have h24 : sin (2 * θ) ≥ -1 := by
            linarith [Real.neg_one_le_sin (2 * θ), Real.sin_le_one (2 * θ)]
          nlinarith
        nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (sin θ - cos θ)]
      have h18 : (sin θ + cos θ) ≤ Real.sqrt 2 := by
        have h19 : (sin θ + cos θ) ^ 2 ≤ (2 : ℝ) := by linarith
        have h20 : (sin θ + cos θ) ≤ Real.sqrt 2 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by linarith)]
        linarith
      linarith
    have h14 : - (sqrt 2 - 1)/2 ≤ sin θ + cos θ - (1 + Real.sqrt 2)/2 := by
      nlinarith [Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by linarith)]
    have h15 : sin θ + cos θ - (1 + Real.sqrt 2)/2 ≤ (sqrt 2 - 1)/2 := by
      nlinarith [Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by linarith)]
    apply abs_le.mpr
    constructor <;> linarith [h14, h15]