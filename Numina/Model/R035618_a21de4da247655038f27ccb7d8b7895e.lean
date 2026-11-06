import Mathlib

open Real

theorem inequalities_241100 (x y : ℝ) :
  x^4 / 2016 ≤ sin (x^2 - 5 * y) - 1 ↔
  ∃ k : ℤ, (x = 0 ∧ y = -π/10 - 2*k*π/5)
  := by
  constructor
  · -- Assume x^4 / 2016 ≤ sin (x^2 - 5 * y) - 1, prove ∃ k : ℤ, (x = 0 ∧ y = -π/10 - 2*k*π/5)
    intro h
    have h1 : sin (x^2 - 5 * y) ≤ 1 := by
      apply sin_le_one
    have h2 : x^4 ≥ 0 := by
      positivity
    have h3 : x^4 / 2016 ≥ 0 := by
      positivity
    have h4 : sin (x^2 - 5 * y) = 1 := by
      nlinarith
    have h5 : x^4 = 0 := by
      nlinarith [Real.sin_le_one (x ^ 2 - 5 * y)]
    have hx0 : x = 0 := by
      have h6 : x^4 = 0 := h5
      simp at h6 ⊢
      all_goals
      linarith
    rw [show x = 0 by linarith [hx0]] at h4
    have h7 : sin (-5 * y) = 1 := by
      have h8 : sin (0 ^ 2 - 5 * y) = 1 := by
        simpa using h4
      have h9 : (0 : ℝ) ^ 2 - 5 * y = -5 * y := by
        ring
      rw [h9] at h8
      linarith
    have h8 : ∃ k : ℤ, -5 * y = Real.pi / 2 + 2 * k * Real.pi := by
      rw [sin_eq_one_iff] at h7
      rcases h7 with ⟨k, hk⟩
      refine ⟨k, by linarith [hk]⟩
    rcases h8 with ⟨k, hk⟩
    have hy : y = -Real.pi / 10 - 2 * k * Real.pi / 5 := by
      have eq1 : -5 * y = Real.pi / 2 + 2 * k * Real.pi := by
        linarith
      linarith [eq1]
    refine ⟨k, ?_⟩
    constructor
    · -- x = 0
      exact hx0
    · -- y = -π/10 - 2*k*π/5
      linarith [hy]
  · -- Assume ∃ k : ℤ, (x = 0 ∧ y = -π/10 - 2*k*π/5), prove x^4 / 2016 ≤ sin (x^2 - 5 * y) - 1
    rintro ⟨k, ⟨hx0, hy⟩⟩
    have hx4 : x^4 = 0 := by
      rw [show x = (0 : ℝ) by linarith [hx0]]
      norm_num
    have h10 : x^2 - 5 * y = Real.pi / 2 + 2 * k * Real.pi := by
      have h11 : x = 0 := by linarith [hx0]
      have h12 : y = -Real.pi / 10 - 2 * k * Real.pi / 5 := by
        linarith [hy]
      rw [h11, h12]
      ring_nf
    have h13 : sin (x^2 - 5 * y) = 1 := by
      rw [h10]
      have h14 : sin (Real.pi / 2 + 2 * k * Real.pi) = 1 := by
        have h15 : sin (Real.pi / 2 + 2 * k * Real.pi) = sin (Real.pi / 2) := by
          have h16 : Real.pi / 2 + 2 * k * Real.pi = Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := by ring
          rw [h16]
          rw [Real.sin_add_int_mul_two_pi]
        rw [h15]
        rw [Real.sin_pi_div_two]
      linarith [h14]
    have h18 : sin (x^2 - 5 * y) - 1 = 0 := by
      linarith [h13]
    rw [show x ^ 4 / 2016 = (0 : ℝ) by linarith [hx4]]
    linarith [h18]