import Mathlib

open Real Set
open scoped Real

theorem algebra_152650 (f : ℝ → ℝ) (hf : f = λ x => sin x - 1 / 2 * cos x) :
    IsGreatest (range f) (Real.sqrt 5 / 2) := by
  have h1 : ∀ x, f x = sin x - 1 / 2 * cos x := by
    intro x
    rw [hf]

  constructor
  · -- Show that sqrt(5)/2 is in the range of f
    use Real.pi - Real.arcsin (2 * Real.sqrt 5 / 5)
    have h2 : sin (Real.pi - Real.arcsin (2 * Real.sqrt 5 / 5)) = 2 * Real.sqrt 5 / 5 := by
      rw [sin_pi_sub]
      rw [Real.sin_arcsin]
      · -- Show that 2*sqrt(5)/5 ≤ 1
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
      · -- Show that -1 ≤ 2*sqrt(5)/5
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
    have h3 : cos (Real.pi - Real.arcsin (2 * Real.sqrt 5 / 5)) = - Real.sqrt 5 / 5 := by
      have h4 : cos (Real.pi - Real.arcsin (2 * Real.sqrt 5 / 5)) = - cos (Real.arcsin (2 * Real.sqrt 5 / 5)) := by
        rw [cos_pi_sub]
      rw [h4]
      have h5 : cos (Real.arcsin (2 * Real.sqrt 5 / 5)) = Real.sqrt 5 / 5 := by
        rw [Real.cos_arcsin]
        have h6 : (2 * Real.sqrt 5 / 5) ^ 2 ≤ 1 := by
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
        have h7 : Real.sqrt (1 - (2 * Real.sqrt 5 / 5) ^ 2) = Real.sqrt 5 / 5 := by
          rw [show (1 - (2 * Real.sqrt 5 / 5) ^ 2 : ℝ) = (1 / 5 : ℝ) by
            nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
          ]
          have h8 : Real.sqrt (1 / 5 : ℝ) = Real.sqrt 5 / 5 := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
            <;> ring_nf
            <;> norm_num
          linarith
        linarith
      linarith
    have h9 : f (Real.pi - Real.arcsin (2 * Real.sqrt 5 / 5)) = Real.sqrt 5 / 2 := by
      rw [h1]
      simp [h2, h3]
      all_goals
        ring_nf
        <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
    linarith
  · -- Show that sqrt(5)/2 is the greatest element in the range
    intro y
    rintro ⟨x, hx⟩
    rw [h1] at hx
    have h10 : sin x - 1 / 2 * cos x ≤ Real.sqrt 5 / 2 := by
      nlinarith [sq_nonneg (sin x - 2 * Real.sqrt 5 / 5), sq_nonneg (cos x + Real.sqrt 5 / 5), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith), Real.sin_sq_add_cos_sq x]
    linarith [h10, hx]