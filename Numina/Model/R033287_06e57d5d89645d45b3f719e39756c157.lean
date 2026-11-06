import Mathlib

open Real Set

lemma lemma_1 (x : ℝ) :
    sqrt 3 / 2 * sin (x + π / 2) + cos (π / 6 - x) =
    sqrt 3 * cos x + 1 / 2 * sin x := by
  have h1 : sin (x + π / 2) = cos x := by
    rw [sin_add_pi_div_two]
  have h2 : cos (π / 6 - x) = cos (π / 6) * cos x + sin (π / 6) * sin x := by
    rw [cos_sub]
  have h3 : cos (π / 6) = sqrt 3 / 2 := by
    rw [cos_pi_div_six]
  have h4 : sin (π / 6) = 1 / 2 := by
    rw [sin_pi_div_six]
  rw [h1, h2, h3, h4]
  ring

theorem algebra_266836 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sqrt 3 / 2 * sin (x + π / 2) + cos (π / 6 - x)) :
  IsGreatest (range f) (sqrt 13 / 2) := by
  have h1 : ∀ x, f x = sqrt 3 * cos x + 1 / 2 * sin x := by
    intro x
    rw [h₀ x]
    rw [lemma_1 x]

  have h2 : sqrt 13 / 2 ∈ range f := by
    use Real.arcsin (1 / Real.sqrt 13)
    rw [h1 (Real.arcsin (1 / Real.sqrt 13))]
    have h3 : Real.sin (Real.arcsin (1 / Real.sqrt 13)) = 1 / Real.sqrt 13 := by
      apply Real.sin_arcsin
      all_goals
        have hx1 : 0 ≤ 1 / Real.sqrt 13 := by
          positivity
        have hx2 : 1 / Real.sqrt 13 ≤ 1 := by
          have h33 : Real.sqrt 13 ≥ Real.sqrt 1 := by
            apply Real.sqrt_le_sqrt
            norm_num
          have h34 : Real.sqrt 1 = (1 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h34] at h33
          have h35 : 0 < Real.sqrt 13 := by
            positivity
          have h36 : (1 / Real.sqrt 13 : ℝ) ≤ (1 : ℝ) := by
            have h77 : Real.sqrt 13 ≥ (1 : ℝ) := by nlinarith [Real.sqrt_nonneg 13, h33]
            have h78 : 0 < Real.sqrt 13 := by positivity
            apply (div_le_iff₀ (by positivity)).mpr
            nlinarith
          linarith
        all_goals
          nlinarith
    have h31 : Real.cos (Real.arcsin (1 / Real.sqrt 13)) = Real.sqrt 3 * (2 / Real.sqrt 13) := by
      have h9 : Real.cos (Real.arcsin (1 / Real.sqrt 13)) = Real.sqrt (1 - (1 / Real.sqrt 13) ^ 2) := by
        rw [Real.cos_arcsin]
      rw [h9]
      have h42 : (1 / Real.sqrt 13) ^ 2 = 1 / (13 : ℝ) := by
        field_simp
      rw [h42]
      have h747 : Real.sqrt (1 - (1 / 13 : ℝ)) = Real.sqrt 3 * (2 / Real.sqrt 13) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num <;> ring_nf <;> norm_num
      rw [h747]

    rw [h3, h31]
    field_simp [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (13 : ℝ), Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ) by norm_num)]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 13, Real.sqrt_nonneg (13 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]

  have h7 : ∀ y ∈ range f, y ≤ sqrt 13 / 2 := by
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h1 x] at hx
    nlinarith [sq_nonneg (sqrt 3 * sin x - 1 / 2 * cos x), Real.sqrt_nonneg 3, Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), Real.cos_sq_add_sin_sq x]

  constructor
  · exact h2
  · intro y hy
    have h9 : y ≤ sqrt 13 / 2 := by
      apply h7 y
      simpa using hy
    linarith