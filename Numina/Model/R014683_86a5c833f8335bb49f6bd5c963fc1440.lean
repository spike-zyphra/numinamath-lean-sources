import Mathlib

open Real Set
open scoped Real

theorem algebra_212871 : IsGreatest {x | ∃ θ, x = sin (θ / 2) * (1 + cos θ)} (4 * sqrt 3 / 9) := by
  constructor
  · -- Show that $4\sqrt{3}/9$ is in the set.
    use 2 * (Real.arcsin (Real.sqrt 3 / 3))
    have h1 : sin ((2 * (Real.arcsin (Real.sqrt 3 / 3)) ) / 2) = Real.sqrt 3 / 3 := by
      have h2 : (2 * (Real.arcsin (Real.sqrt 3 / 3)) ) / 2 = Real.arcsin (Real.sqrt 3 / 3) := by ring
      rw [h2]
      rw [Real.sin_arcsin]
      · -- show sqrt 3 / 3 >= 0
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0: ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      · -- show sqrt 3 / 3 <= 1
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h2 : cos (2 * (Real.arcsin (Real.sqrt 3 / 3)) ) = 1 / 3 := by
      have h3 : cos (2 * (Real.arcsin (Real.sqrt 3 / 3)) ) = 1 - 2 * (sin (Real.arcsin (Real.sqrt 3 / 3)) ) ^ 2 := by
        rw [cos_two_mul, sin_sq]
        <;> ring
      have h4 : sin (Real.arcsin (Real.sqrt 3 / 3)) = Real.sqrt 3 / 3 := by
        apply Real.sin_arcsin
        · -- Show sqrt 3 / 3 ≥ 0
          nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        · -- Show sqrt 3 / 3 ≤ 1
          nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h5 : (sin (Real.arcsin (Real.sqrt 3 / 3)) ) ^ 2 = (Real.sqrt 3 / 3) ^ 2 := by
        rw [h4]
      rw [h3, h4]
      have h6 : (Real.sqrt 3 / 3 : ℝ) ^ 2 = 1 / 3 := by
        calc
          (Real.sqrt 3 / 3 : ℝ) ^ 2 = (Real.sqrt 3) ^ 2 / 9 := by ring
          _ = 3 / 9 := by rw [Real.sq_sqrt]; linarith
          _ = 1 / 3 := by norm_num
      nlinarith [h6, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
    rw [h1, h2]
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
  · -- Show that $4\sqrt{3}/9$ is greatest in the set.
    intro x hx
    rcases hx with ⟨θ, hθ⟩
    have h1 : sin θ = 2 * sin (θ / 2) * cos (θ / 2) := by
      rw [← Real.sin_two_mul]
      ring_nf
    have h2 : cos θ = 2 * cos (θ / 2) ^ 2 - 1 := by
      rw [← Real.cos_two_mul]
      ring_nf
    have h5 : sin (θ / 2) * (1 + cos θ) = 2 * sin (θ / 2) * cos (θ / 2) ^ 2 := by
      rw [h2]
      have h5a : sin (θ / 2) * (1 + (2 * cos (θ / 2) ^ 2 - 1)) = 2 * sin (θ / 2) * cos (θ / 2) ^ 2 := by
        nlinarith
      linarith [h5a]
    have h6 : sin (θ / 2) ^ 2 + cos (θ / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (θ / 2)
    by_cases h3 : sin (θ / 2) ≥ 0
    · -- Assume sin (θ / 2) ≥ 0
      have h8 : sin (θ / 2) * (1 + cos θ) = sin (θ / 2) * (1 + (1 - 2 * sin (θ / 2) ^ 2)) := by
        rw [h2]
        all_goals nlinarith [Real.sin_sq_add_cos_sq θ]
      have h9 : sin (θ / 2) * (1 + cos θ) = 2 * sin (θ / 2) * (1 - sin (θ / 2) ^ 2) := by
        rw [h8]
        ring
      have h10 : sin (θ / 2) ≥ 0 := by linarith
      have h11 : sin (θ / 2) ≤ 1 := by 
        apply sin_le_one
      nlinarith [sq_nonneg (sin (θ / 2) ^ 2 - 1 / 3), sq_nonneg (sin (θ / 2) - Real.sqrt 3 / 3), sq_nonneg (sin (θ / 2) + Real.sqrt 3 / 3), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (sin (θ / 2) ^ 2 - 1 / 3), sq_nonneg (sin (θ / 2) * (sin (θ / 2) ^ 2 * 3 * 3 - 1 * 1 * 1)), h10, h11]
    · -- Assume sin (θ / 2) < 0
      have h4 : sin (θ / 2) ≤ 0 := by linarith
      have h5 : sin (θ / 2) * (1 + cos θ) ≤ 0 := by 
        nlinarith [sq_nonneg (1 + cos θ), show sin (θ / 2) ≤ 0 by nlinarith, Real.sin_sq_add_cos_sq θ, sq_nonneg (sin (θ / 2)), sq_nonneg (cos θ + 1), sq_nonneg (sin (θ / 2) + 1)]
      have h6 : 4 * Real.sqrt 3 / 9 > 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
      nlinarith