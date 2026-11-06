import Mathlib

theorem algebra_193148 {A B : ℝ} (hA : 100 * A = 35 ^ 2 - 15 ^ 2) (hB : (A - 1) ^ 6 = 27 ^ B) :
    A = 10 ∧ B = 4 := by
  have hA1 : A = 10 := by
    nlinarith
  have hB1 : B = 4 := by
    rw [show A = 10 by linarith [hA1]] at hB
    have h1 : ( ( (10 : ℝ) - 1 ) ^ 6 ) = ( 27 : ℝ ) ^ ( B ) := by
      linarith [ hB ]
    have h2 : ( (10 : ℝ) - 1 ) ^ 6 = (3 : ℝ) ^ (12 : ℝ) := by norm_num
    have h3 : (27 : ℝ) ^ B = (3 : ℝ) ^ (3 * B : ℝ) := by
      have h4 : (27 : ℝ) ^ B = (3 ^ (3 : ℝ)) ^ B := by
        norm_num
      rw [h4]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h2] at h1
    rw [h3] at h1
    have h4 : (3 : ℝ) ^ (12 : ℝ) = (3 : ℝ) ^ (3 * B : ℝ) := by linarith [ h1 ]
    have h5 : (12 : ℝ) = (3 * B : ℝ) := by
      apply_fun (Real.logb (3 : ℝ)) at h4
      simp at h4 ⊢
      all_goals linarith [ h4 ]
    linarith [ h5 ]
  exact ⟨hA1, hB1⟩