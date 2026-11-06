import Mathlib

theorem algebra_276781 {t : ℝ} (ht : t > 0 ∧ t ≠ 1) (x y : ℝ)
    (hx : x = t ^ ((1 : ℝ) / (t - 1))) (hy : y = t ^ (t / (t - 1))) :
    y ^ x = x ^ y := by 
  rw [hx, hy]
  have ht_pos : t > 0 := ht.left
  have ht_ne_one : t ≠ 1 := ht.right
  have h1 : t ^ (t / (t - 1) : ℝ) = (t ^ ((1 : ℝ) / (t - 1)) ) * t := by
    have h2 : t / (t - 1) = (1 : ℝ) / (t - 1) + 1 := by
      field_simp [(show t - 1 ≠ 0 from by
        intro h'
        apply ht_ne_one
        linarith
      )]
      <;> linarith
    rw [h2]
    have h3 : t ^ ((1 : ℝ) / (t - 1) + (1 : ℝ)) = t ^ ((1 : ℝ) / (t - 1) ) * t ^ (1 : ℝ) := by
      rw [← Real.rpow_add]
      ring_nf
      all_goals linarith [ht_pos]
    rw [h3]
    <;> norm_num
  -- Transform left side
  have h4 : (t ^ (t / (t - 1) : ℝ) ) ^ (t ^ ((1 : ℝ) / (t - 1)) ) = t ^ ((t / (t - 1) ) * (t ^ ((1 : ℝ) / (t - 1)) ) ) := by
    rw [← Real.rpow_mul]
    all_goals
      positivity
  have h5 : (t ^ ((1 : ℝ) / (t - 1)) ) ^ (t ^ (t / (t - 1) : ℝ) ) = t ^ ((1 / (t - 1) ) * (t ^ (t / (t - 1) ) ) ) := by
    rw [← Real.rpow_mul]
    all_goals
      positivity
  rw [h4, h5]
  -- Prove the exponents equal
  have h6 : (t / (t - 1) : ℝ) * (t ^ ((1 : ℝ) / (t - 1)) ) = (1 / (t - 1) : ℝ) * (t ^ (t / (t - 1) : ℝ) ) := by
    rw [h1]
    field_simp [(show t - 1 ≠ 0 by
      intro h'
      apply ht_ne_one
      linarith
    )]
    <;> ring_nf
  rw [h6]
  all_goals norm_num