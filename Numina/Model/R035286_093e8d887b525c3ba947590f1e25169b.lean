import Mathlib
open Real
theorem inequalities_61617 (a : ℝ) (ha : 0 < a) (h : ∃ x y z : ℝ, a ^ x + a ^ y + a ^ z = 14 - a ∧ x + y + z = 1) : a ≤ 8 := by
  rcases h with ⟨x, y, z, heq1, heq2⟩
  have h1 : a ^ x > 0 := by positivity
  have h2 : a ^ y > 0 := by positivity
  have h3 : a ^ z > 0 := by positivity

  have h4 : a ^ x + a ^ y + a ^ z ≥ 3 * ( (a ^ x * (a ^ y) * (a ^ z)) ) ^ (1 / 3 : ℝ) := by
    have h112 : ( (a ^ x) * (a ^ y) * (a ^ z) ) ^ (1 / 3 : ℝ) ≤ ( (a ^ x + a ^ y + a ^ z ) ) / 3 := by
      have h111 : ( (a ^ x) * (a ^ y) * (a ^ z) ) ^ (1 / 3 : ℝ) =
          ( (a ^ x) ) ^ (1 / 3 : ℝ) * ( (a ^ y) ) ^ (1 / 3 : ℝ) * ( (a ^ z) ) ^ (1 / 3 : ℝ) := by
        rw [← Real.mul_rpow, ← Real.mul_rpow]
        all_goals
          positivity
      rw [h111]
      have h115 : ( (a ^ x) ) ^ (1 / 3 : ℝ) * ( (a ^ y) ) ^ (1 / 3 : ℝ) * ( (a ^ z) ) ^ (1 / 3 : ℝ) ≤ ( (a ^ x + a ^ y + a ^ z ) ) / 3 := by
        have h116 : ( (a ^ x) ) ^ (1 / 3 : ℝ) * ( (a ^ y) ) ^ (1 / 3 : ℝ) * ( (a ^ z) ) ^ (1 / 3 : ℝ) ≤ (1 / 3 : ℝ) * (a ^ x) + (1 / 3 : ℝ) * (a ^ y) + (1 / 3 : ℝ) * (a ^ z) := by
          have h117 : ( (a ^ x) ) ^ (1 / 3 : ℝ) * ( (a ^ y) ) ^ (1 / 3 : ℝ) * ( (a ^ z) ) ^ (1 / 3 : ℝ) ≤ (1 / 3 : ℝ) * (a ^ x) + (1 / 3 : ℝ) * (a ^ y) + (1 / 3 : ℝ) * (a ^ z) := by
            apply Real.geom_mean_le_arith_mean3_weighted
            all_goals
              try { positivity }
              try { norm_num  }
          linarith
        have h118 : ( (1 / 3 : ℝ) * (a ^ x) + (1 / 3 : ℝ) * (a ^ y) + (1 / 3 : ℝ) * (a ^ z) ) = ( (a ^ x + a ^ y + a ^ z ) ) / 3 := by
          ring
        linarith
      linarith
    have h114 : ( (a ^ x * (a ^ y) * (a ^ z) ) ) ^ (1 / 3 : ℝ) ≤ ( (a ^ x + a ^ y + a ^ z ) ) / 3 := h112
    nlinarith

  have h23 : (a ^ x * (a ^ y) * (a ^ z)) = a := by
    have h5 : a ^ x * (a ^ y) * (a ^ z) = a ^ (1 : ℝ) := by
      have h6 : a ^ x * (a ^ y) * (a ^ z) = a ^ (x + y + z : ℝ) := by
        rw [← Real.rpow_add, ← Real.rpow_add]
        ring_nf
        all_goals
          linarith
      rw [h6, heq2]
      all_goals
        norm_num
    rw [h5]
    all_goals
      norm_num

  rw [h23] at h4

  by_contra h9
  push_neg at h9
  have h10 : a > 8 := by
    linarith
  have h11 : a ^ (1 / 3 : ℝ) > 2 := by
    have h13 : (8 : ℝ) < a := by
      linarith
    have h14 : (8 : ℝ) ^ (1 / 3 : ℝ) < a ^ (1 / 3 : ℝ) := by
      apply Real.rpow_lt_rpow
      ·
        norm_num
      ·
        nlinarith
      all_goals
        norm_num
    have h15 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
      have h17 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
      rw [h17]
      rw [← Real.rpow_mul]
      norm_num
      all_goals
        positivity
    nlinarith


  have h111 : a ^ x + a ^ y + a ^ z < 6 := by
    have h112 : 14 - a < 6 := by
      nlinarith
    nlinarith [ heq1 ]

  have h115 : 3 * a ^ (1 / 3 : ℝ) ≥ 6 := by
    have h113 : a ^ (1 / 3 : ℝ) ≥ 2 := by
      have h112 : (8 : ℝ) ≤ a := by
        linarith
      have h117 : a ^ (1 / 3 : ℝ) ≥ (8 : ℝ) ^ (1 / 3 : ℝ) := by
        apply Real.rpow_le_rpow
        ·
          linarith
        ·
          linarith
        all_goals
          norm_num
      have h114 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
        have h115 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
          have h117 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
          rw [h117]
          rw [← Real.rpow_mul]
          norm_num
          all_goals
            positivity
        linarith
      nlinarith
    nlinarith

  nlinarith