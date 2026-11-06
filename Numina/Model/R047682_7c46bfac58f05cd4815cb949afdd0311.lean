import Mathlib

theorem algebra_192640 {a b c d : ℝ}
    (ha : a = Real.logb 5 ((125 * 625) / 25)) (h : (r + 1 / r) ^ 2 = a - 2)
    (hb : r ^ 3 + 1 / r ^ 3 = b) (hc : 2 ^ 3 + c * 2 + 10 = b) (hd : 9 ^ (d + 2) = (6489 + c) + 9 ^ d) :
    a = 5 ∧ b = 0 ∧ c = -9 ∧ d = 2 := by
  have ha2 : a = 5 := by
    rw [ha]
    have h1 : (125 * 625 : ℝ) / 25 = (3125 : ℝ) := by norm_num
    rw [h1]
    have h2 : Real.logb 5 ((3125 : ℝ)) = 5 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    linarith
  have h1 : (r + 1 / r) ^ 2 = 3 := by
    rw [ha2] at h
    linarith
  have h2 : r ^ 2 + 1 / r ^ 2 = 1 := by
    have : r ≠ 0 := by
      by_contra h3
      rw [h3] at h1
      norm_num at h1
    have h1' : r ^ 2 + 2 + 1 / r ^ 2 = 3 := by 
      have h' : (r + 1 / r) ^ 2 = r ^ 2 + 2 + 1 / r ^ 2 := by 
        field_simp [(show r ≠ 0 by assumption)]
        <;> ring
      rw [h'] at h1
      linarith
    have : r ^ 2 + 1 / r ^ 2 = 1 := by
      linarith
    assumption
  have h3 : r ^ 3 + 1 / r ^ 3 = 0 := by
    have h4 : r ^ 3 + 1 / r ^ 3 = (r + 1 / r) * (r ^ 2 - 1 + 1 / r ^ 2) := by
      field_simp [(show r ≠ 0 from by
        by_contra h3
        rw [h3] at h1
        norm_num at h1
      )]
      <;> ring
    have h5 : r ^ 2 - 1 + 1 / r ^ 2 = 0 := by
      have h6 : r ^ 2 + 1 / r ^ 2 = 1 := h2
      have h7 : r ^ 2 - 1 + 1 / r ^ 2 = (r ^ 2 + 1 / r ^ 2) - 1 := by 
        field_simp [(show r ≠ 0 from by
          by_contra h3
          rw [h3] at h1
          norm_num at h1
        )]
        <;> ring
      rw [h7, h6]
      all_goals norm_num
    rw [h4, h5]
    <;> norm_num
  have hb2 : b = 0 := by 
    linarith [hb, h3]
  have hc2 : c = -9 := by
    rw [hb2] at hc
    nlinarith
  have h5 : d = (2 : ℝ) := by
    rw [hc2] at hd
    norm_num at hd
    have h80 : (9 : ℝ) ^ (d + 2 : ℝ) = (81 : ℝ) * (9 : ℝ) ^ d := by
      have h81 : (81 : ℝ) = (9 : ℝ) ^ (2 : ℝ) := by
        norm_num
      have eq1 : (9 : ℝ) ^ (d + 2 : ℝ) = (9 : ℝ) ^ (d : ℝ) * (9 : ℝ) ^ (2 : ℝ) := by
        rw [show d + 2 = d + (2 : ℝ) by ring]
        rw [← Real.rpow_add]
        ring_nf
        all_goals norm_num
      rw [eq1]
      rw [h81]
      <;> ring_nf <;> norm_num
      all_goals norm_num
    have h81 : (9 : ℝ) ^ (d + 2 : ℝ) = (6480 : ℝ) + (9 : ℝ) ^ d := by
      linarith
    -- Now need to solve 9^d = 81.
    have heq : (9 : ℝ) ^ d = (81 : ℝ) := by
      nlinarith [h80, h81]
    have h9 : (81 : ℝ) = (9 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [h9] at heq
    have h10 : d = (2 : ℝ) := by
      have h82 : (9 : ℝ) ^ (d : ℝ) = (9 : ℝ) ^ (2 : ℝ) := heq
      have h83 : d = (2 : ℝ) := by
        apply_fun (Real.logb (9 : ℝ)) at h82
        have h11 : Real.logb (9 : ℝ) ((9 : ℝ) ^ (d : ℝ)) = Real.logb (9 : ℝ) ((9 : ℝ) ^ (2 : ℝ)) := by linarith [h82]
        have h12 : Real.logb (9 : ℝ) ((9 : ℝ) ^ (d : ℝ)) = d := by
          rw [Real.logb_rpow]
          all_goals norm_num
        have h13 : Real.logb (9 : ℝ) ((9 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) := by
          rw [Real.logb_rpow]
          all_goals norm_num
        linarith [h12, h13, h11]
      exact_mod_cast h83
    assumption
  have ha4 : a = 5 := ha2
  have hb4 : b = 0 := hb2
  have hc4 : c = -9 := hc2
  have hd2 : d = (2 : ℝ) := h5
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩