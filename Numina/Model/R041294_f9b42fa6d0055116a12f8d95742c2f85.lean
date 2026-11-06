import Mathlib

theorem Real.rpow_right_inj : ∀ {x y z : ℝ}, 0 < x → x ≠ 1 → (x ^ y = x ^ z ↔ y = z) := by 
  intro x y z hx hx1
  constructor
  · -- Assume x ^ y = x ^ z, prove y = z
    intro h
    have h1 : y = z := by
      apply_fun (Real.logb x) at h
      simp [hx, hx1] at h ⊢
      <;> linarith
    exact h1
  · -- Assume y = z, prove x ^ y = x ^ z
    intro h
    rw [h]
    all_goals norm_num

open Real

theorem algebra_196050 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x ^ (Real.logb 3 y) + 2 * y ^ (Real.logb 3 x) = 27) (h2 : Real.logb 3 y - Real.logb 3 x = 1) :
    (x = 3 ∧ y = 9) ∨ (x = 1 / 9 ∧ y = 1 / 3) := by
  have h3 : Real.logb 3 y = Real.logb 3 x + 1 := by linarith
  have h4 : y = 3 * x := by
    have h5 : Real.logb 3 y = Real.logb 3 x + 1 := h3
    have h6 : Real.log y = Real.log x + Real.log (3 : ℝ) := by
      have h7 : Real.logb 3 y = Real.logb 3 x + 1 := h3
      have h8 : Real.logb 3 y = Real.log y / Real.log (3 : ℝ) := by
        field_simp [Real.logb]
      have h9 : Real.logb 3 x = Real.log x / Real.log (3 : ℝ) := by
        field_simp [Real.logb]
      rw [h8, h9] at h7
      have h10 : Real.log (3 : ℝ) ≠ 0 := by
        have h5 : Real.log (3 : ℝ) > 0 := by
          apply Real.log_pos
          all_goals linarith
        linarith
      have h11 : Real.log y = Real.log x + Real.log (3 : ℝ) := by
        field_simp [h10] at h7 ⊢
        linarith
      linarith
    have h7 : y = 3 * x := by
      have h8 : Real.log y = Real.log (x * 3) := by 
        rw [h6]
        have : Real.log (x * 3) = Real.log x + Real.log (3 : ℝ) := by
          rw [Real.log_mul (by linarith) (by norm_num)]
        linarith
      have h10 : y > 0 := hy
      have h11 : x * 3 > 0 := by nlinarith
      have h12 : y = x * 3 := by
        apply Real.log_injOn_pos (Set.mem_Ioi.mpr h10) (Set.mem_Ioi.mpr h11) h8
        all_goals
          try { norm_num }
          all_goals try linarith
      nlinarith
    linarith
  have h8 : x ^ (Real.logb 3 y) = x ^ (Real.logb 3 x + 1) := by
    rw [h3]
  have h9 : (3 * x) ^ (Real.logb 3 x : ℝ) = x ^ (1 + Real.logb 3 x : ℝ) := by
    calc
      (3 * x) ^ (Real.logb 3 x : ℝ) = (3 : ℝ) ^ (Real.logb 3 x : ℝ) * x ^ (Real.logb 3 x : ℝ) := by
        rw [show (3 * x : ℝ) = (3 : ℝ) * x by ring]
        rw [Real.mul_rpow]
        all_goals linarith
      _ = (x) * x ^ (Real.logb 3 x : ℝ) := by
        have h11 : (3 : ℝ) ^ (Real.logb 3 x : ℝ) = (x : ℝ) := by
          rw [Real.rpow_logb]
          all_goals try linarith
          all_goals try norm_num
        rw [h11]
        all_goals try linarith
      _ = x ^ (1 : ℝ) * x ^ (Real.logb 3 x : ℝ) := by
        simp
      _ = x ^ (1 + Real.logb 3 x : ℝ) := by 
        rw [← Real.rpow_add]
        ring_nf
        all_goals linarith
  have h1' : x ^ (Real.logb 3 x + 1 : ℝ) + 2 * x ^ (1 + Real.logb 3 x : ℝ) = 27 := by
    have h11 : (3 * x) ^ (Real.logb 3 x : ℝ) = x ^ (1 + Real.logb 3 x : ℝ) := h9
    have eq1 : x ^ (Real.logb 3 y : ℝ) + 2 * y ^ (Real.logb 3 x : ℝ) = 27 := h1
    have eq2 : x ^ (Real.logb 3 y : ℝ) = x ^ (Real.logb 3 x + 1 : ℝ) := by
      rw [h3]
    have eq3 : y ^ (Real.logb 3 x : ℝ) = (3 * x) ^ (Real.logb 3 x : ℝ) := by
      rw [h4]
    rw [eq2, eq3] at eq1
    rw [h11] at eq1
    linarith
  have h12 : (x ^ (1 + Real.logb 3 x : ℝ) : ℝ) = 9 := by
    have eq1 : x ^ (Real.logb 3 x + 1 : ℝ) + 2 * x ^ (1 + Real.logb 3 x : ℝ) = 27 := by linarith [h1']
    have eq2 : x ^ (Real.logb 3 x + 1 : ℝ) = x ^ (1 + Real.logb 3 x : ℝ) := by
      ring_nf
    rw [eq2] at eq1
    nlinarith 
  have h13 : ( (3 : ℝ) ^ ( (Real.logb 3 x) * (1 + Real.logb 3 x) ) ) = (9 : ℝ) := by
    have h14 : x ^ (1 + Real.logb 3 x : ℝ) = ( (3 : ℝ) ^ (Real.logb 3 x : ℝ) ) ^ (1 + Real.logb 3 x : ℝ) := by
      have h15 : x = (3 : ℝ) ^ (Real.logb 3 x : ℝ) := by
        field_simp [Real.rpow_logb, hx.ne.symm]
        all_goals try linarith
        all_goals try norm_num at *
      rw [h15]
      <;> simp [Real.rpow_mul]
      <;> linarith
    rw [h14] at h12
    have h15 : (( (3 : ℝ) ^ (Real.logb 3 x : ℝ) ) ^ (1 + Real.logb 3 x : ℝ) ) = (3 : ℝ) ^ ( (Real.logb 3 x * (1 + Real.logb 3 x) ) : ℝ) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals try linarith
    rw [h15] at h12
    norm_num at h12 ⊢
    linarith
  have h14 : Real.logb 3 x * (1 + Real.logb 3 x) = (2 : ℝ) := by
    have h16 : ( (3 : ℝ) ^ ( Real.logb 3 x * (1 + Real.logb 3 x) ) ) = (9 : ℝ) := h13
    have h17 : Real.logb 3 x * (1 + Real.logb 3 x) = (2 : ℝ) := by
      have h18 : ( (3 : ℝ) ^ ( Real.logb 3 x * (1 + Real.logb 3 x) ) ) = (9 : ℝ) := h16
      have h19 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (Real.logb 3 x * (1 + Real.logb 3 x))) = Real.logb (3 : ℝ) (9 : ℝ) := by
        rw [h18]
      have h20 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (Real.logb 3 x * (1 + Real.logb 3 x))) = Real.logb 3 x * (1 + Real.logb 3 x) := by
        rw [Real.logb_rpow_eq_mul_logb_of_pos]
        all_goals norm_num
      have h21 : Real.logb (3 : ℝ) (9 : ℝ) = (2 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      linarith [h19, h20, h21]
    linarith
  have h12 : (Real.logb 3 x) ^ 2 + (Real.logb 3 x) - 2 = 0 := by
    nlinarith [h14]
  have h13 : (Real.logb 3 x + 2) * (Real.logb 3 x - 1) = 0 := by
    nlinarith [h12]
  cases' (mul_eq_zero.mp h13) with h14 h15
  · -- Real.logb 3 x = -2
    have h17 : Real.logb 3 x = -2 := by linarith
    have h18 : x = (1 / 9 : ℝ) := by
      have h19 : x = (3 : ℝ) ^ (Real.logb 3 x : ℝ) := by
        field_simp [Real.rpow_logb, hx.ne.symm]
        all_goals try linarith
        all_goals try norm_num at *
      rw [h19, h17]
      norm_num
    have h19 : y = (1 / 3 : ℝ) := by
      rw [h4, h18]
      all_goals norm_num
    right
    exact ⟨by linarith, by linarith⟩
  · -- Real.logb 3 x = 1
    have h17 : Real.logb 3 x = (1 : ℝ) := by linarith
    have h18 : x = (3 : ℝ) := by
      have h19 : x = (3 : ℝ) ^ (Real.logb 3 x : ℝ) := by
        field_simp [Real.rpow_logb, hx.ne.symm]
        all_goals try linarith
        all_goals try norm_num at *
      rw [h19, h17]
      norm_num
    have h19 : y = (9 : ℝ) := by
      rw [h4, h18]
      all_goals norm_num
    left
    exact ⟨by linarith, by linarith⟩