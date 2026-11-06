import Mathlib

open Real

theorem algebra_310123 {x : ℝ} :
    (cosh x)^2 - (sinh x)^2 = 1 ∧
    1 - (tanh x)^2 = (1 / cosh x)^2 ∧
    ∀ y, tanh (x - y) = (tanh x - tanh y) / (1 - tanh x * tanh y) := by
  constructor
  · -- Proof that cosh²x - sinh²x = 1.
    have h1 : (cosh x)^2 - (sinh x)^2 = 1 := by
      exact cosh_sq_sub_sinh_sq x
    exact h1
  constructor
  · -- Proof that 1 - tanh²x = sech²x.
    have h : 1 - (tanh x)^2 = (1 / cosh x)^2 := by
      have htanh : tanh x = (sinh x) / (cosh x) := by
        rw [tanh_eq_sinh_div_cosh]
      rw [htanh]
      have h1 : (cosh x)^2 - (sinh x)^2 = 1 := by
        exact cosh_sq_sub_sinh_sq x
      have hne1 : cosh x ≠ 0 := by
        have h_pos : cosh x ≥ 1 := by
          have h_def : cosh x = (exp x + exp (-x)) / 2 := by
            rw [Real.cosh_eq]
          rw [h_def]
          have h1 : exp x > 0 := exp_pos x
          have h2 : exp (-x) > 0 := exp_pos (-x)
          have h3 : exp x + exp (-x) ≥ 2 := by
            have h4 : exp (-x) = 1 / exp x := by
              rw [exp_neg]
              <;> field_simp
            rw [h4]
            have h5 : exp x + 1 / exp x ≥ 2 := by
              have h6 : exp x + 1 / exp x - 2 ≥ 0 := by
                have h7 : exp x + 1 / exp x - 2 = (exp x - 1) ^ 2 / exp x := by
                  field_simp
                  ring_nf
                rw [h7]
                apply div_nonneg
                nlinarith [sq_nonneg (exp x - 1)]
                positivity
              linarith
            linarith
          have : (exp x + exp (-x)) / 2 ≥ 1 := by
            have h8 : exp x + exp (-x) ≥ 2 := h3
            have h9 : (exp x + exp (-x)) / 2 ≥ (2) / 2 := by
              apply (div_le_div_iff (by norm_num) (by norm_num)).mpr
              linarith
            have h8' : (exp x + exp (-x)) / 2 ≥ 1 := by
              linarith
            linarith
          linarith
          all_goals nlinarith [exp_pos x, exp_pos (-x)]
        have : cosh x ≥ 0 := by linarith [h_pos]
        have : cosh x > 0 := by linarith [h_pos]
        linarith
      field_simp [hne1]
      <;> nlinarith [exp_pos x, exp_pos (-x)]
    exact h
  · -- Proof of tanh(x-y) = ...
    intro y
    have h : tanh (x - y) = (tanh x - tanh y) / (1 - tanh x * tanh y) := by
      have ht1 : tanh (x - y) = (sinh (x - y) / cosh (x - y)) := by
        rw [tanh_eq_sinh_div_cosh]
      have ht2 : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
        rw [sinh_sub]
      have ht3 : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
        rw [cosh_sub]
      rw [ht1, ht2, ht3]
      have ht4 : tanh x = (sinh x / cosh x) := by
        rw [tanh_eq_sinh_div_cosh]
      have ht5 : tanh y = (sinh y / cosh y) := by
        rw [tanh_eq_sinh_div_cosh]
      rw [ht4, ht5]
      have hne1 : cosh x ≠ 0 := by
        have h_pos : cosh x ≥ 1 := by
          have h_def : cosh x = (exp x + exp (-x)) / 2 := by
            rw [Real.cosh_eq]
          rw [h_def]
          have h1 : exp x > 0 := exp_pos x
          have h2 : exp (-x) > 0 := exp_pos (-x)
          have h3 : exp x + exp (-x) ≥ 2 := by
            have h4 : exp (-x) = 1 / exp x := by
              rw [exp_neg]
              <;> field_simp
            rw [h4]
            have h5 : exp x + 1 / exp x ≥ 2 := by
              have h6 : exp x + 1 / exp x - 2 ≥ 0 := by
                have h7 : exp x + 1 / exp x - 2 = (exp x - 1) ^ 2 / exp x := by
                  field_simp
                  ring_nf
                rw [h7]
                apply div_nonneg
                nlinarith [sq_nonneg (exp x - 1)]
                positivity
              linarith
            linarith
          have : (exp x + exp (-x)) / 2 ≥ 1 := by
            have h8 : exp x + exp (-x) ≥ 2 := h3
            have h9 : (exp x + exp (-x)) / 2 ≥ (2) / 2 := by
              apply (div_le_div_iff (by norm_num) (by norm_num)).mpr
              linarith
            have h8' : (exp x + exp (-x)) / 2 ≥ 1 := by
              linarith
            linarith
          all_goals nlinarith [exp_pos x, exp_pos (-x)]
        have : cosh x > 0 := by linarith [h_pos]
        linarith
      have hne2 : cosh y ≠ 0 := by
        have h_pos : cosh y ≥ 1 := by
          have h_def : cosh y = (exp y + exp (-y)) / 2 := by
            rw [Real.cosh_eq]
          rw [h_def]
          have h1 : exp y > 0 := exp_pos y
          have h2 : exp (-y) > 0 := exp_pos (-y)
          have h3 : exp y + exp (-y) ≥ 2 := by
            have h4 : exp (-y) = 1 / exp y := by
              rw [exp_neg]
              <;> field_simp
            rw [h4]
            have h5 : exp y + 1 / exp y ≥ 2 := by
              have h6 : exp y + 1 / exp y - 2 ≥ 0 := by
                have h7 : exp y + 1 / exp y - 2 = (exp y - 1) ^ 2 / exp y := by
                  field_simp
                  ring_nf
                rw [h7]
                apply div_nonneg
                nlinarith [sq_nonneg (exp y - 1)]
                positivity
              linarith
            linarith
          have : (exp y + exp (-y)) / 2 ≥ 1 := by
            have h8 : exp y + exp (-y) ≥ 2 := h3
            have h9 : (exp y + exp (-y)) / 2 ≥ (2) / 2 := by
              apply (div_le_div_iff (by norm_num) (by norm_num)).mpr
              linarith
            have h8' : (exp y + exp (-y)) / 2 ≥ 1 := by
              linarith
            linarith
          all_goals nlinarith [exp_pos y, exp_pos (-y)]
        have : cosh y > 0 := by linarith [h_pos]
        linarith
      field_simp [hne1, hne2]
      <;> ring_nf <;> simp [Real.sinh_eq, Real.cosh_eq] <;> field_simp [hne1, hne2]
      <;> nlinarith [exp_pos x, exp_pos (-x), exp_pos y, exp_pos (-y)]
    exact h