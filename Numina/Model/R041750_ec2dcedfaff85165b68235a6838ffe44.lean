import Mathlib

theorem algebra_10339 (f : ℝ → ℝ) (k : ℝ) (hk : k < 0) (hf : ∀ x, f x = x ^ k) :
    Set.Ioc 0 1 = f ''Set.Ici 1 := by
  ext y
  simp only [hf, Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_image, Set.mem_Ici]
  constructor
  · -- Assume y ∈ (0, 1]
    rintro ⟨hy0, hy1⟩
    use y ^ (1 / k)
    constructor
    · -- Show x ≥ 1
      have h1 : y ^ (1 / k) ≥ 1 := by
        have h61 : k < 0 := by linarith
        have h62 : (1 / k : ℝ) < 0 := by
          apply div_neg_of_pos_of_neg
          all_goals linarith
        have h65 : y ^ (1 / k) = Real.exp ((1 / k) * (Real.log y)) := by
          rw [Real.rpow_def_of_pos]
          all_goals
            try simp [Real.rpow_def_of_pos]
            all_goals
              try nlinarith
        rw [h65]
        have h5 : Real.log y ≤ 0 := by
          have h66 : y ≤ (1 : ℝ) := by linarith
          have h67 : Real.log y ≤ Real.log (1 : ℝ) := by
            apply Real.log_le_log
            all_goals
              try linarith
          have h68 : Real.log (1 : ℝ) = 0 := Real.log_one
          linarith
        have h7 : (1 / k) * (Real.log y) ≥ 0 := by
          have h8 : (1 / k) < 0 := h62
          have h9 : Real.log y ≤ 0 := h5
          nlinarith
        have h71 : Real.exp ((1 / k) * (Real.log y)) ≥ 1 := by
          have h72 : (1 / k) * (Real.log y) ≥ (0 : ℝ) := h7
          have h73 : Real.exp ((1 / k) * (Real.log y)) ≥ Real.exp (0 : ℝ) := by
            apply Real.exp_le_exp_of_le
            all_goals
              linarith
          have h74 : Real.exp (0 : ℝ) = (1 : ℝ) := Real.exp_zero
          linarith
        linarith
      linarith
    · -- Show x ^ k = y
      have h2 : (y ^ (1 / k) : ℝ) ^ k = y := by
        have h65 : (y ^ (1 / k) : ℝ) ^ k = y := by
          have h66 : (y ^ (1 / k) : ℝ) ^ k = y ^ ((1 / k) * k) := by
            rw [← Real.rpow_mul]
            all_goals
              try linarith
          rw [h66]
          have h67 : (1 / k) * k = (1 : ℝ) := by
            field_simp [show k ≠ 0 by linarith]
          rw [h67]
          all_goals
            try simp
          all_goals
            try linarith
        linarith
      linarith
  · -- Assume y ∈ f '' [1, ∞)
    rintro ⟨x, hx, hxy⟩
    constructor
    · -- Show 0 < y
      have hy2 : y > 0 := by
        have h1 : (x : ℝ) ^ k > 0 := by
          positivity
        linarith
      linarith
    · -- Show y ≤ 1
      have h1 : (x : ℝ) ^ k ≤ (1 : ℝ) := by
        have h11 : (1 : ℝ) = (1 : ℝ) := by rfl
        have h12 : (x : ℝ) ≥ (1 : ℝ) := by
          linarith
        have hk1 : k < (0 : ℝ) := by linarith
        have h21 : (x : ℝ) ^ k ≤ (1 : ℝ) ^ k := by
          apply Real.rpow_le_rpow_of_exponent_nonpos
          all_goals
            try linarith
        have h22 : (1 : ℝ) ^ k = (1 : ℝ) := by
          simp [Real.one_rpow]
        nlinarith
      linarith