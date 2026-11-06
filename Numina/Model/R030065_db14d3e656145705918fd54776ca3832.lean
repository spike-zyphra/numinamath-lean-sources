import Mathlib

theorem algebra_21101 (f : ℝ → ℝ) (hf : ∀ x, f x = (3 / 7) ^ x) :
    f '' Set.Ici 0 = Set.Ioc 0 1 := by
  ext y
  simp [hf, Set.mem_image, Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · -- Assume y in image of [0, ∞)
    rintro ⟨x, hx, rfl⟩
    have hx1 : 0 ≤ x := by linarith
    have h1 : (3 / 7 : ℝ) ^ x > 0 := by
      apply Real.rpow_pos_of_pos
      all_goals norm_num
    have h2 : (3 / 7 : ℝ) ^ x ≤ 1 := by
      have h3 : (3 / 7 : ℝ) ^ x ≤ (3 / 7 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_ge
        all_goals
          try norm_num
          try linarith
      have h4 : (3 / 7 : ℝ) ^ (0 : ℝ) = 1 := by
        simp
      linarith [h3, h4]
    constructor
    · -- Show 0 < (3 / 7 : ℝ) ^ x
      linarith
    · -- Show (3 / 7 : ℝ) ^ x ≤ 1
      linarith
  · -- Assume y ∈ (0, 1]
    rintro ⟨hy1, hy2⟩
    use Real.logb (3 / 7) y
    constructor
    · -- Show 0 ≤ x
      have hx1 : 0 ≤ Real.logb (3 / 7) y := by
        apply Real.logb_nonneg_of_base_lt_one
        all_goals
          try norm_num
          try linarith
      linarith
    · -- Show (3 / 7 : ℝ) ^ (Real.logb (3 / 7) y) = y
      have h_eq : (3 / 7 : ℝ) ^ (Real.logb (3 / 7) y) = y := by
        rw [Real.rpow_logb]
        all_goals
          try norm_num
          try linarith
      linarith [h_eq]