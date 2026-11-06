import Mathlib

theorem algebra_155992 (a : ℝ) (ha : a > 0) (f : ℝ → ℝ)
    (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x, f x = 1 / a - 1 / (a ^ x + 1)) :
    Set.range f = Set.Ioo (-1 / 2) (1 / 2) := by
  -- First determine the value of a
  have ha2 : a = 2 := by 
    have h1 := hodd 0
    simp [hf] at h1
    field_simp at h1 
    nlinarith 
  -- Now determine the form of f(x)
  have hfx : ∀ x, f x = 1 / 2 - 1 / (2 ^ x + 1) := by
    intro x 
    rw [hf x]
    rw [ha2]
  -- Now prove the range
  ext y
  simp only [Set.mem_range, Set.mem_setOf_eq, Set.mem_Ioo]
  constructor 
  · -- Assume y ∈ range f 
    rintro ⟨x, hx⟩ 
    rw [hfx x] at hx 
    have h1 : (2 : ℝ) ^ x > 0 := by positivity 
    have h2 : 0 < (2 : ℝ) ^ x + 1 := by 
      linarith 
    have h3 : -1 / 2 < 1 / 2 - 1 / ((2 : ℝ) ^ x + 1) := by 
      have h4 : 1 / ((2 : ℝ) ^ x + 1) < 1 := by 
        apply (div_lt_iff₀ (by linarith)).mpr 
        linarith 
      linarith 
    have h4 : 1 / 2 - 1 / ((2 : ℝ) ^ x + 1) < 1 / 2 := by 
      have h5 : 0 < 1 / ((2 : ℝ) ^ x + 1) := by 
        apply div_pos 
        norm_num 
        all_goals 
          positivity 
      linarith 
    constructor <;> 
    linarith 
  · -- Assume y ∈ (-1/2, 1/2)
    rintro ⟨hy1, hy2⟩
    use Real.logb (2 : ℝ) ((1 + 2 * y) / (1 - 2 * y))
    rw [hfx]
    have h5 : (2 : ℝ) ^ (Real.logb (2 : ℝ) ((1 + 2 * y) / (1 - 2 * y))) = (1 + 2 * y) / (1 - 2 * y) := by
      rw [Real.rpow_logb]
      all_goals 
        have h1 : (1 - 2 * y) > 0 := by linarith
        have h2 : (1 + 2 * y) > 0 := by linarith 
        have h3 : (1 + 2 * y) / (1 - 2 * y) > 0 := by 
          apply div_pos 
          <;> linarith 
        all_goals 
          nlinarith 
    rw [h5]
    field_simp [show (1 - 2 * y) ≠ 0 by linarith]
    <;> 
      ring_nf <;> 
      field_simp <;> 
      nlinarith