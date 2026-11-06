import Mathlib

theorem algebra_15490  :
    {k : ℝ| ∃ a b c, a + b + c = 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ k = (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c)} = {3} := by
  ext k 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume k is in the first set; prove it's in the singleton {3}
    rintro ⟨a, b, c, h1, ha, hb, hc, hk⟩
    have h2 : a ^ 3 + b ^ 3 + c ^ 3 = 3 * (a * b * c) := by
      have h4 : a + b + c = 0 := h1
      have h5 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + a * c + b * c)) := by
        ring 
      rw [h4] at h5
      have h6 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = 0 := by
        linarith
      linarith
    have hk2 : (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) = 3 := by
      have h7 : a * b * c ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        exact ha 
        exact hb 
        exact hc 
      have h8 : a ^ 3 + b ^ 3 + c ^ 3 = 3 * (a * b * c) := h2 
      rw [h8]
      have h10 : (a * b * c) ≠ 0 := h7
      field_simp [h10]
      <;> nlinarith 
    rw [hk]
    linarith
  · -- Assume k = 3; prove it's in the first set
    intro hk
    rw [hk]
    use 1, 2, -3
    constructor
    · norm_num 
    constructor
    · norm_num
    constructor 
    · norm_num 
    constructor
    · norm_num 
    · norm_num