import Mathlib

theorem algebra_138063 (p q : ℝ) :
    (∀ x ∈ Set.Icc 1 5, |x^2 + p * x + q| ≤ 2) ↔ (p, q) = (-6, 7) := by
  constructor
  · -- Assume that the inequality |x ^ 2 + p * x + q| ≤ 2 has no solution in [1, 5]
    intro h
    have h1 := h 1 (Set.left_mem_Icc.mpr (by norm_num))
    have h5 := h 5 (Set.right_mem_Icc.mpr (by norm_num))
    have h3 := h 3 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    have h2 := h 2 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    have h4 := h 4 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    -- this is replace with `linarith` later after remove abs
    have h1_neg : -2 ≤ 1 + p * 1 + q := by linarith [abs_le.mp h1]
    have h1_pos : 1 + p * 1 + q ≤ 2 := by linarith [abs_le.mp h1]
    have h5_neg : -2 ≤ 5 ^ 2 + p * 5 + q := by linarith [abs_le.mp h5]
    have h5_pos : 5 ^ 2 + p * 5 + q ≤ 2 := by linarith [abs_le.mp h5]
    have h3_neg : -2 ≤ 3 ^ 2 + p * 3 + q := by linarith [abs_le.mp h3]
    have h3_pos : 3 ^ 2 + p * 3 + q ≤ 2 := by linarith [abs_le.mp h3]
    have h2_neg : -2 ≤ 2 ^ 2 + p * 2 + q := by linarith [abs_le.mp h2]
    have h2_pos : 2 ^ 2 + p * 2 + q ≤ 2 := by linarith [abs_le.mp h2]
    have h4_neg : -2 ≤ 4 ^ 2 + p * 4 + q := by linarith [abs_le.mp h4]
    have h4_pos : 4 ^ 2 + p * 4 + q ≤ 2 := by linarith [abs_le.mp h4]
    have hp : p = -6 := by 
      nlinarith 
    have hq : q = 7 := by 
      rw [hp] at h1_neg h1_pos h5_neg h5_pos h3_neg h3_pos h2_neg h2_pos h4_neg h4_pos
      nlinarith
    simp [Prod.ext_iff, hp, hq]
  · -- Assume that (p, q) = (-6, 7)
    rintro ⟨rfl, rfl⟩
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have h1 : 1 ≤ x := by linarith
    have h2 : x ≤ 5 := by linarith
    have h3 : -2 ≤ x^2 + (-6) * x + 7 := by
      nlinarith [sq_nonneg (x - 3)]
    have h4 : x^2 + (-6) * x + 7 ≤ 2 := by 
      nlinarith [sq_nonneg (x - 3)]
    have h5 : |x^2 + (-6) * x + 7| ≤ 2 := by 
      apply abs_le.mpr 
      constructor
      · linarith 
      · linarith 
    exact h5