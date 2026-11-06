import Mathlib

theorem algebra_141404 (x y : ℝ) (h₀ : 0 ≤ y ∧ y ≤ Real.pi / 2) (h₁ : x + Real.sin y = 2008)
    (h₂ : x + 2008 * Real.cos y = 2007) : x + y = 2007 + Real.pi / 2 := by
  rcases h₀ with ⟨hy1, hy2⟩
  have eq1 : Real.sin y - 2008 * Real.cos y = 1 := by
    nlinarith
  have h4 : Real.sin y ≥ 0 := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    linarith
    linarith [show y ≤ Real.pi by linarith [show y ≤ Real.pi / 2 by linarith, show Real.pi / 2 ≤ Real.pi by linarith [Real.pi_pos]]]
  have h5 : Real.cos y ≥ 0 := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · -- Show that -π/2 ≤ y
      linarith [show y ≥ 0 by linarith, show y ≤ Real.pi by linarith [show y ≤ Real.pi / 2 by linarith, show Real.pi / 2 ≤ Real.pi by linarith [Real.pi_pos]]]
    · -- Show that y ≤ π/2
      linarith [show y ≤ Real.pi / 2 by linarith]
  have h6 : Real.cos y = 0 := by
    nlinarith [sq_nonneg (Real.sin y - 1), sq_nonneg (Real.cos y), 
        Real.sin_sq_add_cos_sq y, h4, h5
      ]
  have h7 : y = Real.pi / 2 := by
    have h8 : Real.cos y = 0 := h6
    by_cases h : y < Real.pi / 2 
    · -- Assume y < Real.pi / 2
      have h11 : Real.cos y > 0 := by
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · -- Show -π/2 < y
          linarith [h, Real.pi_pos]
        · -- Show y < π/2
          linarith [h, Real.pi_pos]
      nlinarith
    · -- Assume y ≥ Real.pi / 2
      have h12 : y ≥ Real.pi / 2 := by linarith
      have h13 : y ≤ Real.pi / 2 := by linarith
      linarith
  have h9 : Real.sin y = 1 := by
    rw [show y = Real.pi / 2 by linarith [h7]]
    norm_num
  have h8 : x = 2007 := by
    linarith [h₁, h9]
  linarith [h8, h7]