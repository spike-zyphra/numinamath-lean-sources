import Mathlib

theorem algebra_9047 : {k | k ≠ 0 ∧ ∃ x₁ x₂ : ℝ,
    k * x₁ ^ 2 - 6 * x₁ + 9 = 0 ∧ k * x₂ ^ 2 - 6 * x₂ + 9 = 0 ∧ x₁ ≠ x₂} = {k | k < 1 ∧ k ≠ 0} := by 
  ext k
  simp only [Set.mem_setOf_eq, and_imp]
  constructor
  · -- Assuming the existence of distinct roots, proving k < 1 and k ≠ 0
    rintro ⟨hkne, x₁, x₂, h₁, h₂, hne⟩
    have h3 : k * (x₁ ^ 2 - x₂ ^ 2) - 6 * (x₁ - x₂) = 0 := by 
      have eq1 : k * x₁ ^ 2 - 6 * x₁ + 9 = 0 := h₁
      have eq2 : k * x₂ ^ 2 - 6 * x₂ + 9 = 0 := h₂
      have eq3 : (k * x₁ ^ 2 - 6 * x₁ + 9) - (k * x₂ ^ 2 - 6 * x₂ + 9) = 0 := by linarith
      ring_nf at eq3 ⊢
      linarith
    have h4 : (x₁ - x₂) * (k * (x₁ + x₂) - 6) = 0 := by 
      have eq1 : k * (x₁ ^ 2 - x₂ ^ 2) - 6 * (x₁ - x₂) = 0 := h3
      have eq2 : k * (x₁ ^ 2 - x₂ ^ 2) - 6 * (x₁ - x₂) = (x₁ - x₂) * (k * (x₁ + x₂) - 6) := by 
        ring
      rw [eq2] at eq1
      linarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- x₁ - x₂ = 0 
      exfalso
      apply hne
      linarith
    · -- k * (x₁ + x₂) - 6 = 0 
      have h6' : k * (x₁ + x₂) = 6 := by linarith 
      have hk1 : k < 1 := by
        have h7 : k * (x₁ * x₂) = 9 := by 
          nlinarith [sq_pos_of_ne_zero hkne, sq_pos_of_ne_zero (show (x₁ - x₂ : ℝ) ≠ 0 by intro h; apply hne; linarith), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂)]
        have h8 : (x₁ - x₂) ^ 2 > 0 := by
          apply sq_pos_of_ne_zero
          intro h 
          apply hne
          linarith 
        nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (k * (x₁ - x₂)), sq_nonneg (x₁ + x₂ - 3), sq_nonneg (x₂ - 3), sq_pos_of_ne_zero hkne, sq_pos_of_ne_zero (show (x₁ - x₂ : ℝ) ≠ 0 by intro h; apply hne; linarith)]
      tauto 
  · -- Now prove the reverse direction
    rintro ⟨hk1, hkne⟩
    constructor 
    · exact_mod_cast hkne 
    · -- Show the existence of two distinct roots
      have h10 : k < 1 := hk1 
      have h11 : k ≠ 0 := hkne 
      have h13 : 0 < 1 - k := by linarith 
      use (3 + 3 * Real.sqrt (1 - k)) / k, (3 - 3 * Real.sqrt (1 - k)) / k 
      constructor 
      · -- Show that x₁ is a root 
        field_simp [hkne]
        ring_nf 
        rw [Real.sq_sqrt (by linarith)]
        <;> nlinarith 
      constructor 
      · -- Show that x₂ is a root 
        field_simp [hkne]
        ring_nf 
        rw [Real.sq_sqrt (by linarith)]
        <;> nlinarith 
      · -- Show that x₁ ≠ x₂ 
        by_contra h 
        field_simp [hkne] at h 
        have h19 : Real.sqrt (1 - k) = 0 := by 
          nlinarith 
        have h19' : 1 - k > 0 := by linarith 
        have h20 : Real.sqrt (1 - k) > 0 := by 
          apply Real.sqrt_pos.mpr 
          linarith 
        linarith