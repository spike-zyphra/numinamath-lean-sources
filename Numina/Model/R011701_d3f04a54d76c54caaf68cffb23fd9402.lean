import Mathlib
open Nat Real Finset Set
noncomputable section

theorem algebra_200234 :
    ∀ a : ℝ, (∀ y : ℝ, ∃ x : ℝ, y = Real.log (x^2 - a * x + a) ∧ x^2 - a * x + a > 0) ↔
    (a ≤ 0 ∨ a ≥ 4) := by 
  intro a 
  constructor 
  · -- (∀ y : ℝ, ∃ x : ℝ, y = Real.log (x^2 - a * x + a) ∧ x^2 - a * x + a > 0) → (a ≤ 0 ∨ a ≥ 4)
    intro h 
    by_contra h1 
    push_neg at h1 
    have h2 : a > 0 := by nlinarith 
    have h3 : a < 4 := by nlinarith 
    have h4 : (4 * a - a ^ 2 : ℝ) / 4 > 0 := by nlinarith 
    have h5 := h (Real.log ((4 * a - a ^ 2) / 8))
    rcases h5 with ⟨x, hx1, hx2⟩ 
    have hx_eq : x^2 - a * x + a = (4 * a - a^2) / 8 := by 
      have h6 : Real.log (x^2 - a * x + a) = Real.log ((4 * a - a ^ 2) / 8) := by linarith [hx1]
      have h7 : x^2 - a * x + a > 0 := hx2 
      have h8 : (4 * a - a ^ 2 : ℝ) / 8 > 0 := by nlinarith 
      have h9 : x^2 - a * x + a = (4 * a - a ^ 2) / 8 := by
        apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr (by linarith)) h6 
      linarith 
    nlinarith [sq_nonneg (x - a / 2), sq_nonneg (x - (4 * a - a^2) / 8), sq_nonneg (x * 4), sq_nonneg (x - a), sq_nonneg ((4 * a - a^2) / 8 - x^2)]
  · -- (a ≤ 0 ∨ a ≥ 4) → (∀ y : ℝ, ∃ x : ℝ, y = Real.log (x^2 - a * x + a) ∧ x^2 - a * x + a > 0)
    rintro (h | h)
    · -- Case where a ≤ 0 
      intro y 
      have h6 : a ≤ 0 := h 
      have h7 : a ^ 2 + 4 * (Real.exp y) - 4 * a ≥ 0 := by 
        nlinarith [sq_nonneg (a - 2), h, Real.exp_pos y] 
      have h8 : ∃ x : ℝ, x ^ 2 - a * x + a = Real.exp y := by 
        use (a + Real.sqrt (a ^ 2 + 4 * (Real.exp y) - 4 * a)) / 2 
        nlinarith [Real.sqrt_nonneg (a ^ 2 + 4 * (Real.exp y) - 4 * a), Real.sq_sqrt (show a ^ 2 + 4 * (Real.exp y) - 4 * a ≥ 0 by linarith), Real.exp_pos y] 
      rcases h8 with ⟨x, hx⟩ 
      use x 
      constructor 
      · -- Show that y = Real.log (x^2 - a * x + a)
        have h9 : x ^ 2 - a * x + a = Real.exp y := hx 
        have h10 : Real.log (x ^ 2 - a * x + a) = y := by 
          rw [h9] 
          field_simp [Real.log_exp] 
        linarith 
      · -- Show that x^2 - a * x + a > 0 
        have h9 : x ^ 2 - a * x + a = Real.exp y := hx 
        have h10 : Real.exp y > 0 := Real.exp_pos y 
        linarith [h9, h10] 
    · -- Case where a ≥ 4 
      intro y 
      have h6 : a ≥ 4 := h 
      have h7 : a ^ 2 + 4 * (Real.exp y) - 4 * a ≥ 0 := by 
        nlinarith [sq_nonneg (a - 2), h, Real.exp_pos y] 
      have h8 : ∃ x : ℝ, x ^ 2 - a * x + a = Real.exp y := by 
        use (a + Real.sqrt (a ^ 2 + 4 * (Real.exp y) - 4 * a)) / 2 
        nlinarith [Real.sqrt_nonneg (a ^ 2 + 4 * (Real.exp y) - 4 * a), Real.sq_sqrt (show a ^ 2 + 4 * (Real.exp y) - 4 * a ≥ 0 by linarith), Real.exp_pos y] 
      rcases h8 with ⟨x, hx⟩ 
      use x 
      constructor 
      · -- Show that y = Real.log (x^2 - a * x + a)
        have h9 : x ^ 2 - a * x + a = Real.exp y := hx 
        have h10 : Real.log (x ^ 2 - a * x + a) = y := by 
          rw [h9] 
          field_simp [Real.log_exp] 
        linarith 
      · -- Show that x^2 - a * x + a > 0 
        have h9 : x ^ 2 - a * x + a = Real.exp y := hx 
        have h10 : Real.exp y > 0 := Real.exp_pos y 
        linarith [h9, h10]