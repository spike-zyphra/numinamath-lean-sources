import Mathlib

theorem algebra_147109 (x : ℝ) (hx : x ∈ Set.Ioo 0 1) :
    2 * Real.log (Real.sqrt x) - Real.log (1 - x) = 2 ↔
    x = (Real.exp 2) / (1 + Real.exp 2) := by
  rcases hx with ⟨hx1, hx2⟩
  constructor
  · -- Assume 2 * Real.log (Real.sqrt x) - Real.log (1 - x) = 2, prove x = (Real.exp 2) / (1 + Real.exp 2)
    intro h_eq
    have h1 : 2 * Real.log (Real.sqrt x) = Real.log x := by
      have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)
      have h3 : 2 * Real.log (Real.sqrt x) = Real.log ((Real.sqrt x) ^ 2) := by
        simp [Real.log_pow]
      rw [h3]
      rw [h2]
    have h4 : Real.log x - Real.log (1 - x) = 2 := by
      linarith [h_eq, h1]
    have h5 : Real.log x - Real.log (1 - x) = Real.log (x / (1 - x)) := by
      rw [Real.log_div (by linarith) (by linarith)]
    have h6 : Real.log (x / (1 - x)) = 2 := by
      linarith [h4, h5]
    have h7 : x / (1 - x) = Real.exp 2 := by
      have h8 : Real.log (x / (1 - x)) = 2 := h6
      have h9 : x / (1 - x) > 0 := by
        apply div_pos
        all_goals linarith
      have h10 : Real.log (x / (1 - x)) = 2 := h6
      rw [← h10]
      field_simp [Real.exp_log]
    have h8 : x = (Real.exp 2) / (1 + Real.exp 2) := by
      have h9 : x / (1 - x) = Real.exp 2 := h7
      have h10 : (1 - x) ≠ 0 := by linarith
      field_simp [h10] at h9 ⊢
      nlinarith [Real.exp_pos 2]
    exact h8
  · -- Assume x = (Real.exp 2) / (1 + Real.exp 2), prove 2 * Real.log (Real.sqrt x) - Real.log (1 - x) = 2
    intro h_eq
    have h1 : 2 * Real.log (Real.sqrt x) = Real.log x := by
      have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)
      have h3 : 2 * Real.log (Real.sqrt x) = Real.log ((Real.sqrt x) ^ 2) := by
        simp [Real.log_pow]
      rw [h3]
      rw [h2]
    have h4 : Real.log x - Real.log (1 - x) = 2 := by
      have h5 : x = (Real.exp 2) / (1 + Real.exp 2) := h_eq
      have h6 : 1 - x = 1 / (1 + Real.exp 2) := by
        rw [h5]
        field_simp [Real.exp_pos 2]
      have h7 : x / (1 - x) = Real.exp 2 := by
        rw [h6]
        rw [h5]
        field_simp [Real.exp_pos 2]
        <;> nlinarith [Real.exp_pos 2]
      have h8 : Real.log (x / (1 - x)) = 2 := by
        have h9 : x / (1 - x) = Real.exp 2 := h7
        rw [h9]
        have h10 : Real.log (Real.exp 2) = 2 := Real.log_exp 2
        linarith
      have h9 : Real.log (x / (1 - x)) = Real.log x - Real.log (1 - x) := by
        rw [Real.log_div (by linarith) (by linarith)]
      linarith [h9, h8]
    linarith [h1, h4]