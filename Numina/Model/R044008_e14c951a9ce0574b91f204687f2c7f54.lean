import Mathlib

open Real

theorem inequalities_248996 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b) ∧
    (3 / 2 = a / (b + c) + b / (a + c) + c / (a + b) ↔ a = b ∧ b = c) := by
  constructor
  · -- First part: proving the inequality. 
    have h1 : 0 < b + c := by nlinarith 
    have h2 : 0 < a + c := by nlinarith 
    have h3 : 0 < a + b := by nlinarith 
    have h4 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 ≥ 0 := by
      have pos1 : 0 < (b + c) * (a + c) * (a + b) := by positivity 
      have h5 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 =
          (a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) - 3 / 2 * (b + c) * (a + c) * (a + b)) / ((b + c) * (a + c) * (a + b)) := by
        field_simp
        ring 
      rw [h5] at *
      apply div_nonneg 
      · 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos (mul_pos ha hb) hc]
      · 
        positivity 
    linarith 
  · -- Second part: proving the equality holds iff a = b ∧ b = c 
    constructor 
    · -- Assume equality holds, prove a = b ∧ b = c 
      intro h_eq 
      have h1 : 0 < b + c := by nlinarith 
      have h2 : 0 < a + c := by nlinarith 
      have h3 : 0 < a + b := by nlinarith 
      have pos1 : 0 < (b + c) * (a + c) * (a + b) := by positivity 
      have h4 : a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) = 3 / 2 * (b + c) * (a + c) * (a + b) := by 
        have h_eq1 : a / (b + c) + b / (a + c) + c / (a + b) = 3 / 2 := by linarith 
        have eq1 : a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) = (a / (b + c) + b / (a + c) + c / (a + b)) * ((b + c) * (a + c) * (a + b)) := by 
          field_simp
          <;> nlinarith 
        rw [h_eq1] at eq1 
        nlinarith 
      have eq1 : (a - b) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a + b by nlinarith) (show 0 < a + c by nlinarith), mul_pos (show 0 < a + b by nlinarith) (show 0 < b + c by nlinarith), mul_pos (show 0 < a + c by nlinarith) (show 0 < b + c by nlinarith)]
      have eq2 : a - b = 0 := by 
        nlinarith 
      have eq3 : a = b := by 
        nlinarith 
      have eq4 : (b - c) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a + b by nlinarith) (show 0 < a + c by nlinarith), mul_pos (show 0 < a + b by nlinarith) (show 0 < b + c by nlinarith), mul_pos (show 0 < a + c by nlinarith) (show 0 < b + c by nlinarith)]
      have eq5 : b - c = 0 := by 
        nlinarith 
      have eq6 : b = c := by 
        linarith 
      constructor <;> tauto 
    · -- Assume a = b ∧ b = c, prove equality 
      rintro ⟨h1, h2⟩ 
      have h3 : a = c := by 
        linarith 
      have h4 : a / (b + c) = 1 / 2 := by
        have h6 : b = a := by linarith 
        have h7 : c = a := by linarith 
        have h8 : b + c = 2 * a := by 
          rw [h6, h7]
          nlinarith 
        rw [h8] 
        have h9 : a ≠ 0 := by nlinarith 
        field_simp [h9]
        <;> 
        try { 
          ring 
        } 
      have h5 : b / (a + c) = 1 / 2 := by 
        have h6 : a = b := by linarith 
        have h7 : c = b := by linarith 
        have h8 : a + c = 2 * b := by 
          rw [h6, h7]
          nlinarith 
        rw [h8] 
        have h9 : b ≠ 0 := by nlinarith 
        field_simp [h9]
        <;> 
        try { 
          ring 
        } 
      have h6 : c / (a + b) = 1 / 2 := by 
        have h6 : a = c := by linarith 
        have h7 : b = c := by linarith 
        have h8 : a + b = 2 * c := by 
          rw [h6, h7]
          nlinarith 
        rw [h8] 
        have h9 : c ≠ 0 := by nlinarith 
        field_simp [h9]
        <;> 
        try { 
          ring 
        } 
      linarith [h4, h5, h6]