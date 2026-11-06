import Mathlib

theorem algebra_166692 (a : ℝ) (x y z : ℝ) (h : x + y + z = a) :
    x * y + y * z + z * x ≤ a ^ 2 / 3 ∧
    (x * y + y * z + z * x = a ^ 2 / 3 ↔ x = y ∧ y = z) := by 
  have h1 : x * y + y * z + z * x ≤ a ^ 2 / 3 := by
    have h2 : (x * y + y * z + z * x : ℝ) ≤ (a ^ 2 / 3 : ℝ) := by 
      have h3 : (x - y : ℝ) ^ 2 + (y - z : ℝ) ^ 2 + (z - x : ℝ) ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
      have h4 : (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + y * z + z * x) := by
        nlinarith 
      have h5 : (x + y + z) ^ 2 = a ^ 2 := by 
        rw [h]
      have h6 : a ^ 2 - 3 * (x * y + y * z + z * x) ≥ 0 := by 
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          h3]
      nlinarith
    linarith
  constructor
  · -- Prove the first part: x * y + y * z + z * x ≤ a ^ 2 / 3
    exact h1 
  · -- Prove the second part: the equivalence
    constructor
    · -- Prove forward direction: if x * y + y * z + z * x = a^2 / 3 then x = y ∧ y = z
      intro h_eq
      have h5 : (x - y : ℝ) ^ 2 + (y - z : ℝ) ^ 2 + (z - x : ℝ) ^ 2 = 0 := by
        have h6 : (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + y * z + z * x) := by
          nlinarith 
        have h7 : (x + y + z) ^ 2 = a ^ 2 := by 
          rw [h]
        have h8 : (x * y + y * z + z * x) = a^2 / 3 := by
          linarith [h_eq]
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          h7, h8]
      have h6 : (x - y : ℝ) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          h5]
      have h7 : (y - z : ℝ) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          h5]
      have h8 : x - y = 0 := by 
        nlinarith 
      have h9 : y - z = 0 := by 
        nlinarith 
      have hx1 : x = y := by 
        linarith 
      have hx2 : y = z := by 
        linarith 
      exact ⟨hx1, hx2⟩
    · -- Prove backward direction: if x = y ∧ y = z then x * y + y * z + z * x = a ^ 2 / 3
      rintro ⟨rfl, rfl⟩
      -- From h : x + x + x = a, get 3x = a
      have h' : 3 * x = a := by 
        nlinarith [h]
      -- So x = a / 3
      have hx1 : x = a / 3 := by 
        linarith
      have eq3 : x * x + x * x + x * x = a ^ 2 / 3 := by 
        rw [show x = a / 3 by linarith [hx1]]
        field_simp 
        <;> nlinarith 
      linarith
      all_goals try linarith 
      all_goals try tauto 
  all_goals try linarith 
  all_goals try tauto 
  all_goals try linarith 
  all_goals try tauto
  all_goals try linarith
  all_goals try tauto