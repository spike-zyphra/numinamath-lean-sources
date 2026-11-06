import Mathlib

open Real Set

theorem algebra_601626 {a b : ℝ} (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hab : a * b = 1 / 36) :
    IsLeast {x | ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 0 < b ∧ b < 1 ∧ a * b = 1 / 36 ∧ x = 1 / (1 - a) + 1 / (1 - b)} (12 / 5) := by
  constructor 
  · -- First, we prove 12/5 is in the set. 
    use 1 / 6, 1 / 6 
    norm_num 
  · -- Now, we prove 12/5 is the least element in the set. 
    intro x hx 
    rcases hx with ⟨a, b, ha1, ha2, hb1, hb2, hab, hx⟩ 
    have h : 1 / (1 - a) + 1 / (1 - b) ≥ 12 / 5 := by 
      have h1 : 0 < 1 - a := by nlinarith 
      have h2 : 0 < 1 - b := by nlinarith 
      have h3 : a * b = 1 / 36 := hab 
      have h4 : (1 / (1 - a) + 1 / (1 - b)) - 12 / 5 ≥ 0 := by 
        have h5 : (1 / (1 - a) + 1 / (1 - b)) - 12 / 5 = (5 * ((1 - b) + (1 - a)) - 12 * ((1 - a) * (1 - b)) ) / (5 * ((1 - a) * (1 - b))) := by 
          field_simp 
          ring 
        rw [h5] 
        have h6 : 0 < 5 * ((1 - a) * (1 - b)) := by 
          nlinarith 
        have h7 : (5 * ((1 - b) + (1 - a)) - 12 * ((1 - a) * (1 - b)) ) ≥ 0 := by 
          nlinarith [sq_nonneg (a - 1 / 6), sq_nonneg (b - 1 / 6), sq_nonneg (a * b - 1 / 36), sq_nonneg (a - b), 
            mul_pos (show 0 < 1 - a by nlinarith) (show 0 < 1 - b by nlinarith), 
            mul_pos ha1 hb1, 
            mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hb1) 
          ]
        apply div_nonneg 
        linarith 
        linarith 
      linarith 
    linarith [h, hx]