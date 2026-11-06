import Mathlib

theorem algebra_10782 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∃! x, (x ^ 2 / a ^ 2 - (x ^ 2 + 1) / b ^ 2) = 1) :
    (a ^ 2 + b ^ 2) / a ^ 2 = (5 : ℝ) / 4 := by
  rcases h with ⟨x, ⟨hx1, hx2⟩⟩
  have eq1 : (x ^ 2 / a ^ 2 - (x ^ 2 + 1) / b ^ 2) = 1 := by 
    simpa using hx1 
  have eq2 : (-x) ^ 2 / a ^ 2 - ((-x) ^ 2 + 1) / b ^ 2 = 1 := by 
    have eq3 : (-x) ^ 2 / a ^ 2 - ((-x) ^ 2 + 1) / b ^ 2 = (x ^ 2 / a ^ 2 - (x ^ 2 + 1) / b ^ 2) := by 
      ring_nf 
    rw [eq3] 
    linarith [eq1]
  have eq3 : ∀ y : ℝ, (y ^ 2 / a ^ 2 - (y ^ 2 + 1) / b ^ 2) = 1 → y = x := by 
    intro y hy 
    apply hx2 
    simpa using hy 
  have eq4 := eq3 (-x) eq2 
  have hx0 : x = 0 := by linarith 
  rw [hx0] at eq1 
  field_simp [hb, ha] at eq1 
  all_goals nlinarith [sq_pos_of_ne_zero hb, sq_pos_of_ne_zero ha]