import Mathlib

theorem algebra_137451 (n : ℕ) (x : Fin n → ℤ) (hx : ∀ i, x i = 0 ∨ x i = 1 ∨ x i = -1)
    (hsum : ∑ i, x i = 1000) :
    ∑ i, (x i) ^ 2017 = 1000 := by 
  have h1 : ∀ i, (x i) ^ 2017 = x i := by 
    intro i
    have h2 : x i = 0 ∨ x i = 1 ∨ x i = -1 := hx i
    rcases h2 with (h | h | h)
    · 
      rw [h]
      all_goals norm_num
    · 
      rw [h]
      all_goals norm_num
    · 
      rw [h]
      all_goals norm_num
  simp_rw [h1]
  <;> exact hsum