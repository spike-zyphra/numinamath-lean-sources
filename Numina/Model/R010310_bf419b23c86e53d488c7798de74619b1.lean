import Mathlib

theorem algebra_14691 (n : ℕ) (h₀ : n = 15 - 5) :
    (3 ^ 5) * n + 5 = 2435 := 
  calc
    (3 ^ 5) * n + 5 = (3 ^ 5) * (15 - 5) + 5 := by rw [h₀]
    _ = (3 ^ 5) * 10 + 5 := by norm_num
    _ = 243 * 10 + 5 := by norm_num
    _ = 2430 + 5 := by norm_num
    _ = 2435 := by norm_num

theorem final_result : 
    ∃ (regularMembers : ℕ), regularMembers = 2430 ∧ regularMembers + 5 = 2435 := by 
  exact ⟨2430, rfl, by norm_num⟩