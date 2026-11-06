import Mathlib

theorem algebra_114678 {b c : ℝ} (h : 3 * (-4) ^ 2 + b * (-4) + c = 0 ∧ ∀ x, 3 * x ^ 2 + b * x + c = 0 → x = -4) :
    b = 24 := by
  rcases h with ⟨h1, h2⟩
  have eq1 : c = 4 * b - 48 := by 
    linarith 
  have h3 : 3 * (-b / 3 + 4) ^ 2 + b * (-b / 3 + 4) + c = 0 := by
    have eq5 : 3 * (-b / 3 + 4) ^ 2 + b * (-b / 3 + 4) + c = -4 * b + 48 + c := by 
      ring_nf 
    rw [eq5]
    linarith [h1, eq1]
  have eq5 : -b / 3 + 4 = -4 := by 
    apply h2 
    linarith [h3]
  have eq6 : b = 24 := by 
    linarith [eq5]
  exact_mod_cast eq6