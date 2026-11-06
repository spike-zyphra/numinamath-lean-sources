import Mathlib

theorem algebra_144643 (a : ℝ) (h : ∃! x : ℝ, x^2 = 3 * (a * x - 3)) :
    a = 2 ∨ a = -2 := by 
  rcases h with ⟨x, ⟨hx1, hx2⟩⟩
  have h2 : ∀ y : ℝ, y ^ 2 = 3 * (a * y - 3) → y = x := by
    intro y hy
    simpa using hx2 y hy

  have h3 : (3 * a - x) ^ 2 = 3 * (a * (3 * a - x) - 3) := by 
    nlinarith [hx1]
  
  have h4 : (3 * a - x) = x := by 
    apply h2 
    exact h3

  have h5 : x = 3 * a / 2 := by
    linarith
  
  rw [h5] at hx1

  have h6 : 9 * a ^ 2 / 4 = 9 * a ^ 2 / 2 - 9 := by
    nlinarith

  have h7 : a ^ 2 = 4 := by
    nlinarith

  have h8 : a = 2 ∨ a = -2 := by 
    have h9 : a ^ 2 = 4 := h7 
    have : a = 2 ∨ a = -2 := by
      have h10 : a ^ 2 - 4 = 0 := by linarith 
      have h11 : (a - 2) * (a + 2) = 0 := by
        linarith [h10]
      cases' (mul_eq_zero.1 h11) with h12 h13 
      · -- a - 2 = 0 
        left
        linarith 
      · -- a + 2 = 0 
        right 
        linarith 
    tauto
  
  tauto