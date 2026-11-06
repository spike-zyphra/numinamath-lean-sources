import Mathlib

theorem algebra_187114 {u v : ℝ} (h1 : u^2 + u * v = 15) (h2 : v^2 + u * v = 10) :
    (u = -3 ∧ v = -2) ∨ (u = 3 ∧ v = 2) := by 
  have h3 : u ^ 2 - v ^ 2 = 5 := by linarith 
  have eq1 : u * (u + v) = 15 := by 
    nlinarith 
  have eq2 : v * (u + v) = 10 := by 
    nlinarith 
  have h5 : u + v ≠ 0 := by 
    by_contra h
    have h6 : u * (u + v) = 0 := by 
      rw [h]
      ring 
    rw [h6] at eq1 
    linarith 
  have h6 : (u + v) ^ 2 = 25 := by 
    have h10 : (u + v) ^ 2 = u * (u + v) + v * (u + v) := by 
      ring 
    rw [h10, eq1, eq2] 
    all_goals linarith 
  have h7 : (u + v) = 5 ∨ (u + v) = -5 := by 
    have h : (u + v) ^ 2 = 25 := h6 
    have h8 : (u + v) = 5 ∨ (u + v) = -5 := by 
      have h9 : (u + v) ^ 2 - 25 = 0 := by linarith 
      have h10 : (u + v - 5) * (u + v + 5) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h10) with h11 h12 
      · left 
        linarith 
      · right 
        linarith 
    exact h8 
  cases' h7 with huv5 huv5 
  · -- Case $u + v = 5$
    have hu : u = 3 := by 
      rw [huv5] at eq1 
      nlinarith 
    have hv : v = 2 := by 
      rw [huv5] at eq2 
      nlinarith 
    right 
    exact ⟨hu, hv⟩ 
  · -- Case $u + v = -5$
    have hu : u = -3 := by 
      rw [huv5] at eq1 
      nlinarith 
    have hv : v = -2 := by 
      rw [huv5] at eq2 
      nlinarith 
    left 
    exact ⟨hu, hv⟩