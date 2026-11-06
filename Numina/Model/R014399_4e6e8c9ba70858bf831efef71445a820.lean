import Mathlib

theorem algebra_2224 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a / b + a / c = (b + c) / (b + c - a)) :
    a = b ∨ a = c ∨ b = c := by
  have h1 : b + c - a ≠ 0 := by
    by_contra h1
    have h2 : b + c = a := by linarith
    rw [show b + c - a = 0 by linarith [h2] ] at h 
    field_simp [h2, show 0 < b * c by nlinarith] at h 
    all_goals
      nlinarith
  have eq1 : a * (b + c) * (b + c - a) = (b * c) * (b + c) := by 
    have eq1 : a / b + a / c = (b + c) / (b + c - a) := h 
    have eq2 : a / b + a / c = a * (b + c) / (b * c) := by 
      field_simp 
      <;> nlinarith 
    rw [eq2] at eq1 
    have h2 : b * c ≠ 0 := by nlinarith 
    have h3 : b + c - a ≠ 0 := h1 
    field_simp [h2, h3] at eq1 ⊢ 
    nlinarith
  have eq4 : (b + c) * (a * (b + c - a) - b * c) = 0 := by 
    nlinarith [eq1] 
  cases' (mul_eq_zero.mp eq4) with h5 h6 
  · -- Case $b + c = 0$, which is impossible because $b > 0$ and $c > 0$
    nlinarith
  · -- Case $a * (b + c - a) - b * c = 0$
    have eq5 : a * (b + c - a) - b * c = 0 := by 
      linarith 
    have eq6 : (b - a) * (a - c) = 0 := by 
      nlinarith [eq5]
    cases' (mul_eq_zero.mp eq6) with h7 h8 
    · -- Case $b - a = 0$, so $a = b$
      left 
      linarith 
    · -- Case $a - c = 0$, so $a = c$
      right 
      left 
      linarith