import Mathlib

theorem algebra_9553 {a b : ℝ} (ha : a^2 + 9*a + 30 = 0) (hb : b^2 + 9*b + 30 = 0)
    (hab : a ≠ b) : a^3 + b^3 = 81 := by
  have hab1 : a + b = -9 := by
    have eq1 : a^2 + 9*a + 30 = 0 := ha
    have eq2 : b^2 + 9*b + 30 = 0 := hb
    have eq3 : a^2 + 9*a = -30 := by linarith
    have eq4 : b^2 + 9*b = -30 := by linarith
    have eq5 : a^2 + 9*a = b^2 + 9*b := by linarith
    have eq6 : (a - b) * (a + b + 9) = 0 := by
      ring_nf at eq5 ⊢ 
      linarith 
    cases' (mul_eq_zero.mp eq6) with h1 h2 
    · -- $a - b = 0$, so $a = b$, contradicts $a ≠ b$
      exfalso 
      apply hab 
      linarith 
    · -- $a + b + 9 = 0$, so $a + b = -9$
      linarith 
  have hab2 : a * b = 30 := by 
    have eq1 : a^2 + 9*a + 30 = 0 := ha
    have hab1' : a + b = -9 := hab1 
    have h : b = -9 - a := by 
      linarith 
    rw [h] 
    nlinarith [ha]
  have eq : a^3 + b^3 = (a + b) ^ 3 - 3 * (a * b) * (a + b) := by 
    ring 
  rw [eq, hab1, hab2] 
  norm_num 
  all_goals nlinarith [ha, hb, hab1, hab2]