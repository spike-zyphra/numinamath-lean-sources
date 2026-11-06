import Mathlib

/- Given an ellipse with its center at the origin and passing through the point $P(3,0)$, and $a=3b$, find the standard equation of the ellipse. -/
theorem algebra_9362 (a b : ℝ) (ha : a > 0) (hb : b > 0) (h : a = 3 * b) (hP : 3 ^ 2 / a ^ 2 + 0 ^ 2 / b ^ 2 = 1 ∨ 0^2 / a^2 + 3^2/b^2 = 1): (a = 3 ∧ b = 1) ∨ (a = 9 ∧ b = 3) := by
simp at hP
rcases hP with hPx | hPy
-- two cases: major axis is x-axis or y-axis.
-- x case.
have aeq': a^2 = 9 := by
  rw [← mul_one (a^2), ← hPx]
  field_simp
  norm_num
-- from a^2=9, obviously a=3
have aeq: a = 3 := by
  have ht1: √(a^2) = √9 := congrArg Real.sqrt aeq'
  have ht2: √9 = 3 := by
    have h1: 0 < (3:ℝ) := by norm_num
    have h2: 3*3 = (9:ℝ) := by norm_num
    exact (Real.sqrt_eq_iff_mul_self_eq_of_pos h1).mpr h2
  have ht3: √(a^2) = a := by
    have h1: 0 ≤ a := le_of_lt ha
    exact Real.sqrt_sq h1
  rwa [ht2, ht3] at ht1
-- a = 3b, so b=1
have beq: b = 1 := by linarith
left
exact ⟨aeq, beq⟩
-- case that major axis is y-axis.
have beq': b^2 = 9 := by
    rw [← mul_one (b^2), ← hPy]
    field_simp
    norm_num
-- b^2=9, so b=3
have beq: b = 3 := by
    have h1: 0 ≤ b := by linarith [hb]
    have h2: 0 ≤ (3:ℝ) := by norm_num
    have h3: (9:ℝ) = 3^2 := by norm_num
    rw [h3] at beq'
    apply (sq_eq_sq h1 h2).mp beq'
-- a=3b, so a = 9
have aeq: a = 9 := by
    rw [beq] at h
    linarith [h]
right
exact ⟨aeq, beq⟩