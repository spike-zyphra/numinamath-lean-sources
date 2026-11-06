import Mathlib

theorem algebra_604648 :
  {(a, b, c, d) : ℝ × ℝ × ℝ × ℝ | a + b + c + d = 20 ∧ a * b + a * c + a * d + b * c + b * d + c * d = 150} =
  {(5, 5, 5, 5)} := by
  ext ⟨a, b, c, d⟩
  simp
  constructor
  · -- Assume $\langle a, b, c, d \rangle$ satisfy both equations, prove $\langle a, b, c, d \rangle = \langle 5, 5, 5, 5 \rangle$.
    rintro ⟨h₁, h₂⟩
    have h3 : (a - 5) ^ 2 + (b - 5) ^ 2 + (c - 5) ^ 2 + (d - 5) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
    have ha1 : a - 5 = 0 := by
      nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5), h3]
    have hb1 : b - 5 = 0 := by
      nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5), h3]
    have hc1 : c - 5 = 0 := by
      nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5), h3]
    have hd1 : d - 5 = 0 := by
      nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5), h3]
    have ha : a = 5 := by linarith
    have hb : b = 5 := by linarith
    have hc : c = 5 := by linarith
    have hd : d = 5 := by linarith
    norm_num [ha, hb, hc, hd]
  · -- Show that $\langle 5, 5, 5, 5 \rangle$ satisfies both equations.
    rintro ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · -- Show that $5+5+5+5=20$.
      norm_num
    · -- Show that $5·5+5·5+5·5+5·5+5·5+5·5=150$
      norm_num