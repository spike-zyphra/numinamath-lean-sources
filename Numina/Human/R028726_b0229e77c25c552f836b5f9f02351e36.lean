import Mathlib

/- Prove that if $0<\frac{a}{b}< b <2 a$ then

$$
\frac{2 a b-a^{2}}{7 a b-3 b^{2}-2 a^{2}}+\frac{2 a b-b^{2}}{7 a b-3 a^{2}-2 b^{2}} \geq 1+\frac{1}{4}\left(\frac{a}{b}-\frac{b}{a}\right)^{2}
$$ -/
theorem inequalities_606259 (a b : ℝ) (h₀ : 0 < a / b) (h₁ : a / b < b) (h₂ : b < 2 * a) (h₃ : a / b < 2) :
    (2 * a * b - a ^ 2) / (7 * a * b - 3 * b ^ 2 - 2 * a ^ 2) + (2 * a * b - b ^ 2) / (7 * a * b - 3 * a ^ 2 - 2 * b ^ 2) ≥ 1 + (1 / 4) * (a / b - b / a) ^ 2 := by
  -- Show that ab > 0.
  have hab : a * b > 0 := by
    apply mul_pos
    linarith
    linarith
  replace hab := ne_of_gt hab
  -- Divide both denominator and numerator of the left-hand side by $ab$.
  rw [<-div_div_div_cancel_right₀ hab]
  nth_rewrite 4 [<-div_div_div_cancel_right₀ hab]
  -- Let u = 2 - a / b and v = 2 - b / a.
  let u := 2 - a / b
  let v := 2 - b / a
  simp at hab
  -- Rewrite the inequality in terms of u and v.
  rw [show (2 * a * b - a ^ 2) / (a * b) = u by field_simp [u, show a ≠ 0 by simp [hab], show b ≠ 0 by simp [hab]]; ring_nf]
  rw [show (7 * a * b - 3 * b ^ 2 - 2 * a ^ 2) / (a * b) = v + u * v by field_simp [u, v, show a ≠ 0 by simp [hab], show b ≠ 0 by simp [hab]]; ring_nf]
  rw [show (2 * a * b - b ^ 2) / (a * b) = v by field_simp [v, show a ≠ 0 by simp [hab], show b ≠ 0 by simp [hab]]; ring_nf]
  rw [show (7 * a * b - 3 * a ^ 2 - 2 * b ^ 2) / (a * b) = u + u * v by field_simp [u, v, show a ≠ 0 by simp [hab], show b ≠ 0 by simp [hab]]; ring_nf]
  rw [show a / b - b / a = v - u by simp [u, v]]
  -- Show that u > 0 and v > 0.
  have hu : u > 0 := by
    simp [u]
    exact h₃
  have hv : v > 0 := by
    simp [v]
    rw [div_lt_iff₀]
    exact h₂
    linarith
  -- Show that u + v ≤ 2.
  have hsum : u + v ≤ 2 := by
    simp [u, v]
    have h := sq_nonneg (Real.sqrt (b / a) - Real.sqrt (a / b))
    rw [sub_sq, Real.sq_sqrt, Real.sq_sqrt, mul_assoc, <-Real.sqrt_mul] at h
    field_simp [show a ≠ 0 by simp [hab], show b ≠ 0 by simp [hab]] at h ⊢
    rw [le_div_iff₀] at h
    rw [div_le_iff₀]
    linarith only [h]
    . apply mul_pos (by linarith) (by linarith)
    . apply mul_pos (by linarith) (by linarith)
    . apply div_nonneg (by linarith) (by linarith)
    . apply div_nonneg (by linarith) (by linarith)
    . apply div_nonneg (by linarith) (by linarith)
  -- Show that uv ≤ 1.
  have hprod : u * v ≤ 1 := by
    have h := sq_nonneg (Real.sqrt u - Real.sqrt v)
    rw [sub_sq, Real.sq_sqrt, Real.sq_sqrt, mul_assoc, <-Real.sqrt_mul] at h
    replace h : Real.sqrt (u * v) ≤ 1 := by
      linarith only [h, hsum]
    rw [<-sq_le_sq₀, Real.sq_sqrt] at h
    simp at h
    exact h
    all_goals
      positivity
  -- Show that (v + u * v) * (u + u * v) ≤ 4.
  have hsumprod : (v + u * v) * (u + u * v) ≤ 4 := by
    rw [show (v + u * v) * (u + u * v) = u * v * (u * v + u + v + 1) by ring, show (4 : ℝ) = 1 * 4 by norm_num]
    apply mul_le_mul hprod (by linarith)
    all_goals
      positivity
  clear_value u v
  -- Reduce fractions to common denominator to show that the inequality holds.
  rw [div_add_div, ge_iff_le, add_comm, <-le_sub_iff_add_le, div_sub_one, one_div_mul_eq_div]
  apply div_le_div₀
  . nlinarith only [hprod, show 0 ≤ u * v by positivity, sq_nonneg (u - v)] 
  . nlinarith only [hprod, show 0 ≤ u * v by positivity]
  . positivity
  . exact hsumprod
  all_goals
    positivity
