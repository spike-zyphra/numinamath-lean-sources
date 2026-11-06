import Mathlib

theorem algebra_526
  {a b c x y z : ℝ} (h : ¬ (a = b ∧ b = c)) (hx : x = a^2 - b * c) (hy : y = b^2 - c * a) (hz : z = c^2 - a * b) : (x > 0 ∨ y > 0 ∨ z > 0) := by 
  by_contra h1
  push_neg at h1
  have h1x : x ≤ 0 := by linarith
  have h1y : y ≤ 0 := by linarith
  have h1z : z ≤ 0 := by linarith
  rw [hx] at h1x
  rw [hy] at h1y
  rw [hz] at h1z
  have h1 : a^2 + b^2 + c^2 ≤ b * c + c * a + a * b := by
    nlinarith
  -- Multiply by $2$ becomes sum of cubes.
  have h2 : (a - b)^2 + (b - c)^2 + (c - a)^2 ≤ 0 := by
    nlinarith [h1]
  have hb1 : (a - b)^2 ≥ 0 := by apply sq_nonneg
  have hb2 : (b - c)^2 ≥ 0 := by apply sq_nonneg
  have hb3 : (c - a)^2 ≥ 0 := by apply sq_nonneg
  have he1 : (a - b) ^ 2 = 0 := by linarith [hb1, hb2, hb3]
  have he2 : (b - c) ^ 2 = 0 := by linarith [hb1, hb2, hb3]
  have he3 : (c - a) ^ 2 = 0 := by linarith [hb1, hb2, hb3]
  have eq1 : a - b = 0 := by
    rwa [sq_eq_zero_iff] at he1
  have eq2 : b - c = 0 := by
    rwa [sq_eq_zero_iff] at he2
  have heq1 : a = b := by linarith [eq1]
  have heq2 : b = c := by linarith [eq2]
  have heq : a = b ∧ b = c := ⟨heq1, heq2⟩
  contradiction
  all_goals nlinarith
  all_goals tauto