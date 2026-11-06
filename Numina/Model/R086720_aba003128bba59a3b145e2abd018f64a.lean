import Mathlib

theorem algebra_213442 {x y : ℝ} (h₀ : x^2 + y^2 = 2) (h₁ : x^2 / (2 - y) + y^2 / (2 - x) = 2) :
    (x, y) = (1, 1) := by 
  have h2 : 2 - y ≠ 0 := by
    by_contra h
    have hy : y = 2 := by linarith
    rw [hy] at h₀
    nlinarith [sq_nonneg x]
  have h3 : 2 - x ≠ 0 := by
    by_contra h
    have hx : x = 2 := by linarith
    rw [hx] at h₀
    nlinarith [sq_nonneg y]
  have h2' : x^2 * (2 - x) + y^2 * (2 - y) = 2 * ((2 - y) * (2 - x)) := by
    field_simp [h2, h3] at h₁ ⊢ 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
  have eq1 : (x - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), 
     sq_nonneg ((x - 1) * (y - 1)), pow_two_nonneg (x - y), sq_nonneg (x * y), sq_nonneg (x + y - 2), h₀, h2']
  have hx1 : x - 1 = 0 := by
    rw [sq_eq_zero_iff] at eq1
    linarith 
  have eq2 : (y - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg ((x - 1) * (y - 1)), pow_two_nonneg (x - y), sq_nonneg (x * y), sq_nonneg (x + y - 2), h₀, h2', hx1]
  have hy1 : y - 1 = 0 := by
    rw [sq_eq_zero_iff] at eq2
    linarith 
  have hx2 : x = 1 := by linarith [hx1]
  have hy2 : y = 1 := by linarith [hy1]
  simp [Prod.ext_iff, hx2, hy2]
  all_goals linarith 
  all_goals nlinarith 
  all_goals simp 
  all_goals nlinarith 
  all_goals nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
  <;> try { linarith }
  all_goals try { simp }
  all_goals try { nlinarith }
  <;> try { nlinarith }
  all_goals try { linarith }
  all_goals try { simp }
  all_goals try { nlinarith }