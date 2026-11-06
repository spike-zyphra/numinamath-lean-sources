import Mathlib

theorem algebra_7397 {a x : ℝ} (ha : x = a) (h : 1 + 1 / x - x ^ 3 = 11) :
    1 + 1 / (-a) - (-a) ^ 3 = -9 := by 
  have h1 : 1 + 1 / a - a ^ 3 = 11 := by 
    rw [show x = a by exact ha] at h
    exact h
  have h2 : a ≠ 0 := by
    by_contra h3
    rw [h3] at h1
    norm_num at h1
    all_goals linarith 
  have h4 : 1 / (-a) = - (1 / a) := by
    field_simp [show a ≠ 0 by assumption]
    all_goals linarith 
  have h5 : (-a) ^ 3 = - (a ^ 3) := by 
    ring 
  rw [h4, h5]
  -- Now we need to manipulate the expression algebraically
  have h4' : 1/a - a^3 = 10 := by 
    have h6 : 1 + 1/a - a^3 = 11 := h1 
    linarith 
  field_simp [show a ≠ 0 by assumption] at h4' ⊢
  -- field_simp handles expressions involving reciprocals, and linarith can solve linear equations
  -- From h1, we have 1 + (1/a) - a^3 = 11
  -- After field_simp, this becomes (a + 1 - a^4)/a = 11
  -- But we also have in our goal the expression (a^3 - 1/a + 1)
  -- field_simp will convert expressions involving reciprocals to their polynomial form
  -- Then linarith can solve the resulting linear constraints
  nlinarith [sq_nonneg a, sq_nonneg (a^2), sq_nonneg (a + 1 - a^4)]
  -- The above tactics are some of Lean's powerful solvers that can handle nonlinear arithmetic
  -- They are able to solve the constraints derived from h4' to conclude the goal of -9
  all_goals nlinarith [sq_nonneg a, sq_nonneg (a^2), sq_nonneg (a + 1 - a^4), sq_pos_of_ne_zero (show a ≠ 0 by assumption)]
  <;> try { tauto }