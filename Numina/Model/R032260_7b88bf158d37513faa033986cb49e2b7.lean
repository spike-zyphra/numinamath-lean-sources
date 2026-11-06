import Mathlib

theorem algebra_162284 (x y : ℝ) (le : 3 * x ≤ y) (h₀ : y + Real.sqrt (y - 3 * x) + 3 * x = 12)
    (h₁ : y ^ 2 + y - 3 * x - 9 * x ^ 2 = 144) :
    (x = -24 ∧ y = 72) ∨ (x = -4 / 3 ∧ y = 12) := by

  let u := Real.sqrt (y - 3 * x)
  have u_pos : u ≥ 0 := by unfold u; positivity
  have u_sq : u^2 = y - 3 * x := by apply Real.sq_sqrt; linarith
  let v := y + 3 * x
  have u_v_add : u + v = 12 := by unfold u v; linarith
  have squares : u^2 * v + u ^ 2 = 144 := by 
    rw [u_sq]; unfold v; rw [← h₁]; ring

  have v_eq : v = 12 - u := by linarith 
  have u_eq' : u^3 - 13 * u^2 + 144 = 0 := by
    have equ2 := squares
    rw [v_eq] at equ2
    nlinarith [sq_nonneg (u ^ 2), sq_nonneg ((12 - u) ^ 2), u_pos]

  have u_eq'' : (u-4) * (u - 12) * (u - (-3)) = 0 := by 
    nlinarith
  simp only [mul_eq_zero] at u_eq''
  rw [sub_eq_zero, sub_eq_zero, sub_eq_zero] at u_eq''
  rcases u_eq'' with ((eq|eq)|eq)

  · -- trip root, caused by linear part, u=4
    have u_eq4 : u = 4 := by linarith 
    have h_eq_1 : y - 3 * x = 16 := by
      calc
        y - 3 * x = u^2 := by linarith 
        _ = 4 ^ 2 := by rw [show u = 4 from u_eq4]
        _ = (16 : ℝ) := by norm_num 
    have h_eq_2 : y + 3 * x = 8 := by 
      linarith [v_eq, u_eq4]
    have h_eq3 : y = 12 := by 
      nlinarith 
    have h_eq4 : x = -4 / 3 := by 
      nlinarith 
    right 
    tauto

  · -- trip root, caused by linear part, u=12, but return sq < 0
    have u_eq12 : u = 12 := by linarith 
    have h_eq_1 : y - 3 * x = 144 := by 
      calc 
        y - 3 * x = u^2 := by linarith 
        _ = 12 ^ 2 := by rw [show u = 12 from u_eq12]
        _ = (144 : ℝ) := by norm_num 
    have h_eq_2 : y + 3 * x = (0 : ℝ) := by
      linarith [v_eq, u_eq12]
    have h_eq3 : y = 72 := by 
      nlinarith 
    have h_eq4 : x = -24 := by 
      nlinarith 
    left 
    tauto

  · -- return negative sq Root
    exfalso 
    have h_eq3 : u = -3 := by linarith 
    nlinarith [show 0 ≤ u from u_pos]