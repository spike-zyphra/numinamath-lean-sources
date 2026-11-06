import Mathlib

open Real

theorem inequalities_81677 {x1 x2 x3 : ℝ} (p : ℝ → ℝ)
    (h₀ : ∀ x, p x = (x - x1) * (x - x2) * (x - x3)) :
    ∀ x, p x * iteratedDeriv 2 p x ≤ (iteratedDeriv 1 p x)^2 := by
  intro x
  have eq1 : iteratedDeriv 1 p x = 3 * x ^ 2 - 2 * (x1 + x2 + x3) * x + (x1 * x2 + x1 * x3 + x2 * x3) := by
    have h3 : p = fun x => (x - x1) * (x - x2) * (x - x3) := by
      funext y
      simp [h₀]
    rw [h3]
    simp [iteratedDeriv_succ, deriv_mul, deriv_id'', mul_comm]
    all_goals 
      field_simp 
      <;> ring_nf 
      <;> field_simp 
      <;> ring
    all_goals try linarith
  
  have eq6 : iteratedDeriv 1 p = (fun y => 3 * y ^ 2 - 2 * (x1 + x2 + x3) * y + (x1 * x2 + x1 * x3 + x2 * x3)) := by
    have h3 : p = fun x => (x - x1) * (x - x2) * (x - x3) := by
      funext y
      simp [h₀]
    have h5 : iteratedDeriv 1 p = (fun y => 3 * y ^ 2 - 2 * (x1 + x2 + x3) * y + (x1 * x2 + x1 * x3 + x2 * x3)) := by
      rw [h3]
      funext y
      simp [iteratedDeriv_succ, deriv_mul, deriv_id'', mul_comm]
      all_goals 
        field_simp 
        <;> ring_nf 
        <;> field_simp 
        <;> ring
      all_goals try linarith
    exact h5
  
  have eq6' : deriv (iteratedDeriv 1 p) x = 6 * x - 2 * (x1 + x2 + x3) := by
    rw [eq6]
    simp [deriv_pow, deriv_mul, deriv_id'', deriv_const, mul_comm, mul_assoc, add_mul, mul_add]
    all_goals 
      field_simp 
      <;> ring_nf 
      <;> field_simp 
      <;> ring
    all_goals try linarith
  
  have eq2 : iteratedDeriv 2 p x = 6 * x - 2 * (x1 + x2 + x3) := by
    have eq5 : iteratedDeriv 2 p x = deriv (iteratedDeriv 1 p) x := by
      simp [iteratedDeriv_succ, deriv_id', iteratedDeriv_one]
    rw [eq5, eq6']
  
  have eq3 : p x = (x - x1) * (x - x2) * (x - x3) := by
    apply h₀
  
  have eq4 : (iteratedDeriv 1 p x)^2 - p x * iteratedDeriv 2 p x ≥ 0 := by
    rw [eq1, eq2, eq3]
    nlinarith [sq_nonneg (x ^ 2 - (x1 + x2 + x3) * x + (x1 * x2 + x1 * x3 + x2 * x3))
      , sq_nonneg ((x - (x1 + x2 + x3)/3))
      , sq_nonneg ((x - x1) - (x - x2))
      , sq_nonneg ((x - x1) - (x - x3))
      , sq_nonneg ((x - x2) - (x - x3))
      , sq_nonneg (x - (x1))
      , sq_nonneg (x - x2)
      , sq_nonneg (x - x3)
      , sq_nonneg ((x1 - x2))
      , sq_nonneg ((x1 - x3))
      , sq_nonneg ((x2 - x3))
      ]
  nlinarith
  all_goals try linarith