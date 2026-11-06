import Mathlib

theorem algebra_215027 (k : ℝ) (h : ∃ x, x^3 + k * x - 128 = 0 ∧ deriv (fun x => x^3 + k * x - 128) x = 0) :
    k = -48 := by 
  rcases h with ⟨x, hx1, hx2⟩
  have h_deriv : deriv (fun x => x^3 + k * x - 128) x = 3 * x^2 + k := by 
    simp [deriv_const, deriv_pow, deriv_mul, deriv_id', mul_comm k, mul_assoc, sub_eq_add_neg]
    -- The derivativeis computed here.
    <;> field_simp <;> ring_nf <;> simp [mul_comm k] <;> ring 
  rw [h_deriv] at hx2 
  have eq1 : k = -3 * x^2 := by 
    nlinarith 
  rw [eq1] at hx1 
  have eq2 : x^3 + (-3 * x^2) * x - 128 = 0 := by linarith
  have eq3 : -2 * x^3 - 128 = 0 := by 
    nlinarith 
  have eq4 : x^3 = -64 := by 
    nlinarith 
  have hx_eq : x = -4 := by
    have h1 : x^3 + 64 = 0 := by 
      nlinarith 
    have h2 : (x + 4) * (x^2 - 4*x + 16) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h2) with h3 h4 
    · -- h3: x + 4 = 0
      linarith 
    · -- h4: x^2 - 4*x + 16 = 0 
      have : x^2 - 4*x + 16 > 0 := by 
        nlinarith [sq_nonneg (x - 2)]
      nlinarith 
  rw [hx_eq] at eq1 
  nlinarith