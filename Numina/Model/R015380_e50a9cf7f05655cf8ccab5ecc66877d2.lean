import Mathlib

theorem algebra_276365 (x : ℝ) (hx : x^2 ≠ 1) :
    ((1 - x^2 + x * Real.sqrt 3 * Complex.I) * (1 - x^2 - x * Real.sqrt 3 * Complex.I)) / (1 - x^6) =
    1 / (1 - x^2) := by

  have eq1 : ((1 - x^2 + x * Real.sqrt 3 * Complex.I) * (1 - x^2 - x * Real.sqrt 3 * Complex.I)) = ( (1 - x^2) ^2 + 3 * x ^2 ) := by
    simp [pow_two, Complex.ext_iff, mul_add, mul_sub, sub_mul, add_mul, mul_comm, mul_assoc, Real.sqrt_sq]
    <;> ring_nf 
    <;> norm_num 
    all_goals 
      ring_nf 
      <;> norm_num
  have h2 : (1 - x^2) ≠ 0 := by 
    intro h 
    apply hx 
    have : x^2 = 1 := by nlinarith 
    assumption 
  have h3 : (1 - x^6) ≠ 0 := by 
    by_contra h 
    have h4 : x^6 = 1 := by nlinarith 
    have h5 : x^2 = 1 := by 
      have h6 : x^6 - 1 = 0 := by linarith 
      have h7 : (x^2 - 1) * (x^4 + x^2 + 1) = 0 := by 
        ring_nf at h6 ⊢ 
        nlinarith 
      cases' (mul_eq_zero.1 h7) with h4 h7 
      · -- Case x^2 - 1 = 0 
        have h8 : x^2 = 1 := by linarith 
        tauto 
      · -- Case x^4 + x^2 + 1 = 0 
        nlinarith [sq_nonneg (x^2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
    tauto 
  rw [eq1]
  have eq4 : ( ( (1 - x^2) ^2 + 3 * x^2 ) / (1 - x^6) ) = 1 / (1 - x^2) := by 
    have eq5 : ( (1 - x^2) ^2 + 3 * x^2 ) = 1 + x^2 + x^4 := by 
      nlinarith [Real.sqrt_sq (show (0 : ℝ) ≤ 3 by norm_num)]
    have eq6 : (1 + x^2 + x^4) * (1 - x^2) = (1 - x^6) := by 
      nlinarith [sq_nonneg (x^2 - 1)]
    have h6 : (1 - x^6) ≠ 0 := h3 
    have h4 : (1 - x^2) ≠ 0 := h2 
    rw [eq5] 
    field_simp [h4, h6] 
    <;> nlinarith 
  exact_mod_cast eq4