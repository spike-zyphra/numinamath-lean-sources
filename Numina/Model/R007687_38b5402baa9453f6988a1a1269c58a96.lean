import Mathlib

theorem algebra_105210 :
    {x : ℚ | x ^ 3 + (x + 1) ^ 3 + (x + 2) ^ 3 = (x + 3) ^ 3} = {3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Forward direction: If x is a solution, then x = 3
    intro h_eq
    have eq1 : x ^ 3 + (x + 1) ^ 3 + (x + 2) ^ 3 - (x + 3) ^ 3 = 0 := by linarith
    have h_eq2 : 2 * x ^ 3 - 12 * x - 18 = 0 := by
      ring_nf at eq1 ⊢
      linarith
    have h_eq4 : (x - 3) * (2 * x ^ 2 + 6 * x + 6) = 0 := by 
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 3), sq_nonneg (x + 3 / 2)]
    cases' (mul_eq_zero.mp h_eq4) with h_eq6 h_eq7
    · -- Case h_eq6: x - 3 = 0, so x = 3
      linarith
    · -- Case h_eq7: 2x^2 + 6x + 6 = 0 
      have h_eq8 : 2 * x ^ 2 + 6 * x + 6 = 0 := by linarith
      have h_eq9 : x ^ 2 + 3 * x + 3 = 0 := by 
        nlinarith 
      have h_eq10 : (x + 3/2)^2 + 3/4 = 0 := by
        nlinarith 
      have h_eq11 : (x + 3/2)^2 ≥ 0 := by 
        apply sq_nonneg 
      nlinarith 
  · -- Backward direction: If x = 3, then it's a solution 
    intro h_eq 
    rw [h_eq] 
    norm_num