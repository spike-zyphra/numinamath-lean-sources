import Mathlib

theorem algebra_20320 :
    {x | ∃y, y ^ 3 = 3 * x - 2 ∧ 3 * y = x ^ 3 + 2} = {1, -2} := by 
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the left side, prove x in the right side
    rintro ⟨y, hy1, hy2⟩
    have eq1 : y ^ 3 + 3 * y = x ^ 3 + 3 * x := by 
      nlinarith 
    have eq2 : (y - x) * (y ^ 2 + y * x + x ^ 2 + 3) = 0 := by 
      have eq1' : y ^ 3 + 3 * y = x ^ 3 + 3 * x := eq1 
      have eq3 : y ^ 3 - x ^ 3 + 3 * y - 3 * x = 0 := by 
        linarith 
      have eq4 : y ^ 3 - x ^ 3 = (y - x) * (y ^ 2 + y * x + x ^ 2) := by 
        ring 
      rw [eq4] at eq3 
      have eq5 : (y - x) * (y ^ 2 + y * x + x ^ 2) + 3 * (y - x) = 0 := by 
        linarith 
      have eq6 : (y - x) * (y ^ 2 + y * x + x ^ 2 + 3) = 0 := by 
        nlinarith 
      linarith 
    cases' (mul_eq_zero.mp eq2) with h_eq h_eq1 
    · -- If y - x = 0, then y = x 
      have h_eq2 : y = x := by linarith 
      rw [show y = x by linarith] at hy1 hy2 
      have hx_eq : x ^ 3 - 3 * x + 2 = 0 := by 
        nlinarith 
      have hx_eq2 : (x - 1) ^ 2 * (x + 2) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp hx_eq2) with h6 h7 
      · -- If (x - 1)^2 = 0, then x = 1 
        have h_eq2 : x = 1 := by 
          nlinarith 
        left 
        exact h_eq2 
      · -- If x + 2 = 0, then x = -2 
        have h_eq2 : x = -2 := by 
          nlinarith 
        right 
        exact h_eq2 
    · -- If y ^ 2 + y * x + x ^ 2 + 3 = 0 
      have h_eq1' : y ^ 2 + y * x + x ^ 2 + 3 = 0 := h_eq1 
      nlinarith [sq_nonneg (y + x), sq_nonneg (y - x), sq_nonneg (y + 1), sq_nonneg (x + 1), 
          sq_nonneg (y * x)]
  · -- Show that 1 and -2 are in the set 
    rintro (rfl | rfl)
    · -- Let x = 1, then y = 1 
      refine ⟨1, by norm_num, by norm_num⟩ 
    · -- Let x = -2, then y = -2 
      refine ⟨-2, by norm_num, by norm_num⟩