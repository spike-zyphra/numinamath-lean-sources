import Mathlib

theorem algebra_202101 (K : ℕ) (hK : K = {x : ℤ | (x^2 - 3 * x + 2)^2 - 3 * (x^2 - 3 * x) - 4 = 0}.ncard) :
    K = 2 := by 
  have h1 : {x : ℤ | (x^2 - 3 * x + 2)^2 - 3 * (x^2 - 3 * x) - 4 = 0} = {0, 3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x satisfies the equation
      intro h
      have h_eq : (x^2 - 3 * x + 2)^2 - 3 * (x^2 - 3 * x) - 4 = 0 := by 
        linarith
      have h_eq2 : (x ^ 2 - 3 * x) * (x ^ 2 - 3 * x + 1) = 0 := by
        nlinarith [sq_nonneg (x ^ 2 - 3 * x - 1)]
      cases' (mul_eq_zero.mp h_eq2) with h_eq3 h_eq4
      · 
        have h_eq5 : x * (x - 3) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h_eq5) with h_eq6 h_eq7
        · 
          left
          linarith
        · 
          right
          linarith
      · 
        have h_eq5 : x ^ 2 - 3 * x + 1 = 0 := by 
          nlinarith 
        have h2 : x ≥ 0 := by nlinarith 
        have h3 : x ≤ 3 := by nlinarith 
        interval_cases x <;> omega 
    · 
      rintro (h | h)
      · 
        rw [h]
        norm_num 
      · 
        rw [h]
        norm_num 
  rw [h1] at hK
  rw [hK]
  rw [Set.ncard_pair (by norm_num)]
  all_goals norm_num