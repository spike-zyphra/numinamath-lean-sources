import Mathlib


theorem algebra_10961 :
    {x : ℝ | 5 = (x ^ 3 - 2 * x ^ 2 - 8 * x) / (x + 2)} = {-1, 5} ∧
    -1 + 5 = 4 := by
  constructor 
  · -- Show {x : ℝ | 5 = (x ^ 3 - 2 * x ^ 2 - 8 * x) / (x + 2)} = {-1, 5}
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume 5 = (x ^ 3 - 2 * x ^ 2 - 8 * x) / (x + 2) holds, prove x ∈ {-1, 5}
      intro h 
      have h1 : x + 2 ≠ 0 := by 
        by_contra h2 
        have eq1 : x = -2 := by linarith 
        rw [eq1] at h 
        norm_num [eq1] at h 
      have eq1 : x ^ 3 - 2 * x ^ 2 - 8 * x = 5 * (x + 2) := by 
        have eq2 : x + 2 ≠ 0 := h1 
        field_simp [eq2] at h ⊢ 
        linarith 
      have eq2 : x ^ 3 - 2 * x ^ 2 - 8 * x - 5 * (x + 2) = 0 := by linarith [eq1]
      have eq3 : x ^ 3 - 2 * x ^ 2 - 8 * x - 5 * (x + 2) = 
          (x + 1) * (x - 5) * (x + 2) := by ring
      have eq4 : (x + 1) * (x - 5) * (x + 2) = 0 := by 
        rw [eq3] at eq2 
        linarith 
      cases' (mul_eq_zero.mp eq4) with eq5 eq6 
      cases' (mul_eq_zero.mp eq5) with eq7 eq8 
      · -- eq7: x + 1 = 0 
        left 
        linarith 
      · -- eq8: x - 5 = 0 
        right 
        linarith 
      · -- eq6: x + 2 = 0 
        have eq8 : x = -2 := by linarith
        rw [eq8] at h
        norm_num [eq8] at h
    · -- Assume x ∈ {-1, 5}, prove 5 = (x ^ 3 - 2 * x ^ 2 - 8 * x) / (x + 2)
      rintro (h | h)
      · -- x = -1 
        rw [h] 
        norm_num 
      · -- x = 5 
        rw [h] 
        norm_num 
  · -- Prove -1 + 5 = 4 
    norm_num