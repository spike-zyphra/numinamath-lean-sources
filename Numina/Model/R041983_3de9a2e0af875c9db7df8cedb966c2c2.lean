import Mathlib

theorem algebra_22643 : {x : ℝ | 0 ≤ (3 * x ^ 2 - 8 * x + 1) ∧ 0 ≤ (9 * x ^ 2 - 24 * x - 8) ∧ (√(3 * x ^ 2 - 8 * x + 1) + √(9 * x ^ 2 - 24 * x - 8) = 3)} = {3, -1 / 3} := by 
  ext x
  simp only [sub_nonneg, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨le1, le2, heq⟩
    have h1 : √(3 * x ^ 2 - 8 * x + 1) ≥ 0 := by positivity
    have h2 : √(9 * x ^ 2 - 24 * x - 8) ≥ 0 := by positivity
    have eq1 : √(3 * x ^ 2 - 8 * x + 1) = 3 - √(9 * x ^ 2 - 24 * x - 8) := by 
      linarith 
    have eq3 : (√(3 * x ^ 2 - 8 * x + 1))^2 = (3 - √(9 * x ^ 2 - 24 * x - 8))^2 := by 
      rw [eq1] 
    have eq4 : (√(3 * x ^ 2 - 8 * x + 1))^2 = 3 * x ^ 2 - 8 * x + 1 := Real.sq_sqrt le1
    have eq5 : (3 - √(9 * x ^ 2 - 24 * x - 8))^2 = 9 - 6 * √(9 * x ^ 2 - 24 * x - 8) + (√(9 * x ^ 2 - 24 * x - 8))^2 := by ring 
    have eq7 : (x - 3) * (x + 1/3) = 0 := by
      have eq3' : (√(3 * x ^ 2 - 8 * x + 1))^2 = 3 * x ^ 2 - 8 * x + 1 := by 
        apply Real.sq_sqrt 
        linarith
      have eq4' : (√(9 * x ^ 2 - 24 * x - 8))^2 = 9 * x ^ 2 - 24 * x - 8 := by 
        apply Real.sq_sqrt 
        nlinarith 
      nlinarith [Real.sqrt_nonneg (3 * x ^ 2 - 8 * x + 1), Real.sqrt_nonneg (9 * x ^ 2 - 24 * x - 8), 
        sq_nonneg (√(3 * x ^ 2 - 8 * x + 1) - (3 - √(9 * x ^ 2 - 24 * x - 8))), 
        sq_nonneg (√(3 * x ^ 2 - 8 * x + 1) + √(9 * x ^ 2 - 24 * x - 8) - 3), 
        mul_nonneg (Real.sqrt_nonneg (3 * x ^ 2 - 8 * x + 1)) (Real.sqrt_nonneg (9 * x ^ 2 -24 * x -8))]
    cases' (mul_eq_zero.mp eq7) with h8_1 h8_2
    · -- Case x -3 =0, x=3
      left
      linarith
    · -- Case x +1/3 =0, x=-1/3
      right
      linarith
  · -- Assume {3, -1/3}, prove in the set.
    rintro (rfl | rfl)
    · -- x = 3
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Show sqrt + sqrt =3
        have h1 : √ (3 * (3: ℝ) ^ 2 - 8 * (3) + 1) = 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h2 : √ (9 * (3: ℝ) ^ 2 - 24 * (3) - 8) = 1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h1, h2]
        all_goals norm_num
    · -- x = -1/3
      constructor
      · -- First condition
        norm_num
      constructor
      · -- Second condition
        norm_num
      · -- Show sqrt + sqrt =3
        have h1 : √ (3 * (-1/3: ℝ) ^ 2 - 8 * (-1/3) + 1) = 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h2 : √ (9 * (-1/3: ℝ) ^ 2 - 24 * (-1/3) - 8) = 1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h1, h2]
        all_goals norm_num