import Mathlib

theorem algebra_232273 :
    Set.ncard {x : ℝ | (x = x + 6 ∧ x ≠ x ^ 2) ∨ (x = x ^ 2 ∧ x ≠ x + 6) ∨ (x + 6 = x ^ 2 ∧ x ≠ x + 6)} = 4 := by
  have h1 : {x : ℝ | (x = x + 6 ∧ x ≠ x ^ 2) ∨ (x = x ^ 2 ∧ x ≠ x + 6) ∨ (x + 6 = x ^ 2 ∧ x ≠ x + 6)} = {0, 1, 3, -2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume element is in left side
      rintro (h | h | h)
      · -- Case $x = x + 6 ∧ x ≠ x^2$
        exfalso
        linarith 
      · -- Case $x = x^2 ∧ x ≠ x + 6$
        rcases h with ⟨h2, h3⟩
        have h4 : x ^ 2 - x = 0 := by
          linarith 
        have h5 : x * (x - 1) = 0 := by
          linarith 
        cases' (mul_eq_zero.mp h5) with hx hx
        · -- Case $x = 0$
          left 
          linarith 
        · -- Case $x - 1 = 0$, so $x = 1$
          right 
          left 
          linarith 
      · -- Case $x + 6 = x^2 ∧ x ≠ x + 6$
        rcases h with ⟨h1, h3⟩ 
        have h2 : x ^ 2 - x - 6 = 0 := by 
          nlinarith 
        have h3 : (x - 3) * (x + 2) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.mp h3) with hx hx
        · -- Case $x - 3 = 0$, so $x = 3$ 
          right 
          right 
          left 
          linarith 
        · -- Case $x + 2 = 0$, so $x = -2$ 
          right 
          right 
          right 
          linarith 
    · -- Assume element is in right side 
      rintro (rfl | rfl | rfl | rfl)
      · -- Case $x = 0$
        simp 
      · -- Case $x = 1$
        simp 
      · -- Case $x = 3$
        simp 
        <;> norm_num 
        <;> norm_num
      · -- Case $x = -2$
        simp 
        <;> norm_num 
        <;> norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals norm_num
  all_goals norm_num