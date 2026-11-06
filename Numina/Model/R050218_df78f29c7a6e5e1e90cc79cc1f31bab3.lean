import Mathlib

theorem algebra_8147 :
  Set.Infinite {(x : ℝ) | abs (x - 2) + abs (x - 3) = 1} := by
  have h1 : {x : ℝ | abs (x - 2) + abs (x - 3) = 1} = Set.Icc 2 3 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- First, we prove that if $|x-2| + |x-3| = 1$, then $2 \leq x \leq 3$
      intro h
      by_cases h2 : x ≥ 2
      · -- Case where $x \geq 2$
        by_cases h3 : x ≥ 3
        · -- Case where $x \geq 3$
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
          constructor <;> linarith
        · -- Case where $2 \leq x < 3$
          rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h
          constructor <;> linarith
      · -- Case where $x < 2$
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
        constructor <;> linarith
    · -- Now, we prove that if $2 \leq x \leq 3$, then $|x-2| + |x-3| = 1$
      rintro ⟨h2, h3⟩
      by_cases h4 : x ≥ 2
      · -- Case where $2 \leq x$
        by_cases h5 : x ≥ 3
        · -- Case where $x \geq 3$
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        · -- Case where $2 \leq x < 3$
          rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          linarith
      · -- Case where $x < 2$, which is impossible
        linarith
  rw [h1]
  apply Set.Icc_infinite
  all_goals norm_num