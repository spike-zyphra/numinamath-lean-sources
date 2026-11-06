import Mathlib

open Set

theorem algebra_20164 (j : Icc (-1 : ℝ) 2 → ℝ) (hj : ∀ x, j x = 2 * x ^ 2 + 1) :
    range j = Icc 1 9 := by 
  ext y
  simp [hj, Set.mem_range, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- Prove that if y is in range j, then y is in [1, 9]
    rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hx1, hx2⟩
    have h1 : 0 ≤ x ^ 2 := sq_nonneg x
    have h2 : x ^ 2 ≤ 4 := by
      nlinarith [sq_nonneg x]
    constructor
    · -- Show that 1 ≤ y
      nlinarith
    · -- Show that y ≤ 9
      nlinarith
  · -- Prove that if y ∈ [1, 9], then y is in range j
    rintro ⟨hy1, hy2⟩
    use Real.sqrt ((y - 1) / 2)
    constructor
    · -- Show x ∈ [-1, 2]
      have h1 : 0 ≤ (y - 1) / 2 := by linarith
      have h2 : Real.sqrt ((y - 1) / 2) ≥ 0 := by positivity
      have h4 : (Real.sqrt ((y - 1) / 2)) ^ 2 ≤ (4 : ℝ) := by
        have h7 : (Real.sqrt ((y - 1) / 2)) ^ 2 = (y - 1) / 2 := by
          rw [Real.sq_sqrt]
          linarith
        rw [h7]
        linarith
      have h5 : Real.sqrt ((y - 1) / 2) ≤ (2 : ℝ) := by
        nlinarith [sq_nonneg (Real.sqrt ((y - 1) / 2) - 2), Real.sqrt_nonneg ((y - 1) / 2)]
      constructor
      · -- Show x ≥ -1
        nlinarith [Real.sqrt_nonneg ((y - 1) / 2)]
      · -- Show x ≤ 2
        linarith
    · -- Show that y = 2 * x ^ 2 + 1
      have h3 : (Real.sqrt ((y - 1) / 2) : ℝ) ^ 2 = (y - 1) / 2 := by
        rw [Real.sq_sqrt]
        all_goals linarith
      nlinarith [Real.sqrt_nonneg ((y - 1) / 2), h3]