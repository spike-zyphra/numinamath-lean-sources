import Mathlib

open Real Set
/-let x be a real number, y = |x-1| + |x+1|.Among the following four conclusions, the correct one is ( ). 
(A) y has no minimum value 
(B) There is only one x that makes y take the minimum value 
(C) There are infinitely many x that make y take the minimum value 
(D) There are finitely many x that make y take the minimum value-/
theorem algebra_311255 {y : ℝ → ℝ} (hy : ∀ x, y x = abs (x - 1) + abs (x + 1)) :
    IsLeast {z | ∃ x, y x = z} (y 1) ∧
    {x | y x = y 1}.Infinite := by

  have y1 : y 1 = 2 := by
    rw [hy 1]
    norm_num

  have h1 : IsLeast {z | ∃ x, y x = z} (y 1) := by
    constructor
    · -- Show y(1) is in the set
      use 1
    · -- Show y(1) is a lower bound
      intro z hz
      rcases hz with ⟨x, hx⟩
      rw [y1] at *
      rw [hy x] at hx
      have h : abs (x - 1) + abs (x + 1) ≥ 2 := by
        by_cases h1 : x ≥ 1
        · -- Case x ≥ 1
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        · -- Case -1 ≤ x < 1
          by_cases h2 : -1 ≤ x
          · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
            linarith
          · -- Case x < -1
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
            linarith
      linarith

  have h2 : {x | y x = y 1}.Infinite := by
    have h_eq : {x | y x = y 1} = Set.Icc (-1) 1 := by
      ext x
      simp [y1, hy]
      constructor
      · -- Forward direction: |x - 1| + |x + 1| = 2 → x ∈ [-1, 1]
        intro h
        by_cases h1 : x ≥ 1
        · -- Case x ≥ 1
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
          constructor <;> linarith
        · -- Case -1 ≤ x < 1
          by_cases h2 : -1 ≤ x
          · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h
            constructor <;> linarith
          · -- Case x < -1
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
            linarith
      · -- Backward direction: x ∈ [-1, 1] → |x - 1| + |x + 1| = 2
        rintro ⟨h1, h2⟩
        by_cases h3 : x ≥ 1
        · -- Case x = 1
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        · -- Case -1 ≤ x < 1
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
          linarith
    rw [h_eq]
    apply Set.Icc_infinite
    norm_num

  exact ⟨h1, h2⟩