import Mathlib

open Real Set

theorem algebra_311255 {y : ℝ → ℝ} (hy : ∀ x, y x = abs (x - 1) + abs (x + 1)) :
    IsLeast {z | ∃ x, y x = z} (y 1) ∧
    {x | y x = y 1}.Infinite := by
  have h1 : y 1 = 2 := by
    rw [hy]
    norm_num [abs_of_nonneg]
  constructor
  · -- First part: is least
    constructor
    · -- Exists 1, y1 = 2
      use 1
      all_goals
        norm_num [h1]
    · -- For all z in range, need to show right implication in min least.
      rintro z ⟨x, hx⟩
      have hx': y x = z := hx
      rw [hy] at hx'
      have h_eq : abs (x - 1) + abs (x + 1) ≥ 2 := by
        by_cases h1 : x ≥ 1
        · -- Case x >= 1
          rw [abs_of_nonneg (show (x - 1 : ℝ) ≥ 0 by linarith), abs_of_nonneg (show (x + 1 : ℝ) ≥ 0 by linarith)]
          nlinarith
        by_cases h2 : x ≤ -1
        · -- Case x <= -1
          rw [abs_of_nonpos (show (x - 1 : ℝ) ≤ 0 by linarith), abs_of_nonpos (show (x + 1 : ℝ) ≤ 0 by linarith)]
          all_goals
            nlinarith
        · -- Case -1 < x < 1
          rw [abs_of_nonpos (show (x - 1 : ℝ) ≤ 0 by linarith), abs_of_nonneg (show (x + 1 : ℝ) ≥ 0 by linarith)]
          all_goals
            nlinarith
      linarith
  · -- Show that {x | y x = 2} is infinite.
    rw [h1]
    have h4 : {a : ℝ | y a = 2} = Set.Icc (-1 : ℝ) (1 : ℝ) := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · -- Let ha be a value from the original, the a in T.
        intro ha
        have h_eq : abs (a - 1) + abs (a + 1) = 2 := by
          rw [← ha, hy]
        by_cases h1 : a ≥ 1
        · -- Case a >= 1
          rw [abs_of_nonneg (show a - 1 ≥ 0 by linarith), abs_of_nonneg (show a + 1 ≥ 0 by linarith)] at h_eq
          constructor
          · linarith
          · linarith
        by_cases h2 : a ≤ -1
        · -- Case a ≤ -1
          rw [abs_of_nonpos (show a - 1 ≤ 0 by linarith), abs_of_nonpos (show a + 1 ≤ 0 by linarith)] at h_eq
          all_goals
            constructor
            · linarith
            · linarith
        · -- Case -1 < a < 1
          rw [abs_of_nonpos (show a - 1 ≤ 0 by linarith), abs_of_nonneg (show a + 1 ≥ 0 by linarith)] at h_eq
          all_goals
            constructor
            · nlinarith
            · nlinarith
      · -- Show that if a is in the interval, then it is in the set.
        rintro ⟨ha1, ha2⟩
        have h_eq : abs (a - 1) + abs (a + 1) = 2 := by
          rw [abs_of_nonpos (show a - 1 ≤ 0 by linarith), abs_of_nonneg (show a + 1 ≥ 0 by linarith)]
          all_goals
            linarith
        rw [← h_eq]
        rw [hy]
    rw [h4]
    apply Set.Icc_infinite
    all_goals norm_num