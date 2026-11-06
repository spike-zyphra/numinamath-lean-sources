import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_206 {f : ℝ → ℝ} (hf : ∀ x, f x = abs (x - 1) + abs (x + 1)) :
    IsLeast (range f) (f (-1)) ∧
    {x | f x = f (-1)}.Infinite := by
  have h1 : ∀ x, f x = abs (x - 1) + abs (x + 1) := hf
  have h2 : f (-1) = 2 := by 
    rw [h1]
    norm_num [abs]
  constructor
  · -- Show $f(-1)$ is the least element in the range
    constructor
    · -- $f(-1)$ is in the range
      use -1
      all_goals simp [h2]
    · -- $f(-1)$ is minimal
      intro y hy
      rcases hy with ⟨x, hx⟩
      have hx1 : f x = abs (x - 1) + abs (x + 1) := h1 x
      have h3 : f x ≥ 2 := by
        have eq1 : abs (x - 1) + abs (x + 1) ≥ 2 := by 
          by_cases h14 : x ≥ 1
          · -- x ≥ 1
            rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
            all_goals linarith
          · -- x < 1
            by_cases h15 : x ≥ -1
            · -- -1 ≤ x < 1
              rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
              all_goals linarith
            · -- x < -1
              rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
              all_goals linarith
        have h8 : f x = abs (x - 1) + abs (x + 1) := hx1
        linarith [h8, eq1]
      have h4 : f (-1) ≤ f x := by
        have h5 : f x ≥ (2 : ℝ) := h3
        have h6 : f (-1) = (2 : ℝ) := h2
        linarith [h6, h5]
      linarith [h4, hx]
  · -- Show that {x | f x = f (-1)} is infinite
    have h7 : {x | f x = f (-1)} = Set.Icc (-1 : ℝ) (1 : ℝ) := by
      ext x
      simp [h2, h1]
      constructor
      · -- Assume h8: $f x = 2$, show $-1 \leq x \land x \leq 1$.
        intro h8
        have h10 : -1 ≤ x := by
          by_cases h14 : x ≥ 1
          · -- x ≥ 1
            rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h8
            all_goals nlinarith
          · -- x < 1
            by_cases h15 : x ≥ -1
            · -- -1 ≤ x < 1
              rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h8
              all_goals nlinarith
            · -- x < -1
              rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h8
              all_goals nlinarith
        have h11 : x ≤ 1 := by 
          by_cases h14 : x ≥ 1
          · -- x ≥ 1
            rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h8
            all_goals nlinarith
          · -- x < 1
            by_cases h15 : x ≥ -1
            · -- -1 ≤ x < 1
              rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h8
              all_goals nlinarith
            · -- x < -1
              rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h8
              all_goals nlinarith
        constructor <;> try linarith
      · -- Assume $-1 \leq x \land x \leq 1$, show $f x = 2$.
        rintro ⟨h10, h11⟩
        by_cases h12 : x ≥ 1
        · -- Case x = 1
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          all_goals nlinarith
        · -- Case -1 ≤ x < 1
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
          all_goals nlinarith
    rw [h7]
    apply Set.Icc_infinite
    all_goals linarith