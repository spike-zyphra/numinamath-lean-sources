import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_259368 {f : ℝ → ℝ}
  (hf : f = λ x => abs (x - 1) + abs (2 * x - 1) + abs (3 * x - 1) +
    abs (4 * x - 1) + abs (5 * x - 1)) :
  IsLeast (range f) (f (1 / 4)) := by 
  -- Let's compute f(1/4), it should be 7/4
  have h1 : ∀ x, f x = abs (x - 1) + abs (2 * x - 1) + abs (3 * x - 1) + abs (4 * x - 1) + abs (5 * x - 1) := by
    intro x
    rw [hf]

  have h2 : f (1 / 4 : ℝ) = 7 / 4 := by
    rw [h1]
    norm_num [abs_of_neg, abs_of_nonneg, abs_of_nonpos, abs_of_pos]

  constructor
  · -- Show that f(1/4) is in the range of f
    use 1 / 4
    all_goals simp [h2]

  · -- Show that f(1/4) is indeed the minimum value
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h3 : f x = abs (x - 1) + abs (2 * x - 1) + abs (3 * x - 1) + abs (4 * x - 1) + abs (5 * x - 1) := by
      rw [hf]
    have h4 : f (1 / 4 : ℝ) ≤ f x := by
      rw [h2, h3]
      cases' abs_cases (x - 1) with h1 h1
      · cases' abs_cases (2 * x - 1) with h2 h2
        · cases' abs_cases (3 * x - 1) with h3 h3
          · cases' abs_cases (4 * x - 1) with h4 h4
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x ≥ 1
                linarith
              · -- Case 4/5 ≤ x < 1
                linarith
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case 3/4 ≤ x < 4/5
                linarith
              · -- Case 1/2 ≤ x < 3/4
                linarith
          · cases' abs_cases (4 * x - 1) with h4 h4
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case 2/5 ≤ x < 1/2
                linarith
              · -- Case 1/3 ≤ x < 2/5
                linarith
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case 1/4 ≤ x < 1/3
                linarith
              · -- Case 1/5 ≤ x < 1/4
                linarith
        · cases' abs_cases (3 * x - 1) with h3 h3
          · cases' abs_cases (4 * x - 1) with h4 h4
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x < 1/5
                linarith
              · -- Case x < 1/5
                linarith
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x < 1/5
                linarith
              · -- Case x < 1/5
                linarith
          · cases' abs_cases (4 * x - 1) with h4 h4
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x < 1/5
                linarith
              · -- Case x < 1/5
                linarith
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x < 1/5
                linarith
              · -- Case x < 1/5
                linarith
      · cases' abs_cases (2 * x - 1) with h2 h2
        · cases' abs_cases (3 * x - 1) with h3 h3
          · cases' abs_cases (4 * x - 1) with h4 h4
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x < 1/5
                linarith
              · -- Case x < 1/5
                linarith
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x < 1/5
                linarith
              · -- Case x < 1/5
                linarith
          · cases' abs_cases (4 * x - 1) with h4 h4
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x < 1/5
                linarith
              · -- Case x < 1/5
                linarith
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x < 1/5
                linarith
              · -- Case x < 1/5
                linarith
        · cases' abs_cases (3 * x - 1) with h3 h3
          · cases' abs_cases (4 * x - 1) with h4 h4
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x < 1/5
                linarith
              · -- Case x < 1/5
                linarith
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x < 1/5
                linarith
              · -- Case x < 1/5
                linarith
          · cases' abs_cases (4 * x - 1) with h4 h4
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x < 1/5
                linarith
              · -- Case x < 1/5
                linarith
            · cases' abs_cases (5 * x - 1) with h5 h5
              · -- Case x < 1/5
                linarith
              · -- Case x < 1/5
                linarith
    linarith