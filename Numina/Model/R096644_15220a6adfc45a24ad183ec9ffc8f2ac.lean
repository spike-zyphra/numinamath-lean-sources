import Mathlib

theorem algebra_527 (f : ℝ → ℝ) (hf : f = fun x => x * abs x - 2 * x + 1) :
    IsGreatest {y | ∃ x, abs (x + 1) ≤ 6 ∧ f x = y} 16 := by
  constructor
  · -- Let's show 16 is in the set
    use 5
    constructor
    · -- Show that abs (5 + 1) ≤ 6
      norm_num [abs]
    · -- Show that f 5 = 16
      simp [hf]
      norm_num [abs]
  · -- Now let's show 16 is an upper bound
    intro y
    rintro ⟨x, hx1, hx2⟩
    have h1 : -7 ≤ x := by 
      linarith [abs_le.mp hx1]
    have h2 : x ≤ 5 := by 
      linarith [abs_le.mp hx1]
    simp [hf] at hx2
    by_cases h : x ≥ 0
    · -- If x ≥ 0 then |x| = x
      rw [abs_of_nonneg h] at hx2
      nlinarith [sq_nonneg (x - 4), sq_nonneg (x - 5), sq_nonneg (x - 1), sq_nonneg (x - -1), sq_nonneg (x - -7), sq_nonneg (x - 5)]
    · -- If x < 0 then |x| = -x
      rw [abs_of_neg (lt_of_not_ge h)] at hx2
      nlinarith [sq_nonneg (x - 4), sq_nonneg (x - 5), sq_nonneg (x - 1), sq_nonneg (x - -1), sq_nonneg (x - -7), sq_nonneg (x - 5)]