import Mathlib

/-let f(x) = |x + 1| + |x| - |x - 2|. Then the number of different solutions
of f(f(x)) + 1 = 0 is -/

def f: ℝ → ℝ := fun x => |x + 1| + |x| - |x - 2|

theorem algebra_164686: {x: ℝ | f (f x) + 1 = 0}.encard = 3 := by
  have h1 : {x : ℝ | f (f x) + 1 = 0} = {-3, -1, (1 / 3 : ℝ)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, f]
    constructor
    · -- First implication: f(f(x)) + 1 = 0 → { -3, -1, 1/3 }
      intro h_eq
      have eq2 : (|(|x + 1| + |x| - |x - 2|) + 1| + |(|x + 1| + |x| - |x - 2|)| - |(|x + 1| + |x| - |x - 2|) - 2| : ℝ) = -1 := by 
        linarith
      by_cases h1 : x < -1
      · -- x < -1
        have eqfx : |x + 1| + |x| - |x - 2| = -x - 3 := by
          rw [abs_of_neg (show x + 1 < 0 by linarith), abs_of_neg (show x < 0 by linarith), abs_of_neg (show x - 2 < 0 by linarith)]
          all_goals linarith
        rw [eqfx] at eq2
        have : x = -3 := by
          cases' abs_cases (-x - 3 + 1 : ℝ) with h11 h11 <;> 
          cases' abs_cases (-x - 3 : ℝ) with h12 h12 <;> 
          cases' abs_cases (-x - 3 - 2 : ℝ) with h13 h13 <;> 
          all_goals 
            nlinarith 
        tauto
      by_cases h2 : x ≤ 0
      · -- -1 ≤ x ≤ 0
        have eqfx : |x + 1| + |x| - |x - 2| = x - 1 := by 
          rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), abs_of_nonpos (show x ≤ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith)]
          all_goals linarith
        rw [eqfx] at eq2
        have : x = -1 := by
          cases' abs_cases (x - 1 + 1 : ℝ) with h11 h11 <;> 
          cases' abs_cases (x - 1 : ℝ) with h12 h12 <;> 
          cases' abs_cases (x - 1 - 2 : ℝ) with h13 h13 <;> 
          all_goals 
            nlinarith
        tauto
      by_cases h3 : x ≤ 2
      · -- 0 < x ≤ 2
        have eqfx : |x + 1| + |x| - |x - 2| = 3 * x - 1 := by
          rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), abs_of_nonneg (show x ≥ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith)]
          all_goals linarith
        rw [eqfx] at eq2
        have : x = (1 / 3 : ℝ) := by
          cases' abs_cases ((3 * x - 1) + 1 : ℝ) with h11 h11 <;> 
          cases' abs_cases (3 * x - 1 : ℝ) with h12 h12 <;> 
          cases' abs_cases ((3 * x - 1) - 2 : ℝ) with h13 h13 <;> 
          all_goals 
            nlinarith
        tauto
      · -- x > 2
        have eqfx : |x + 1| + |x| - |x - 2| = x + 3 := by
          rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), abs_of_nonneg (show x ≥ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith)]
          all_goals linarith
        rw [eqfx] at eq2
        exfalso
        cases' abs_cases (x + 3 + 1 : ℝ) with h11 h11 <;> 
          cases' abs_cases (x + 3 : ℝ) with h12 h12 <;> 
            cases' abs_cases (x + 3 - 2 : ℝ) with h13 h13 <;> 
              all_goals 
                nlinarith
    · -- Backward implication
      rintro (rfl | rfl | rfl)
      · -- x = -3
        norm_num [abs_of_nonpos, abs_of_nonneg, abs_of_neg]
      · -- x = -1
        norm_num [abs_of_nonpos, abs_of_nonneg, abs_of_neg]
      · -- x = 1/3
        norm_num [abs_of_nonpos, abs_of_nonneg, abs_of_neg]
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals norm_num