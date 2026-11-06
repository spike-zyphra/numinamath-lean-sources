import Mathlib

open Real Set
open scoped BigOperators

/-Find the minumum value of the expresiion for a,b > 0:
(2*a+2*a*b-b*(b+1))^2 + (b-4*a^2+2*a*(b+1))^2) / (4*a^2+b^2)-/
theorem algebra_223632 :
  IsLeast {x | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ x = ((2*a+2*a*b-b*(b+1))^2 + (b-4*a^2+2*a*(b+1))^2) / (4*a^2+b^2)} 1 := by
  constructor
  · -- First we need to prove that 1 is achievable, i.e., 1 is in the set.
    use 1, 1 -- use a = 1, b = 1 --
    constructor
    · norm_num -- a > 0
    constructor
    · norm_num -- b > 0
    · norm_num -- Show that the expression equals 1
  · -- Now we need to prove that 1 is a lower bound for all elements in the set.
    intro x
    rintro ⟨a, b, ha, hb, h_eq⟩
    have h1 : 0 < 4 * a^2 + b^2 := by nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb] -- this is easy to see --

    -- then we turn to the inequality of division into inequality of subtraction --
    have h2 : ((2 * a + 2 * a * b - b * (b + 1)) ^ 2 + (b - 4 * a^2 + 2 * a * (b + 1)) ^ 2) - (4 * a^2 + b^2) ≥ 0 := by
      nlinarith [sq_nonneg (2 * a + 2 * a * b - b * (b + 1)), sq_nonneg (b - 4 * a^2 + 2 * a * (b + 1)),
        sq_nonneg (2 * a - b), sq_nonneg (b - 1), sq_nonneg (a - 1), sq_nonneg (a - b),
        sq_nonneg (2 * a - b - 1), sq_nonneg (b + 2 * a - 1),
        sq_nonneg (2 * a + 2 * a * b - b * (b + 1) - (2 * a - b) * (b + 1)),
        sq_nonneg (b - 4 * a^2 + 2 * a * (b + 1) - (b + 2 * a - 1) * (2 * a + 1))]

    -- we are almost done, now just modify the inequality to get the desired result --
    have h3 : ((2 * a + 2 * a * b - b * (b + 1)) ^ 2 + (b - 4 * a^2 + 2 * a * (b + 1)) ^ 2) ≥ (4 * a^2 + b^2) := by linarith
    have h4 : ((2 * a + 2 * a * b - b * (b + 1)) ^ 2 + (b - 4 * a^2 + 2 * a * (b + 1)) ^ 2) / (4 * a^2 + b^2) ≥ 1 := by
      have h5 : ((2 * a + 2 * a * b - b * (b + 1)) ^ 2 + (b - 4 * a^2 + 2 * a * (b + 1)) ^ 2) / (4 * a^2 + b^2) ≥ (4 * a^2 + b^2) / (4 * a^2 + b^2) := by
        apply div_le_div_of_nonneg_right
        · linarith
        · nlinarith
      have h6 : (4 * a^2 + b^2) / (4 * a^2 + b^2) = 1 := by
        field_simp [h1]
      linarith
    rw [h_eq]
    linarith
    