import Mathlib

theorem algebra_133622 {P : Polynomial ℤ} (hP1 : P.eval 11 = 2021) (hP2 : P.eval 13 = 2021) :
    IsLeast {x | 0 < x ∧ ∃ P : Polynomial ℤ, P.eval 11 = 2021 ∧ P.eval 13 = 2021 ∧ P.eval 0 = x} 19 := by
  constructor
  · -- Show 19 is in the set
    constructor
    · norm_num
    · use (2021 - 14 * (Polynomial.X - 11) * (Polynomial.X - 13))
      constructor
      · -- Verify P(11) = 2021
        simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        <;> ring
      constructor
      · -- Verify P(13) = 2021
        simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        <;> ring
      · -- Verify P(0) = 19
        simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        <;> ring
  · -- Show 19 is the least
    intro x hx
    rcases hx with ⟨hx_pos, P, hP11, hP13, hP0⟩
    have h1 : (0 : ℤ) - 11 ∣ P.eval 0 - P.eval 11 := by
      apply Polynomial.sub_dvd_eval_sub
    have h2 : (0 : ℤ) - 13 ∣ P.eval 0 - P.eval 13 := by
      apply Polynomial.sub_dvd_eval_sub
    rw [hP0] at h1
    rw [hP11] at h1
    rw [hP0] at h2
    rw [hP13] at h2
    norm_num at h1 h2
    omega