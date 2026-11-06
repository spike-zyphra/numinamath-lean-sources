import Mathlib

theorem algebra_133667 {P : Polynomial ℤ} (hP : P.eval 19 = 2020 ∧ P.eval 21 = 2020) :
    IsLeast {x | 0 < x ∧ ∃ P : Polynomial ℤ, P.eval 19 = 2020 ∧ P.eval 21 = 2020 ∧ P.eval 0 = x} 25 := by 
  constructor
  · -- Show that 25 is in the set
    constructor
    · norm_num
    · use (Polynomial.C (2020 : ℤ) + 
            (Polynomial.X - Polynomial.C 19) * (Polynomial.X - Polynomial.C 21) * Polynomial.C (-5))
      constructor
      · -- Check that $P(19) = 2020$
        simp [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
      constructor
      · -- Check that $P(21) = 2020$
        simp [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
      · -- Check that $P(0) = 25$
        simp [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  · -- Show that 25 is minimal in the set
    intro x hx
    rcases hx with ⟨hx_pos, P, hP19, hP21, hP0⟩
    have h2 : (P.eval 19) % 19 = (P.eval 0) % 19 := by
      have h3 : (19 : Int) % 19 = 0 := by norm_num
      have h4 : (0 : Int) % 19 = 0 := by norm_num
      have h11 : (19 - (0 : Int)) ∣ (P.eval 19 - P.eval 0) := by
        apply P.sub_dvd_eval_sub
      have h12 : (19 - (0 : Int)) = (19 : Int) := by norm_num
      rw [h12] at h11
      omega
    have h3 : (P.eval 21) % 21 = (P.eval 0) % 21 := by
      have h8 : (21 : Int) % 21 = 0 := by norm_num
      have h9 : (0 : Int) % 21 = 0 := by norm_num
      have h11 : (21 - (0 : Int)) ∣ (P.eval 21 - P.eval 0) := by
        apply P.sub_dvd_eval_sub
      have h12 : (21 - (0 : Int)) = (21 : Int) := by norm_num
      rw [h12] at h11
      omega
    have h4 : (P.eval 0) % 19 = 6 := by
      omega
    have h5 : (P.eval 0) % 21 = 4 := by
      omega
    omega