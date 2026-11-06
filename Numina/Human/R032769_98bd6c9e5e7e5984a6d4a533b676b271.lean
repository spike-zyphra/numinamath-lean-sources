import Mathlib

open Real Set

theorem algebra_9165 {f : ℝ → ℝ} (hf : f = λ x => cos (π / 2 - x)) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (2 * π) := by
  simp [hf, cos_pi_div_two_sub]
  constructor
  . simp [pi_pos]
  . intro T ⟨hTpos, hTperiod⟩
    apply congr_fun (a := π / 2) at hTperiod
    simp at hTperiod
    obtain ⟨k, hk⟩ := sin_eq_one_iff.mp hTperiod.symm
    obtain rfl := (add_right_inj _).mp hk
    simp [pi_pos] at hTpos ⊢
    norm_cast
