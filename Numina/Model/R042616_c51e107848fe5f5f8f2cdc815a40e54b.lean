import Mathlib

theorem algebra_233240 {A B : ℝ} (hA : A ∈ Set.Icc 100 999) (hB : B = (A / 10) + 10 * (A % 10)) (hAB : A - B = 478.8) :
    A = 532 := by
  rcases hA with ⟨h1, h2⟩
  have h10 : A % 10 = A - A / 10 * 10 := by
    simp [Nat.mod_eq_of_lt]
  rw [h10] at hB
  norm_num [hB] at hAB
  all_goals
  nlinarith