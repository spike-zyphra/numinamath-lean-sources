import Mathlib

open Real Set

theorem inequalities_47525 (a : ℝ) (ha : a ∈ Ioo 0 (π/2)) :
    1 / tan (a/2) > 1 + 1 / tan a := by
  rcases ha with ⟨ha1, ha2⟩
  have ha3 : 0 < a := ha1
  have ha4 : a < π / 2 := ha2
  have ha5 : 0 < a / 2 := by linarith
  have ha6 : a / 2 < π / 4 := by linarith [show π > 0 by exact pi_pos, ha4]
  have ht1 : 0 < tan (a / 2) := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    · linarith
    · -- Show that a/2 < π/2
      linarith [show π > 0 by exact pi_pos, ha4]
  have ht2 : tan (a / 2) < 1 := by
    have htan : tan (π / 4) = 1 := by
      rw [tan_pi_div_four]
    have h1 : a / 2 < π / 4 := by
      linarith [show π > 0 by exact pi_pos, ha4]
    have h2 : tan (a / 2) < tan (π / 4) := by
      apply Real.tan_lt_tan_of_lt_of_lt_pi_div_two
      all_goals
        linarith [show π > 0 by exact pi_pos, ha4, ha1]
    rw [htan] at h2
    all_goals linarith
  have ht3 : tan a = 2 * tan (a / 2) / (1 - tan (a / 2) ^ 2) := by
    rw [←tan_two_mul]
    all_goals ring_nf
  have ht6 : 1 - tan (a / 2) ^ 2 > 0 := by
    nlinarith [sq_pos_of_pos ht1, sq_nonneg (tan (a / 2) - 1)]
  have ht7 : 1 / tan (a / 2) - (1 + 1 / tan a) > 0 := by
    have ht8 : tan a = 2 * tan (a / 2) / (1 - tan (a / 2) ^ 2) := ht3
    rw [ht8]
    have ht9 : 1 - tan (a / 2) ^ 2 > 0 := ht6
    have ht10 : 0 < tan (a / 2) := ht1
    have ht11 : (tan (a / 2) - 1) ^ 2 > 0 := by
      nlinarith
    have ht12 : 1 / tan (a / 2) - (1 + 1 / (2 * tan (a / 2) / (1 - tan (a / 2) ^ 2))) =
        ( (tan (a / 2) - 1) ^ 2 ) / (2 * tan (a / 2) ) := by
      field_simp [(show tan (a / 2) ≠ 0 by nlinarith), (show 1 - tan (a / 2) ^ 2 ≠ 0 by nlinarith)]
      nlinarith [sq_pos_of_pos ht1]
    rw [ht12]
    have ht14 : (tan (a / 2) - 1) ^ 2 / (2 * tan (a / 2) ) > 0 := by
      apply div_pos
      · linarith
      all_goals
        nlinarith
    linarith
  linarith