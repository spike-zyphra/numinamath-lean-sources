import Mathlib
open Real

theorem algebra_93367 {a b : ℝ} (ha : a = 1 / 2) (hb : (a + 1) * (b + 1) = 2) :
arctan a + arctan b = π / 4 := by
  have ha1 : a = 1 / 2 := ha
  rw [ha1] at hb
  have hb2 : b = 1 / 3 := by
    nlinarith
  rw [ha1, hb2]
  have h1 : arctan (1 / 2 : ℝ) + arctan (1 / 3 : ℝ) = π / 4 := by
    have h2 : arctan (1 / 2 : ℝ) + arctan (1 / 3 : ℝ) = arctan ( (1 / 2 + 1 / 3) / (1 - (1 / 2) * (1 / 3)) ) := by
      rw [arctan_add]
      all_goals norm_num
    have h3 : ( (1 / 2 + 1 / 3 : ℝ) / (1 - (1 / 2) * (1 / 3)) ) = (1 : ℝ) := by
      norm_num
    rw [h2]
    rw [h3]
    have h4 : arctan (1 : ℝ) = π / 4 := by
      rw [arctan_one]
    linarith [h4]
  linarith [h1]