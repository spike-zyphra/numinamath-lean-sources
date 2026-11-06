import Mathlib

open Real

lemma lemma_1 : arctan (1 / 3) + arctan (1 / 7) + arctan (1 / 13) + arctan (1 / 21) = arctan (2 / 3) := by
  have h1 : arctan (1 / 3) + arctan (1 / 7) = arctan (1 / 2) := by
    rw [arctan_add]
    all_goals norm_num
  have h2 : arctan (1 / 2) + arctan (1 / 13) = arctan (3 / 5) := by
    rw [arctan_add]
    all_goals norm_num
  have h3 : arctan (3 / 5) + arctan (1 / 21) = arctan (2 / 3) := by
    rw [arctan_add]
    all_goals norm_num
  linarith [h1, h2, h3]

theorem algebra_174607 : 10 / tan (arctan (1 / 3) + arctan (1 / 7) + arctan (1 / 13) + arctan (1 / 21)) = 15 := by
  have h1 : arctan (1 / 3) + arctan (1 / 7) + arctan (1 / 13) + arctan (1 / 21) = arctan (2 / 3) := lemma_1
  rw [h1]
  have h2 : tan (arctan (2 / 3)) = 2 / 3 := by
    rw [tan_arctan]
  rw [h2]
  all_goals norm_num