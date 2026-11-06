import Mathlib

open Finset Classical

theorem number_theory_610204 : let S := {u ∈ range 10 | ∃ a, u = 3 * a % 10 ∧ 2 * a % 10 = 4}
∑ x ∈ S, x = 7 := by
  intro S
  have h1 : S = {1, 6} := by 
    ext u 
    simp [S]
    constructor 
    · -- Assume u in S
      intro hu 
      rcases hu with ⟨hu, a, h1, h2⟩
      have h3 : a % 10 = 2 ∨ a % 10 = 7 := by 
        omega 
      rcases h3 with (h | h)
      · -- a % 10 = 2 
        omega 
      · -- a % 10 = 7 
        omega 
    · -- Assume u in {1, 6}
      rintro (rfl | rfl)
      · -- u = 1
        constructor 
        · norm_num 
        · use 7 
          all_goals norm_num 
      · -- u = 6
        constructor 
        · norm_num 
        · use 2 
          all_goals norm_num
  rw [h1]
  norm_num [Finset.sum_insert, Finset.sum_singleton]