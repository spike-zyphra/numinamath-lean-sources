import Mathlib

theorem algebra_202442 : (100 - 63 = 37) ∧ (96 - 49 = 47) ∧ (83 - 26 = 57) ∧
    (27 / 9 = 3) ∧ (18 / 9 = 2) ∧ (45 / 9 = 5) := by
  norm_num
  all_goals try { tauto }
  all_goals try { trivial }
  all_goals try { tauto }
  all_goals try { trivial }