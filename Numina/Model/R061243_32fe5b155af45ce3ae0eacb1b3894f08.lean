import Mathlib

theorem number_theory_98866 (d : ℕ) (hd : d > 0) (hne2 : d ≠ 2) (hne5 : d ≠ 5) (hne13 : d ≠ 13) :
    ∃ x y, (x = 2 ∧ y = 5) ∨ (x = 2 ∧ y = 13) ∨ (x = 5 ∧ y = 13) ∨ (x = d ∧ y = 2) ∨
    (x = d ∧ y = 5) ∨ (x = d ∧ y = 13) ∧ ¬ ∃ m, m^2 = x * y - 1 := by
  refine' ⟨d, 5, _⟩
  simp [hne5]
  <;> try { tauto }
  <;> try { linarith }
  all_goals try { tauto }
  <;> try { linarith }
  <;> try { norm_num }
  all_goals try { norm_num }
  <;> try { native_decide }
  <;> try { native_decide }