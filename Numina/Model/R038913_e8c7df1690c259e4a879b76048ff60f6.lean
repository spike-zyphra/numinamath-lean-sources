import Mathlib

theorem inequalities_243671 : {n : ℕ | 2019 < Real.sqrt n ∧ Real.sqrt n < 2020}.encard = 4038 := by
  have h1 : {n : ℕ | 2019 < Real.sqrt n ∧ Real.sqrt n < 2020} = Set.Ioo (2019 ^ 2) (2020 ^ 2) := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Ioo]
    rw [Real.lt_sqrt (by norm_num), Real.sqrt_lt' (by norm_num)]
    all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_eq_toFinset_card']
  <;> try { native_decide }
  all_goals norm_num