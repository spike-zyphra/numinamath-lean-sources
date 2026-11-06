import Mathlib

theorem inequalities_180110 : {x : ℕ | 2014 < Real.sqrt x ∧ Real.sqrt x < 2015}.encard = 4028 := by
  have h1 : {x : ℕ | 2014 < Real.sqrt x ∧ Real.sqrt x < 2015} = 
      Set.Ioo (2014^2) (2015^2) := by
    ext x
    simp
    rw [Real.lt_sqrt (by norm_num), Real.sqrt_lt (by norm_num)]
    all_goals norm_num
    all_goals tauto
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_eq_toFinset_card']
  <;> try native_decide