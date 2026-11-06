import Mathlib

theorem algebra_12577 : {x : ℤ | (x + 3)^2 ≤ 1}.encard = 3 := by 
  have h1 : {x : ℤ | (x + 3)^2 ≤ 1} = {-4, -3, -2} := by 
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume (x + 3)^2 ≤ 1, prove x ∈ {-4, -3, -2}
      intro h
      have h1 : x ≥ -4 := by 
        nlinarith 
      have h2 : x ≤ -2 := by 
        nlinarith 
      interval_cases x <;> tauto 
    · -- Assume x ∈ {-4, -3, -2}, prove (x + 3)^2 ≤ 1 
      rintro (rfl | rfl | rfl)
      · -- x = -4 
        norm_num 
      · -- x = -3 
        norm_num 
      · -- x = -2 
        norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try native_decide