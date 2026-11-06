import Mathlib

def p (n : ℕ) := (Nat.digits 10 n).prod
def s (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_174716 :
    {n | n ∈ Finset.Icc 10 99 ∧ n = p n + s n} =
    {19, 29, 39, 49, 59, 69, 79, 89, 99} := by 
  ext n 
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume n is in {n | n ∈ Finset.Icc 10 99 ∧ n = p n + s n}
    rintro ⟨⟨hn1, hn2⟩, hneq⟩
    interval_cases n <;> norm_num [p, s] at hneq ⊢ <;> omega 
  · -- Assume n is in {19, 29, 39, 49, 59, 69, 79, 89, 99}
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · constructor
      · norm_num 
      · norm_num [p, s]
    · constructor
      · norm_num 
      · norm_num [p, s]
    · constructor
      · norm_num 
      · norm_num [p, s]
    · constructor
      · norm_num 
      · norm_num [p, s]
    · constructor
      · norm_num 
      · norm_num [p, s]
    · constructor
      · norm_num 
      · norm_num [p, s]
    · constructor
      · norm_num 
      · norm_num [p, s]
    · constructor
      · norm_num 
      · norm_num [p, s]
    · constructor
      · norm_num 
      · norm_num [p, s]