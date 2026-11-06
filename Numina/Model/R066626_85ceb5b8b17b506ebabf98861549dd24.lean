import Mathlib

def isCurious (n : ℕ) : Prop :=
  n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).all (fun d => d ≠ 0) ∧
  n ∣ (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) ∧
  (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) < 100 ∧
  (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) > 9

theorem number_theory_250189 :
    {n | isCurious n} = {11, 22, 33, 44, 55, 66, 77, 88, 99} := by 
  ext n
  simp [isCurious, Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor 
  · -- Assume n is curious, prove n ∈ {11, 22, 33, 44, 55, 66, 77, 88, 99}
    intro h
    rcases h with ⟨⟨hn1, hn2⟩, hn3, hn4, hn5, hn6⟩
    interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at hn3 hn4 hn5 hn6 ⊢
      <;> try { tauto }
      <;> try { omega }
  · -- Assume n ∈ {11, 22, 33, 44, 55, 66, 77, 88, 99}, prove n is curious
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- Check n = 11
      constructor 
      · -- Show 11 in [10, 99]
        simp 
      constructor 
      · -- Show digits all not zero 
        native_decide 
      constructor 
      · -- Show 11 divides 11
        native_decide 
      constructor 
      · -- Show reversed digits < 100
        native_decide 
      · -- Show reversed digits > 9
        native_decide 
    · -- Check n = 22
      constructor 
      · -- Show 22 in [10, 99]
        simp 
      constructor 
      · -- Show digits all not zero 
        native_decide 
      constructor 
      · -- Show 22 divides 22
        native_decide 
      constructor 
      · -- Show reversed digits < 100
        native_decide 
      · -- Show reversed digits > 9
        native_decide 
    · -- Check n = 33
      constructor 
      · -- Show 33 in [10, 99]
        simp 
      constructor 
      · -- Show digits all not zero 
        native_decide 
      constructor 
      · -- Show 33 divides 33
        native_decide 
      constructor 
      · -- Show reversed digits < 100
        native_decide 
      · -- Show reversed digits > 9
        native_decide 
    · -- Check n = 44
      constructor 
      · -- Show 44 in [10, 99]
        simp 
      constructor 
      · -- Show digits all not zero 
        native_decide 
      constructor 
      · -- Show 44 divides 44
        native_decide 
      constructor 
      · -- Show reversed digits < 100
        native_decide 
      · -- Show reversed digits > 9
        native_decide 
    · -- Check n = 55
      constructor 
      · -- Show 55 in [10, 99]
        simp 
      constructor 
      · -- Show digits all not zero 
        native_decide 
      constructor 
      · -- Show 55 divides 55
        native_decide 
      constructor 
      · -- Show reversed digits < 100
        native_decide 
      · -- Show reversed digits > 9
        native_decide 
    · -- Check n = 66
      constructor 
      · -- Show 66 in [10, 99]
        simp 
      constructor 
      · -- Show digits all not zero 
        native_decide 
      constructor 
      · -- Show 66 divides 66
        native_decide 
      constructor 
      · -- Show reversed digits < 100
        native_decide 
      · -- Show reversed digits > 9
        native_decide 
    · -- Check n = 77
      constructor 
      · -- Show 77 in [10, 99]
        simp 
      constructor 
      · -- Show digits all not zero 
        native_decide 
      constructor 
      · -- Show 77 divides 77
        native_decide 
      constructor 
      · -- Show reversed digits < 100
        native_decide 
      · -- Show reversed digits > 9
        native_decide 
    · -- Check n = 88
      constructor 
      · -- Show 88 in [10, 99]
        simp 
      constructor 
      · -- Show digits all not zero 
        native_decide 
      constructor 
      · -- Show 88 divides 88
        native_decide 
      constructor 
      · -- Show reversed digits < 100
        native_decide 
      · -- Show reversed digits > 9
        native_decide 
    · -- Check n = 99
      constructor 
      · -- Show 99 in [10, 99]
        simp 
      constructor 
      · -- Show digits all not zero 
        native_decide 
      constructor 
      · -- Show 99 divides 99
        native_decide 
      constructor 
      · -- Show reversed digits < 100
        native_decide 
      · -- Show reversed digits > 9
        native_decide