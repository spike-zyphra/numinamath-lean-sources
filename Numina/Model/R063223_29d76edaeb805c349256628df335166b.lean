import Mathlib

theorem number_theory_19009 : IsGreatest {n : ℕ | ∃ k, 0 < k ∧ n = k + 2 ∧
    100 ≤ k + (k + 1) + (k + 2) ∧ k + (k + 1) + (k + 2) < 220 ∧ Nat.digits 10 (k + (k + 1) + (k + 2)) = List.reverse (Nat.digits 10 (k + (k + 1) + (k + 2)))} 58 := by 
  constructor 
  · -- Show that 58 is in the set 
    use 56 
    all_goals norm_num
    <;> native_decide 
  · -- Show that 58 is the greatest in the set 
    intro n hn 
    rcases hn with ⟨k, hk0, hkn, hsum1, hsum2, hp⟩
    have h' : k < 73 := by 
      omega 
    by_contra h 
    push_neg at h 
    have h' : k >= 57 := by omega 
    interval_cases k <;> norm_num at hp 
      <;> norm_num at hsum1 hsum2 
      <;> norm_num at hp 
      <;> omega 
    <;> omega 
    <;> norm_num at hp
    <;> omega