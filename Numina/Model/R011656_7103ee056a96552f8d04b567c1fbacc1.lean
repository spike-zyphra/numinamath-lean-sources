import Mathlib

theorem number_theory_36137 :
  {2, 4, 6, 8} ∩ {k : ℕ | ∀ n : ℕ, (n^2 + 1).divisors.card ≠ k} = ∅ := by
  ext k
  simp only [Set.mem_inter, Set.mem_singleton_iff, Set.mem_insert_iff, Set.union_insert,
    Set.union_singleton, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hk
  rcases hk with ⟨hk1, hk2⟩
  rcases hk1 with (rfl | rfl | rfl | rfl)
  · -- k = 2
    have h2 : (1 : ℕ) ^ 2 + 1 = 2 := by norm_num
    have h2card : ((1 : ℕ) ^ 2 + 1).divisors.card = 2 := by 
      rw [h2]
      native_decide
    have h21 := hk2 1
    contradiction 
  · -- k = 4
    have h4 : (3 : ℕ) ^ 2 + 1 = 10 := by norm_num 
    have h4card : ((3 : ℕ) ^ 2 + 1).divisors.card = 4 := by 
      rw [h4]
      native_decide
    have h41 := hk2 3
    contradiction 
  · -- k = 6 
    have h6 : (7 : ℕ) ^ 2 + 1 = 50 := by norm_num 
    have h6card : ((7 : ℕ) ^ 2 + 1).divisors.card = 6 := by 
      rw [h6]
      native_decide
    have h61 := hk2 7
    contradiction 
  · -- k = 8 
    have h8 : (13 : ℕ) ^ 2 + 1 = 170 := by norm_num 
    have h8card : ((13 : ℕ) ^ 2 + 1).divisors.card = 8 := by 
      rw [h8]
      native_decide
    have h81 := hk2 13 
    contradiction