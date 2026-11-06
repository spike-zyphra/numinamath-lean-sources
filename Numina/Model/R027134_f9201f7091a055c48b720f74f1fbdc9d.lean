import Mathlib

def fib (n : ℕ) : ℕ := match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

theorem number_theory_188981 :
    Set.ncard {n | n ≤ 100 ∧ 13 ∣ fib n} = 15 := by 
  have h1 : {n | n ≤ 100 ∧ 13 ∣ fib n} = {0, 7, 14, 21, 28, 35, 42, 49, 56, 63, 70, 77, 84, 91, 98} := by 
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Forward: If n ≤ 100 and 13 ∣ fib n then n ∈ {0,7,14,21,28,35,42,49,56,63,70,77,84,91,98}
      intro h
      rcases h with ⟨hn1, hn2⟩
      have h2 : n ≤ 100 := hn1
      interval_cases n <;> norm_num [fib] at hn2 ⊢ <;> omega
    · -- Backward: If n in {0,7,14,21,28,35,42,49,56,63,70,77,84,91,98} then n ≤ 100 and 13 ∣ fib n
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 0
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 7
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 14
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 21
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 28
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 35
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 42
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 49
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 56
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 63
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 70
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 77
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 84
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 91
        constructor
        · norm_num
        · norm_num [fib]
      · -- n = 98
        constructor
        · norm_num
        · norm_num [fib]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]