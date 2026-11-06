import Mathlib

theorem number_theory_198788 :
    {n | 0 < n ∧ ∃ k : ℕ, Nat.factorial n ∣ 2 * k ^ 2 + k + 2018} = {1, 2, 3, 4} := by 
  ext n 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
            Set.union_insert, Set.union_singleton]
  constructor 
  · -- First direction: if n in left side, then n in right side.
    intro h
    rcases h with ⟨hn_pos, ⟨k, hk⟩⟩
    by_cases h1 : n ≤ 4
    · -- If n <= 4 and n > 0, then n ∈ {1, 2, 3, 4}.
      have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by 
        interval_cases n <;> tauto
      tauto
    · -- If n > 4.
      have h2 : n > 4 := by 
        omega
      have h3 : 5 ∣ Nat.factorial n := by
        apply Nat.dvd_factorial
        all_goals 
          omega
      have h4 : 5 ∣ 2 * k ^ 2 + k + 2018 := by
        have h5 : Nat.factorial n ∣ 2 * k ^ 2 + k + 2018 := hk
        exact dvd_trans h3 h5
      have h5 : (2 * k ^ 2 + k + 2018) % 5 = 0 := by 
        omega
      have h6 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by 
        omega
      rcases h6 with (h | h | h | h | h)
      · -- Case k % 5 = 0
        simp [Nat.add_mod, Nat.mul_mod, h, Nat.pow_mod] at h5
      · -- Case k % 5 = 1
        simp [Nat.add_mod, Nat.mul_mod, h, Nat.pow_mod] at h5
      · -- Case k % 5 = 2
        simp [Nat.add_mod, Nat.mul_mod, h, Nat.pow_mod] at h5
      · -- Case k % 5 = 3
        simp [Nat.add_mod, Nat.mul_mod, h, Nat.pow_mod] at h5
      · -- Case k % 5 = 4
        simp [Nat.add_mod, Nat.mul_mod, h, Nat.pow_mod] at h5
  · -- Second direction: if n in right side, then n in left side.
    rintro (rfl | rfl | rfl | rfl)
    · -- n = 1
      constructor 
      · norm_num 
      · use 0 
        norm_num [Nat.factorial]
    · -- n = 2 
      constructor 
      · norm_num 
      · use 0 
        norm_num [Nat.factorial]
    · -- n = 3 
      constructor 
      · norm_num 
      · use 2 
        norm_num [Nat.factorial]
    · -- n = 4 
      constructor 
      · norm_num 
      · use 14 
        norm_num [Nat.factorial]