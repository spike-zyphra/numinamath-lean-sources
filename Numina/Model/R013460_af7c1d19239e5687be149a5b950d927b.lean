import Mathlib

theorem number_theory_131250 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 5000 ∧ 7 ∣ x ∧ ∃ n, x = n^2} = 10 := by
  have h1 : {x : ℕ | x ∈ Finset.Icc 1 5000 ∧ 7 ∣ x ∧ ∃ n, x = n^2} = 
    {49, 196, 441, 784, 1225, 1764, 2401, 3136, 3969, 4900} := by
    ext x
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x in left side, prove right side
      rintro ⟨⟨hx1, hx2⟩, h7, ⟨n, hxn⟩⟩
      have h2 : n ≤ 70 := by
        nlinarith
      have h3 : 7 ∣ n^2 := by
        omega
      have h4 : 7 ∣ n := by
        by_contra h
        push_neg at h
        have h5 : n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
          omega
        have h6 : (n ^ 2) % 7 = 1 ∨ (n ^ 2) % 7 = 2 ∨ (n ^ 2) % 7 = 4 := by
          rcases h5 with (h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
        omega
      rcases h4 with ⟨k, hk⟩
      have h5 : x = 49 * k^2 := by
        rw [hxn]
        rw [show n = 7 * k by linarith]
        ring_nf
      have hk10 : k ≤ 10 := by
        nlinarith [h5, hx2]
      have hk1 : k ≥ 1 := by 
        by_contra h
        push_neg at h
        have hk0 : k = 0 := by
          omega
        rw [hk0] at h5
        nlinarith
      interval_cases k <;> norm_num [h5] at *
    · -- Assume x in right side, prove left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 49
        constructor
        · -- x = 49 in [1, 5000]
          norm_num
        constructor
        · -- x = 49 divisible by 7
          norm_num
        · -- x = 49 is a square
          use 7
          all_goals norm_num
      · -- x = 196
        constructor
        · -- x = 196 in [1, 5000]
          norm_num
        constructor
        · -- x = 196 divisible by 7
          norm_num
        · -- x = 196 is a square
          use 14
          all_goals norm_num
      · -- x = 441
        constructor
        · -- x = 441 in [1, 5000]
          norm_num
        constructor
        · -- x = 441 divisible by 7
          norm_num
        · -- x = 441 is a square
          use 21
          all_goals norm_num
      · -- x = 784
        constructor
        · -- x = 784 in [1, 5000]
          norm_num
        constructor
        · -- x = 784 divisible by 7
          norm_num
        · -- x = 784 is a square
          use 28
          all_goals norm_num
      · -- x = 1225
        constructor
        · -- x = 1225 in [1, 5000]
          norm_num
        constructor
        · -- x = 1225 divisible by 7
          norm_num
        · -- x = 1225 is a square
          use 35
          all_goals norm_num
      · -- x = 1764
        constructor
        · -- x = 1764 in [1, 5000]
          norm_num
        constructor
        · -- x = 1764 divisible by 7
          norm_num
        · -- x = 1764 is a square
          use 42
          all_goals norm_num
      · -- x = 2401
        constructor
        · -- x = 2401 in [1, 5000]
          norm_num
        constructor
        · -- x = 2401 divisible by 7
          norm_num
        · -- x = 2401 is a square
          use 49
          all_goals norm_num
      · -- x = 3136
        constructor
        · -- x = 3136 in [1, 5000]
          norm_num
        constructor
        · -- x = 3136 divisible by 7
          norm_num
        · -- x = 3136 is a square
          use 56
          all_goals norm_num
      · -- x = 3969
        constructor
        · -- x = 3969 in [1, 5000]
          norm_num
        constructor
        · -- x = 3969 divisible by 7
          norm_num
        · -- x = 3969 is a square
          use 63
          all_goals norm_num
      · -- x = 4900
        constructor
        · -- x = 4900 in [1, 5000]
          norm_num
        constructor
        · -- x = 4900 divisible by 7
          norm_num
        · -- x = 4900 is a square
          use 70
          all_goals norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }