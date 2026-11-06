import Mathlib

theorem number_theory_36814 :
    Set.encard {n : ℕ | 0 < n ∧ (n.factorial * (2 * n + 1)).Coprime 221} = 10 := by
  have h1 : {n : ℕ | 0 < n ∧ (n.factorial * (2 * n + 1)).Coprime 221} = {1, 2, 3, 4, 5, 7, 9, 10, 11, 12} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume h
      rintro ⟨hn_pos, h_coprime⟩
      have h2 : n ≤ 12 := by
        by_contra h
        push_neg at h
        have h3 : n ≥ 13 := by omega
        have h4 : ¬ (n.factorial * (2 * n + 1)).Coprime 221 := by
          have h13 : 13 ∣ n.factorial := by
            apply Nat.dvd_factorial
            all_goals linarith
          have h14 : 13 ∣ n.factorial * (2 * n + 1) := by
            apply dvd_trans h13
            simp
          have h15 : 13 ∣ 221 := by norm_num
          have h16 : ¬ (n.factorial * (2 * n + 1)).Coprime 221 := by
            rw [Nat.Coprime] at *
            have h17 : Nat.gcd (n.factorial * (2 * n + 1)) 221 > 1 := by
              have h18 : 13 ∣ Nat.gcd (n.factorial * (2 * n + 1)) 221 := by
                apply Nat.dvd_gcd
                exact h14
                exact h15
              have h19 : Nat.gcd (n.factorial * (2 * n + 1)) 221 ≥ 13 := by
                omega
              omega
            omega
          exact h16
        contradiction
      interval_cases n <;> norm_num [Nat.factorial] at h_coprime ⊢
      <;> tauto
    · -- Show that if n in {1, 2, 3, 4, 5, 7, 9, 10, 11, 12}, then it satisfies the coprime condition.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num [Nat.factorial]
      · constructor
        · norm_num
        · norm_num [Nat.factorial]
      · constructor
        · norm_num
        · norm_num [Nat.factorial]
      · constructor
        · norm_num
        · norm_num [Nat.factorial]
      · constructor
        · norm_num
        · norm_num [Nat.factorial]
      · constructor
        · norm_num
        · norm_num [Nat.factorial]
      · constructor
        · norm_num
        · norm_num [Nat.factorial]
      · constructor
        · norm_num
        · norm_num [Nat.factorial]
      · constructor
        · norm_num
        · norm_num [Nat.factorial]
      · constructor
        · norm_num
        · norm_num [Nat.factorial]
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { linarith }