import Mathlib


lemma prime_two : Prime 2 := by
  refine ⟨by norm_num, by simp, ?_⟩
  intro a b
  exact (Nat.Prime.dvd_mul (by norm_num)).mp

lemma prime_three : Prime 3 := by
  refine ⟨by norm_num, by simp, ?_⟩
  intro a b
  exact (Nat.Prime.dvd_mul (by norm_num)).mp

theorem number_theory_326648 {Z : ℕ → ℕ}
  (hZ : ∀ n, IsLeast {m | 0 < m ∧ n ∣ ∑ i ∈ Finset.range (m+1), i} (Z n)) :
  (∀ p, Odd p → p.Prime → Z p = p - 1) ∧
  (∀ a, 0 < a → Z (2 ^ a) > 2 ^ a) ∧
  (∀ a, 0 < a → Z (3 ^ a) = 3 ^ a - 1) := by


  refine ⟨?_, ?_, ?_⟩
  . intro p h_odd_p h_prime_p

    suffices IsLeast {m | 0 < m ∧ p ∣ ∑ i ∈ Finset.range (m+1), i} (p - 1) from IsLeast.unique (hZ p) this

    constructor
    . simp
      refine ⟨?_, ?_⟩
      . contrapose h_prime_p
        interval_cases p <;> norm_num
      . obtain ⟨k, hk⟩ := h_odd_p
        rw [hk, Finset.sum_range_id]
        norm_num
        rw [Nat.mul_div_assoc]
        . use (2 * k) / 2
        . use k

    . unfold lowerBounds
      simp
      intro m hm_pos h_dvd
      obtain ⟨k, hk⟩ := h_dvd
      replace hk : (∑ i ∈ Finset.range (m + 1), i) * 2 = p * (2 * k) := by
        rw [hk]
        ring
      rw [Finset.sum_range_id_mul_two] at hk
      norm_num at hk
      have h_dvd: p ∣ (m + 1) * m := by use 2 * k
      rw [Nat.Prime.dvd_mul h_prime_p] at h_dvd
      rcases h_dvd with h | h
      . apply Nat.le_of_dvd (show 0<m+1 by omega)
        exact h
      . suffices p ≤ m by omega
        apply Nat.le_of_dvd hm_pos
        exact h

  . intro a h_pos_a

    suffices IsLeast {m | 0 < m ∧ 2 ^ a ∣ ∑ i ∈ Finset.range (m+1), i} (2 ^ (a+1) - 1) by
      rw [IsLeast.unique (hZ (2 ^ a)) this]
      suffices 2 ^ 0 < 2 ^ a by omega
      apply Nat.pow_lt_pow_right
      all_goals omega

    constructor
    . simp
      let m := 2 ^ a

      have h_1_lt_m : 1 < m := by
        rw [show 1 = 2 ^ 0 by norm_num]
        apply Nat.pow_lt_pow_right
        all_goals omega

      suffices m ∣ ∑ i ∈ Finset.range (m*2 - 1 + 1), i by
        unfold m at this
        rw [pow_succ]
        exact this

      rw [Finset.sum_range_id]
      rw [show (m * 2 - 1 + 1) = m * 2 by
        rw [← Nat.sub_add_comm (by omega)]
        omega
      ]

      use (m * 2 - 1)
      have : m * 2 * (m * 2 - 1) = 2 * (m * (m * 2 - 1)) := by ring
      rw [this]
      omega

    . unfold lowerBounds
      simp
      intro m hm_pos h_dvd
      obtain ⟨k, hk⟩ := h_dvd
      replace hk : (∑ i ∈ Finset.range (m + 1), i) * 2 = 2 ^ (a+1) * k := by
        rw [hk]
        ring
      rw [Finset.sum_range_id_mul_two] at hk
      norm_num at hk
      have h_dvd: 2 ^ (a+1) ∣ (m + 1) * m := by use k

      have h1 : (m + 1).Coprime m := by simp [Nat.coprime_self_add_left]

      have h2 : IsPrimePow (2 ^ (a+1)) := by
        use 2, a+1
        exact ⟨prime_two, by omega, by rfl⟩

      rw [Nat.Coprime.isPrimePow_dvd_mul h1 h2] at h_dvd
      rcases h_dvd with h | h
      . apply Nat.le_of_dvd (show 0<m+1 by omega)
        exact h
      . suffices 2 ^ (a+1) ≤ m by omega
        apply Nat.le_of_dvd hm_pos
        exact h

  . intro a h_pos_a

    suffices IsLeast {m | 0 < m ∧ 3 ^ a ∣ ∑ i ∈ Finset.range (m+1), i} (3 ^ a - 1) from IsLeast.unique (hZ (3 ^ a)) this

    constructor
    . simp
      refine ⟨?_, ?_⟩
      . rw [show 1 = 3 ^ 0 by norm_num]
        apply Nat.pow_lt_pow_right
        all_goals omega
      . let m := 3^a
        have hm_odd : Odd m := by
          unfold m
          apply Odd.pow (show Odd 3 by decide)

        obtain ⟨k, hk⟩ := hm_odd
        suffices m ∣ ∑ i ∈ Finset.range (m - 1 + 1), i by unfold m at this; exact this
        rw [hk]
        rw [Finset.sum_range_id]
        norm_num
        rw [Nat.mul_div_assoc]
        . use (2 * k) / 2
        . use k

    . unfold lowerBounds
      simp
      intro m hm_pos h_dvd
      obtain ⟨k, hk⟩ := h_dvd
      replace hk : (∑ i ∈ Finset.range (m + 1), i) * 2 = 3 ^ a * (2 * k) := by
        rw [hk]
        ring
      rw [Finset.sum_range_id_mul_two] at hk
      norm_num at hk
      have h_dvd: 3 ^ a ∣ (m + 1) * m := by use 2 * k

      have h1 : (m + 1).Coprime m := by simp [Nat.coprime_self_add_left]

      have h2 : IsPrimePow (3 ^ a) := by
        use 3, a
        exact ⟨prime_three, h_pos_a, by rfl⟩

      rw [Nat.Coprime.isPrimePow_dvd_mul h1 h2] at h_dvd
      rcases h_dvd with h | h
      . apply Nat.le_of_dvd (show 0<m+1 by omega)
        exact h
      . suffices 3 ^ a ≤ m by omega
        apply Nat.le_of_dvd hm_pos
        exact h
