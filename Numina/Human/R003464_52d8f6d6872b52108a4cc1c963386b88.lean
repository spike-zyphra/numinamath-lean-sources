import Mathlib

/-
Part (a): For any composite number in the arithmetic progression, there's a
larger composite number in the progression.'
-/
lemma part_a {a d : ℕ} (a_gt_1 : 1 < a) (pos_d : 0 < d) :
  ∀ n : ℕ, ∃ m > n, ¬Prime (a + m * d)
    := by
  intro n
  by_cases pos_n : n = 0
  · subst n
    use a
    constructor
    · positivity
    · rw [<- Nat.prime_iff]
      rw [Nat.not_prime_iff_exists_dvd_lt (by omega)]
      use a
      simp_all
      constructor
      · exact a_gt_1
      · positivity

  replace pos_n : 0 < n := by positivity

  by_cases coprime : Nat.Coprime a d
  · use n * a
    constructor
    · conv_rhs => rw [<- mul_one n]
      gcongr

    · have : 2 ≤ a + n * a * d := by
        omega
      rw [<- Nat.prime_iff, Nat.not_prime_iff_exists_dvd_lt this]
      use a
      constructor
      · simp [mul_comm n, mul_assoc]
      · constructor
        · exact a_gt_1
        · have : 0 < n*a*d := by
            positivity
          exact Nat.lt_add_of_pos_right this

  · use n + 1
    constructor
    · linarith
    · have : 2 ≤ a + (n + 1) * d := by
        omega
      rw [<- Nat.prime_iff, Nat.not_prime_iff_exists_dvd_lt this]
      rw [Nat.Prime.not_coprime_iff_dvd] at coprime
      obtain ⟨ c, prime_c, c_div_a, c_div_d ⟩ := coprime
      use c
      constructor
      · have: c ∣ (n+1)*d := by
          exact Nat.dvd_trans c_div_d (Nat.dvd_mul_left _ _)

        exact (Nat.dvd_add_iff_right c_div_a).mp this

      · constructor
        · exact Nat.Prime.two_le prime_c
        · obtain ⟨ k, k_eq ⟩ := c_div_a
          obtain ⟨ j, j_eq ⟩ := c_div_d
          rw [mul_comm, k_eq, j_eq, mul_assoc, <- mul_add c]
          conv_lhs => rw [<- mul_one c]
          gcongr
          · exact Nat.Prime.pos prime_c

          have a_ne_0 : a ≠ 0 := by
            exact Nat.not_eq_zero_of_lt a_gt_1
          have d_ne_0 : d ≠ 0 := by
            exact Nat.not_eq_zero_of_lt pos_d

          have pos_k : 0 < k := by
            suffices k ≠ 0 by exact Nat.zero_lt_of_ne_zero this
            by_contra! eq
            simp [eq] at k_eq
            exact a_ne_0 k_eq

          have : 0 < j := by
            suffices j ≠ 0 by exact Nat.zero_lt_of_ne_zero this
            by_contra! eq
            simp [eq] at j_eq
            exact d_ne_0 j_eq

          have pos_n1 : 0 < n + 1 := by
            exact Nat.add_pos_left pos_n 1

          suffices 0 < j * (n + 1) by
            omega

          exact Nat.mul_pos this pos_n1

/-
Part (b): For any square in the arithmetic progression, there's a larger
square in the progression, or there are no squares in the progression.
-/
lemma part_b {a d : ℕ} :
  (∀ n' > 0, ∃ (j l : ℕ), n' < j ∧ a + j * d = l^2) ∨
  (∀ (n : ℕ), ¬∃ (k : ℕ), a + n * d = k ^ 2) := by
  by_cases h : ∃ (n m : ℕ), a + n * d = m ^ 2
  · left
    rcases h with ⟨n, m, hk⟩
    intro n' pos_n
    by_cases pos_d : d = 0
    · subst d
      use n' + 1, m
      omega
    replace pos_d : 0 < d := by positivity

    by_cases pos_m : m = 0
    · subst m
      use n + 4*d*n'^2, 2*n' * d
      constructor
      · rw [mul_comm 4]
        suffices n' < d * (4 * n' ^ 2) by
          linarith
        suffices n' < 4 * n' ^ 2 by
          exact lt_mul_of_one_le_of_lt pos_d this
        rw [show 4 = 2 * 2 by rfl]
        rw [two_mul]
        conv_lhs => rw [<- one_mul n']
        rw [sq, <- mul_assoc]
        gcongr
        omega
      · replace hk : a + n * d = 0 := hk
        ring_nf
        simp [hk]


    use 2 * m * n' + n + d*n'^2, m + n' * d
    constructor
    · simp at pos_n
      suffices n' < 2 * m * n' by omega
      rw [two_mul]
      conv_lhs => rw [<- one_mul n']
      gcongr
      omega
    · ring_nf
      rw [<- hk]
      ring

  · right
    intro n k
    exact h ⟨n, k⟩

theorem number_theory_185044 {a d : ℕ} : (
    1 < a → 0 < d → ∀ n : ℕ, ∃ m > n, ¬Prime (a + m * d)
  ) ∧ (
    (∀ n' > 0, ∃ (j l : ℕ), n' < j ∧ a + j * d = l^2) ∨
    (∀ (n : ℕ), ¬∃ (k : ℕ), a + n * d = k ^ 2)
  ) := ⟨ part_a, part_b ⟩
