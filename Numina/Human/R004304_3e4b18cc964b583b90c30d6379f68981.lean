import Mathlib

lemma multiplicity_pow (a p: ℤ) (k: ℕ) (h1: 0 < a) (h2: 0 < p) (h3: Prime p):
  multiplicity p (a ^ k) = ↑k * multiplicity p a := by
  have u: emultiplicity p (a ^ k) = ↑k * emultiplicity p a := by
    apply emultiplicity_pow
    tauto
  rw [FiniteMultiplicity.emultiplicity_eq_multiplicity] at u
  rw [FiniteMultiplicity.emultiplicity_eq_multiplicity] at u
  .
    set x:= multiplicity p (a ^ k)
    set y:= multiplicity p a
    clear_value x y
    clear *- u
    norm_cast at u
  .
    rw [Int.finiteMultiplicity_iff]
    zify
    rw [show |p| = p by apply abs_of_nonneg; linarith]
    refine ⟨?_, (by omega)⟩
    by_contra! o
    simp [o] at h3
  .
    rw [Int.finiteMultiplicity_iff]
    zify
    rw [show |p| = p by apply abs_of_nonneg; linarith]
    refine ⟨?_, (by apply pow_ne_zero; omega)⟩
    by_contra! o
    simp [o] at h3

/- Let x be the smallest positive integer that simultaneously satisfies the following conditions:
2x is the square of an integer,
3x is the cube of an integer, and
5x is the fifth power of an integer. Find the prime factorization of x.-/

theorem number_theory_250679: IsLeast
  {x: ℤ | 0 < x ∧ ∃ a b c: ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 2 * x = a ^ 2 ∧ 3 * x = b ^ 3 ∧ 5 * x = c ^ 5} (2 ^ 15 * 3 ^ 20 * 5 ^ 24) := by

  constructor

  -- the forward direction, show the number is in the set
  .
    rw [Set.mem_setOf]
    constructor
    .
      simp
    .
      use (2 ^ 8 * 3 ^ 10 * 5 ^ 12), (2 ^ 5 * 3 ^ 7 * 5 ^ 8), (2 ^ 3 * 3 ^ 4 * 5 ^ 5)
      norm_num


  -- the backward direction, show that the number is indeed the min
  .
    intro x h
    rw [Set.mem_setOf] at h
    rcases h with ⟨hx, h⟩
    obtain ⟨a, b, c, l1, l2, l3, h1, h2, h3⟩ := h
    suffices 2 ^ 15 * 3 ^ 20 * 5 ^ 24 ∣ x by
      apply exists_eq_mul_right_of_dvd at this
      obtain ⟨k, hk⟩ := this
      have lk: 0 < k := by
        omega
      rw [hk]
      omega
    suffices 2 ^ 15 ∣ x ∧ 3 ^ 20 ∣ x ∧ 5 ^ 24 ∣ x by
      rcases this with ⟨p, q, r⟩
      apply IsCoprime.mul_dvd
      .
        norm_num
      .
        apply IsCoprime.mul_dvd
        .
          norm_num
        .
          tauto
        .
          tauto
      .
        tauto
    refine ⟨?_, ?_, ?_⟩

    -- show 2 ^ 15 ∣ x
    .
      -- let p be the power of 2 in x
      set p:= multiplicity 2 x

      -- show that p ≠ 0
      have ip: 0 < p := by
        suffices p ≠ 0 by omega
        simp [p]
        rw [multiplicity_eq_zero]
        simp
        have i: 2 ∣ a ^ 2 := by
          rw [← h1]
          simp
        replace i: 2 ∣ a := by
          apply Prime.dvd_of_dvd_pow at i
          tauto
          norm_num
        replace i: 4 ∣ a ^ 2 := by
          rw [show (4: ℤ) = 2 ^ 2 by norm_num]
          rw [Int.pow_dvd_pow_iff]
          tauto
          norm_num
        rw [← h1] at i
        rw [show (4: ℤ) = 2 * 2 by norm_num] at i
        apply Int.dvd_of_mul_dvd_mul_left at i
        tauto
        norm_num
      have h: 2 ^ p ∣ x := by
        apply pow_multiplicity_dvd
      suffices 15 ≤ p by
        have u: 2 ^ 15 ∣ 2 ^ p := by
          apply Nat.pow_dvd_pow
          tauto
        zify at u
        apply dvd_trans u h
      -- show that 3 ∣ p
      have f2: 3 ∣ p := by
        replace h2: multiplicity 2 (3 * x) = multiplicity 2 (b ^ 3) := by rw [h2]
        rw [multiplicity_mul] at h2
        have u: multiplicity (2: ℤ) (3: ℤ) = 0 := by
          rw [multiplicity_eq_zero]
          norm_num
        simp [u] at h2
        have v:= multiplicity_pow b 2 3 (by omega) (by omega) (by norm_num)
        rw [v] at h2
        simp [p, h2]
        norm_num
        rw [Int.finiteMultiplicity_iff]
        norm_num
        omega
      -- show 5 ∣ p
      have f3: 5 ∣ p := by
        replace h3: multiplicity 2 (5 * x) = multiplicity 2 (c ^ 5) := by rw [h3]
        rw [multiplicity_mul] at h3
        have u: multiplicity (2: ℤ) (5: ℤ) = 0 := by
          rw [multiplicity_eq_zero]
          norm_num
        simp [u] at h3
        have v:= multiplicity_pow c 2 5 (by omega) (by omega) (by norm_num)
        rw [v] at h3
        simp [p, h3]
        norm_num
        rw [Int.finiteMultiplicity_iff]
        norm_num
        omega
      suffices 15 ∣  p by
        apply exists_eq_mul_right_of_dvd at this
        obtain ⟨k, hk⟩ := this
        have lk: 0 < k := by
          omega
        rw [hk]
        omega
      rw [show 15 = 3 * 5 by norm_num]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      norm_num
      tauto
      tauto

    -- show 3 ^ 20 ∣ x
    .
      -- let p be the power of 3 in x
      set p:= multiplicity 3 x

      -- show that p ≠ 0
      have ip: 0 < p := by
        suffices p ≠ 0 by omega
        simp [p]
        rw [multiplicity_eq_zero]
        simp
        have i: 3 ∣ b ^ 3 := by
          rw [← h2]
          simp
        replace i: 3 ∣ b := by
          apply Prime.dvd_of_dvd_pow at i
          tauto
          norm_num
        replace i: 27 ∣ b ^ 3 := by
          rw [show (27: ℤ) = 3 ^ 3 by norm_num]
          rw [Int.pow_dvd_pow_iff]
          tauto
          norm_num
        rw [← h2] at i
        rw [show (27: ℤ) = 3 * 9 by norm_num] at i
        apply Int.dvd_of_mul_dvd_mul_left at i
        have j: 3 ∣ 9 := by
          norm_num
        zify at j
        apply dvd_trans j i
        norm_num
      have h: 3 ^ p ∣ x := by
        apply pow_multiplicity_dvd
      suffices 20 ≤ p by
        have u: 3 ^ 20 ∣ 3 ^ p := by
          apply Nat.pow_dvd_pow
          tauto
        zify at u
        apply dvd_trans u h
      -- show that 2 ∣ p
      have f1: 2 ∣ p := by
        replace h1: multiplicity 3 (2 * x) = multiplicity 3 (a ^ 2) := by rw [h1]
        rw [multiplicity_mul] at h1
        have u: multiplicity (3: ℤ) (2: ℤ) = 0 := by
          rw [multiplicity_eq_zero]
          norm_num
        simp [u] at h1
        have v:= multiplicity_pow a 3 2 (by omega) (by omega) (by norm_num)
        rw [v] at h1
        simp [p, h1]
        norm_num
        rw [Int.finiteMultiplicity_iff]
        norm_num
        omega
      -- show 5 ∣ p
      have f3: 5 ∣ p := by
        replace h3: multiplicity 3 (5 * x) = multiplicity 3 (c ^ 5) := by rw [h3]
        rw [multiplicity_mul] at h3
        have u: multiplicity (3: ℤ) (5: ℤ) = 0 := by
          rw [multiplicity_eq_zero]
          norm_num
        simp [u] at h3
        have v:= multiplicity_pow c 3 5 (by omega) (by omega) (by norm_num)
        rw [v] at h3
        simp [p, h3]
        norm_num
        rw [Int.finiteMultiplicity_iff]
        norm_num
        omega
      -- show 3 ∣ p + 1
      have f2: 3 ∣ p + 1 := by
        replace h2: multiplicity 3 (3 * x) = multiplicity 3 (b ^ 3) := by rw [h2]
        rw [multiplicity_mul] at h2
        simp at h2
        have v:= multiplicity_pow b 3 3 (by omega) (by omega) (by norm_num)
        rw [v] at h2
        simp [p]
        rw [add_comm]
        rw [h2]
        simp
        norm_num
        rw [Int.finiteMultiplicity_iff]
        norm_num
        omega
      clear *- f1 f2 f3
      apply exists_eq_mul_right_of_dvd at f3
      obtain ⟨k, hk⟩ := f3
      have lk: 0 < k := by
          omega
      rw [hk]
      suffices 4 ≤ k by omega
      by_contra! o
      simp [hk] at f1 f2
      interval_cases k
      all_goals norm_num at f1 f2

    -- show 5 ^ 24 ∣ x
    .
      -- let p be the power of 5 in x
      set p:= multiplicity 5 x

      -- show that p ≠ 0
      have ip: 0 < p := by
        suffices p ≠ 0 by omega
        simp [p]
        rw [multiplicity_eq_zero]
        simp
        have i: 5 ∣ c ^ 5 := by
          rw [← h3]
          simp
        replace i: 5 ∣ c := by
          apply Prime.dvd_of_dvd_pow at i
          tauto
          norm_num
        replace i: 5 ^ 5 ∣ c ^ 5 := by
          rw [Int.pow_dvd_pow_iff]
          tauto
          norm_num
        rw [← h3] at i
        rw [show 5 ^ 5 = (5: ℤ) * 5 ^ 4 by norm_num] at i
        apply Int.dvd_of_mul_dvd_mul_left at i
        have j: 5 ∣ 5 ^ 4 := by
          norm_num
        zify at j
        apply dvd_trans j i
        norm_num
      have h: 5 ^ p ∣ x := by
        apply pow_multiplicity_dvd
      suffices 24 ≤ p by
        have u: 5 ^ 24 ∣ 5 ^ p := by
          apply Nat.pow_dvd_pow
          tauto
        zify at u
        apply dvd_trans u h
      -- show that 2 ∣ p
      have f1: 2 ∣ p := by
        replace h1: multiplicity 5 (2 * x) = multiplicity 5 (a ^ 2) := by rw [h1]
        rw [multiplicity_mul] at h1
        have u: multiplicity (5: ℤ) (2: ℤ) = 0 := by
          rw [multiplicity_eq_zero]
          norm_num
        simp [u] at h1
        have v:= multiplicity_pow a 5 2 (by omega) (by omega) (by norm_num)
        rw [v] at h1
        simp [p, h1]
        norm_num
        rw [Int.finiteMultiplicity_iff]
        norm_num
        omega
      -- show 3 ∣ p
      have f2: 3 ∣ p := by
        replace h2: multiplicity 5 (3 * x) = multiplicity 5 (b ^ 3) := by rw [h2]
        rw [multiplicity_mul] at h2
        have u: multiplicity (5: ℤ) (3: ℤ) = 0 := by
          rw [multiplicity_eq_zero]
          norm_num
        simp [u] at h2
        have v:= multiplicity_pow b 5 3 (by omega) (by omega) (by norm_num)
        rw [v] at h2
        simp [p, h2]
        norm_num
        rw [Int.finiteMultiplicity_iff]
        norm_num
        omega
      -- show 5 ∣ p + 1
      have f3: 5 ∣ p + 1 := by
        replace h3: multiplicity 5 (5 * x) = multiplicity 5 (c ^ 5) := by rw [h3]
        rw [multiplicity_mul] at h3
        simp at h3
        have v:= multiplicity_pow c 5 5 (by omega) (by omega) (by norm_num)
        rw [v] at h3
        simp [p]
        rw [add_comm]
        rw [h3]
        simp
        norm_num
        rw [Int.finiteMultiplicity_iff]
        norm_num
        omega
      clear *- f1 f2 f3
      apply exists_eq_mul_right_of_dvd at f3
      obtain ⟨k, hk⟩ := f3
      have lk: 0 < k := by
          omega
      replace hk: p = 5 * k - 1 := by omega
      simp [hk] at *
      suffices 4 ≤ k by omega
      by_contra! o
      interval_cases k
      all_goals norm_num at f1 f2