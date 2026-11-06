import Mathlib

/-b and p are natural numbers greater than 1, and
p+2b, p+4b, p+6b，p+8b, p+10b, p+12b are all prime numbers.
Find the minimum value of p+b.-/

theorem number_theory_631067: IsLeast {n: ℕ | ∃ b p, 1 < b ∧ 1 < p ∧ n = p + b ∧
  Nat.Prime (p + 2 * b) ∧ Nat.Prime (p + 4 * b) ∧ Nat.Prime (p + 6 * b)
  ∧ Nat.Prime (p + 8 * b) ∧ Nat.Prime (p + 10 * b) ∧ Nat.Prime (p + 12 * b)} 82 := by

  constructor

  -- the forward direction
  .
    simp
    use 75
    norm_num
    use 7
    norm_num

  -- the reverse direction
  .
    intro n h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨b, p, hb, hp, h1, h2, h3, h4, h5, h6, h7⟩ := h
    rw [h1]
    clear h1

    -- we show that p is not divided by 2 3 5
    have p1: ¬ 2 ∣ p := by
      by_contra! f
      have o: 2 ∣ p + 4 * b := by
        apply Nat.dvd_add
        exact f
        rw [show 4 * b = 2 * (2 * b) by omega]
        simp
      rw [Nat.prime_dvd_prime_iff_eq] at o
      omega
      norm_num
      exact h3

    -- we show that p is not divided by 3
    have p2: ¬ 3 ∣ p := by
      by_contra! f
      have o: 3 ∣ p + 6 * b := by
        apply Nat.dvd_add
        exact f
        rw [show 6 * b = 3 * (2 * b) by omega]
        simp
      rw [Nat.prime_dvd_prime_iff_eq] at o
      omega
      norm_num
      exact h4

    -- we show that p is not divided by 5
    have p3: ¬ 5 ∣ p := by
      by_contra! f
      have o: 5 ∣ p + 10 * b := by
        apply Nat.dvd_add
        exact f
        rw [show 10 * b = 5 * (2 * b) by omega]
        simp
      rw [Nat.prime_dvd_prime_iff_eq] at o
      omega
      norm_num
      exact h6

    -- hence we show that 7 ≤ p
    have l1: 7 ≤ p := by
      by_contra! g
      interval_cases p
      .
        simp at p1
      .
        simp at p2
      .
        simp at p1
      .
        simp at p3
      .
        have u: 3 ∣ 6 + 12 * b := by
          rw [show 6 + 12 * b = 3 * (2 * (1 + 2 * b)) by omega]
          simp
        rw [Nat.prime_dvd_prime_iff_eq] at u
        omega
        norm_num
        exact h7

    -- we show that 3 ∣ b
    have d1: 3 ∣ b := by
      by_contra! o
      replace o: b % 3 = 1 ∨ b % 3 = 2 := by omega
      replace p2: p % 3 = 1 ∨ p % 3 = 2 := by omega
      have y: (p + 2 * b) % 3 = 0 ∨ (p + 4 * b) % 3 = 0 := by
        rcases o with o | o
        .
          rcases p2 with p2 | p2
          .
            left
            simp [Nat.add_mod, Nat.mul_mod, o, p2]
          .
            right
            simp [Nat.add_mod, Nat.mul_mod, o, p2]
        .
          rcases p2 with p2 | p2
          .
            right
            simp [Nat.add_mod, Nat.mul_mod, o, p2]
          .
            left
            simp [Nat.add_mod, Nat.mul_mod, o, p2]
      rcases y with y | y
      .
        apply Nat.dvd_of_mod_eq_zero at y
        rw [Nat.prime_dvd_prime_iff_eq] at y
        omega
        norm_num
        exact h2
      .
        apply Nat.dvd_of_mod_eq_zero at y
        rw [Nat.prime_dvd_prime_iff_eq] at y
        omega
        norm_num
        exact h3

    -- similarly, we show that 5 ∣ b
    have d2: 5 ∣ b := by
      by_contra! o
      replace o: b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
      replace p3: p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
      have y: (p + 2 * b) % 5 = 0 ∨ (p + 4 * b) % 5 = 0 ∨ (p + 6 * b) % 5= 0 ∨ (p + 8 * b) % 5 = 0 := by
        rcases o with o | o | o | o <;> rcases p3 with p3 | p3 | p3 | p3 <;> simp [Nat.add_mod, Nat.mul_mod, o, p3]
      rcases y with y | y | y | y
      all_goals {
        apply Nat.dvd_of_mod_eq_zero at y
        rw [Nat.prime_dvd_prime_iff_eq] at y
        omega
        norm_num
        trivial
      }

    -- combine d1, d2, we get 15 ∣ b
    replace d1: 15 ∣ b := by
      rw [show 15 = 3 * 5 by omega]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      norm_num
      exact d1
      exact d2
    clear d2

    by_contra! l
    apply exists_eq_mul_right_of_dvd at d1
    obtain ⟨u, d⟩ := d1
    have lu: u ≤ 4 := by
      by_contra! v
      have s: u = 5 := by omega
      simp [s] at d
      simp [d] at l
      replace l: p < 7 := by omega
      omega
    have ru: 1 ≤ u := by
      by_contra! v
      replace v: u = 0 := by omega
      simp [v] at d
      simp [d] at hb
    simp [d] at *
    replace l: p < 82 - 15 * u := by
      omega

    -- use the bound above, we can check the rest cases at all
    interval_cases u
    all_goals {
      simp at l
      interval_cases p
      all_goals {
        try omega
        all_goals {
          simp at *
          all_goals {
            norm_num at *
            }
          }
        }
      }