import Mathlib

lemma one_lt_prime_pow_gcd_dvd {p a n : ℕ} (hp : p.Prime) (hpa : 1 < (p ^ n).gcd a) : p ∣ a := by
  have : (p ^ n).gcd a ∣ p ^ n := by apply Nat.gcd_dvd_left
  rw [Nat.dvd_prime_pow hp] at this
  obtain ⟨k, hk1, hk2⟩ := this
  have : (p ^ n).gcd a ∣ a := by apply Nat.gcd_dvd_right
  rw [hk2] at this
  have := Nat.pow_dvd_of_le_of_pow_dvd (show 1 ≤ k by
    rw [hk2] at hpa
    by_contra h
    simp at h
    rw [h] at hpa
    simp at hpa
  ) this
  simp at this
  exact this


theorem number_theory_608577 :
  IsLeast {x | ∃ a : Fin 5 → ℕ, (∀ i, a i > 0)
    ∧ (∀ i j, i ≠ j → Nat.gcd (a i) (a j) > 1)
    ∧ a 0 ≤ a 1 ∧ a 1 ≤ a 2 ∧ a 2 ≤ a 3 ∧ a 3 ≤ a 4
    ∧ Nat.gcd (Nat.gcd (Nat.gcd (Nat.gcd (a 0) (a 1)) (a 2)) (a 3)) (a 4) = 1 ∧ x = ∏ i, a i} 32400 := by


  constructor
  . simp
    use ![6, 6, 6, 10, 15]
    decide
  . simp [lowerBounds]
    intro n a ha1 ha2 ha01 ha12 ha23 ha34 ha3 hn
    rw [hn]


    have h_a_i_ne_prime_pow : ∀ (i : Fin 5), ∀ p m, Nat.Prime p → a i ≠ p ^ m := by
      intro i p m hp
      by_contra heq
      by_cases hm : m = 0
      . rw [hm] at heq
        simp at heq
        by_cases hi : i = 0
        . have := ha2 0 1 (by simp)
          rw [hi] at heq
          rw [heq] at this
          simp at this
        . have := ha2 i 0 hi
          rw [heq] at this
          simp at this
      . have : ∀ (j : Fin 5), p ∣ a j := by
          intro j
          by_cases hij : i = j
          . rw [← hij]
            rw [heq]
            nth_rw 1 [show p = p ^ 1 by norm_num]
            apply Nat.pow_dvd_pow
            omega
          . have := ha2 i j hij
            rw [heq] at this
            exact one_lt_prime_pow_gcd_dvd hp this

        obtain ⟨k0, hk0⟩ := this 0
        obtain ⟨k1, hk1⟩ := this 1
        obtain ⟨k2, hk2⟩ := this 2
        obtain ⟨k3, hk3⟩ := this 3
        obtain ⟨k4, hk4⟩ := this 4

        rw [hk0, hk1, hk2, hk3, hk4] at ha3
        simp [Nat.gcd_mul_left] at ha3
        rw [ha3.1] at hp
        norm_num at hp


    have : a 0 ≠ 0 := by
      have := ha1 0
      omega

    have : a 0 ≠ 1 := by
      have := h_a_i_ne_prime_pow 0 2 0 Nat.prime_two
      simp at this
      exact this

    have : a 0 ≠ 2 := by
      have := h_a_i_ne_prime_pow 0 2 1 Nat.prime_two
      simp at this
      exact this

    have : a 0 ≠ 3 := by
      have := h_a_i_ne_prime_pow 0 3 1 Nat.prime_three
      simp at this
      exact this

    have : a 0 ≠ 4 := by
      have := h_a_i_ne_prime_pow 0 2 2 Nat.prime_two
      simp at this
      exact this

    have : a 0 ≠ 5 := by
      have := h_a_i_ne_prime_pow 0 5 1 Nat.prime_five
      simp at this
      exact this

    have : a 0 ≠ 7 := by
      have := h_a_i_ne_prime_pow 0 7 1 (by decide)
      simp at this
      exact this

    have : a 0 ≠ 9 := by
      have := h_a_i_ne_prime_pow 0 3 2 (by decide)
      simp at this
      exact this

    have : a 0 ≠ 11 := by
      have := h_a_i_ne_prime_pow 0 11 1 (by decide)
      simp at this
      exact this

    have : a 0 ≠ 13 := by
      have := h_a_i_ne_prime_pow 0 13 1 (by decide)
      simp at this
      exact this

    have : 6 ≤ a 0 := by omega
    have : 6 ≤ a 1 := by omega
    have : 6 ≤ a 2 := by omega

    have : a 1 ≠ 7 := by
      have := h_a_i_ne_prime_pow 1 7 1 (by decide)
      simp at this
      exact this

    have : a 1 ≠ 9 := by
      have := h_a_i_ne_prime_pow 1 3 2 (by decide)
      simp at this
      exact this

    have : a 1 ≠ 11 := by
      have := h_a_i_ne_prime_pow 1 11 1 (by decide)
      simp at this
      exact this

    have : a 1 ≠ 13 := by
      have := h_a_i_ne_prime_pow 1 13 1 (by decide)
      simp at this
      exact this

    have : a 2 ≠ 7 := by
      have := h_a_i_ne_prime_pow 2 7 1 (by decide)
      simp at this
      exact this

    have : a 2 ≠ 9 := by
      have := h_a_i_ne_prime_pow 2 3 2 (by decide)
      simp at this
      exact this

    have : a 2 ≠ 11 := by
      have := h_a_i_ne_prime_pow 2 11 1 (by decide)
      simp at this
      exact this

    have : a 2 ≠ 13 := by
      have := h_a_i_ne_prime_pow 2 13 1 (by decide)
      simp at this
      exact this

    have : a 3 ≠ 6 := by
      by_contra ha3_eq_6
      rw [ha3_eq_6] at ha3
      have : a 0 = 6 := by omega
      rw [this] at ha3
      have : a 1 = 6 := by omega
      rw [this] at ha3
      have : a 2 = 6 := by omega
      rw [this] at ha3
      simp at ha3

      have := ha2 3 4 (by simp)
      rw [ha3_eq_6] at this
      rw [ha3] at this
      simp at this

    have : a 3 ≠ 7 := by
      have := h_a_i_ne_prime_pow 3 7 1 (by decide)
      simp at this
      exact this

    have : a 3 ≠ 8 := by
      have := h_a_i_ne_prime_pow 3 2 3 (by decide)
      simp at this
      exact this

    have : a 3 ≠ 9 := by
      have := h_a_i_ne_prime_pow 3 3 2 (by decide)
      simp at this
      exact this

    have : a 3 ≠ 11 := by
      have := h_a_i_ne_prime_pow 3 11 1 (by decide)
      simp at this
      exact this

    have : a 3 ≠ 13 := by
      have := h_a_i_ne_prime_pow 3 13 1 (by decide)
      simp at this
      exact this

    have : 10 ≤ a 3 := by omega

    have : a 4 ≠ 10 ∧ a 4 ≠ 12 ∧ a 4 ≠ 14 := by
      by_contra
      have : a 4 = 10 ∨ a 4 = 12 ∨ a 4 = 14 := by
        omega

      have ⟨k4, hk4⟩: 2 ∣ a 4 := by omega

      have ⟨k3, hk3⟩ : 2 ∣ a 3 := by
        have : a 3 ≤ 14 := by omega
        interval_cases a 3
        all_goals omega

      have ⟨k2, hk2⟩ : 2 ∣ a 2 := by
        have : a 2 ≤ 14 := by omega
        interval_cases a 2
        all_goals omega

      have ⟨k1, hk1⟩ : 2 ∣ a 1 := by
        have : a 1 ≤ 14 := by omega
        interval_cases a 1
        all_goals omega


      have ⟨k0, hk0⟩ : 2 ∣ a 0 := by
        have : a 0 ≤ 14 := by omega
        interval_cases a 0
        all_goals omega


      rw [hk0, hk1, hk2, hk3, hk4] at ha3
      simp [Nat.gcd_mul_left] at ha3

    have : a 4 ≠ 11 := by
      have := h_a_i_ne_prime_pow 4 11 1 (by decide)
      simp at this
      exact this

    have : a 4 ≠ 13 := by
      have := h_a_i_ne_prime_pow 4 13 1 (by decide)
      simp at this
      exact this

    have : 15 ≤ a 4 := by omega

    rw [Finset.prod_fin_eq_prod_range]
    simp [Finset.prod_range_succ]
    have : 6 * 6 ≤ a 0 * a 1 := by nlinarith
    have : 6 * 6 * 6 ≤ a 0 * a 1 * a 2 := by nlinarith
    have : 6 * 6 * 6 * 10 ≤ a 0 * a 1 * a 2 * a 3 := by nlinarith
    nlinarith
