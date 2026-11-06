import Mathlib

/- Find all positive integer solutions $(x, y)$ to the equation $x! + y! = x^y$. -/

theorem number_theory_305682: {(x, y): ℕ × ℕ | 0 < x ∧ 0 < y ∧
Nat.factorial x + Nat.factorial y = x ^ y} = {(2, 2), (2, 3)} := by

  ext ⟨x, y⟩
  constructor

  -- the forward direction
  .
    simp only [Set.mem_setOf_eq]
    intro h
    rcases h with ⟨hx, hy, h⟩
    simp
    replace hx: 2 ≤ x := by
      by_contra! o
      replace o: x = 1 := by omega
      simp [o] at h
      have i:= Nat.factorial_ne_zero y
      tauto
    by_cases l: y = x

    -- case: y = x
    .
      simp [l] at h
      have lx: x < 3 := by  -- we show that x ≤ 2 by inequality
        by_contra! lx
        have hn: ∀ n: ℕ, 2 * Nat.factorial (n + 3) < (n + 3) ^ (n + 3) := by
          intro n
          induction' n with n ih
          .
            simp
            decide
          .
            rw [Nat.factorial_succ]
            rw [show 2 * ((n + 3 + 1) * (n + 3).factorial) = (n + 3 + 1) * (2 *  (n + 3).factorial) by ring]
            have i: (n + 3 + 1) * (n + 3) ^ (n + 3) ≤ (n + 1 + 3) ^ (n + 1 + 3) := by
              rw [show (n + 1 + 3) ^ (n + 1 + 3) = (n + 3 + 1) * (n + 1 + 3) ^ (n + 3) by ring]
              have s: (n + 3) ^ (n + 3) ≤ (n + 1 + 3) ^ (n + 3) := by
                apply Nat.pow_le_pow_of_le_left
                omega
              nlinarith
            nlinarith
        specialize hn (x - 3)
        rw [show x - 3 + 3  = x by omega] at hn
        linarith
      have o: x = 2 := by omega
      left
      omega

    .
      by_cases r: y < x

      -- case: y < x
      .
        clear l
        have d: y.factorial ∣x.factorial := by
          apply Nat.factorial_dvd_factorial
          linarith
        have eq: x.factorial = y.factorial * (x.factorial / y.factorial) := by
          symm
          rw [Nat.mul_div_eq_iff_dvd]
          exact d
        rw [eq] at h
        replace h: y.factorial * (1 + x.factorial / y.factorial) = x ^ y := by linarith
        have f: 1 + x.factorial / y.factorial ∣ x ^ y := by  -- this is where we derive the contradiction
          rw [← h]
          simp
        have g: (1 + x.factorial / y.factorial).Coprime (x ^ y) := by  -- then we show they are coprime
          apply Nat.Coprime.pow_right
          apply Nat.Coprime.symm
          have i: x ∣ x.factorial / y.factorial := by
            have s: x.factorial = x * (x - 1).factorial := by
              rw [show x = x - 1 + 1 by omega]
              rw [Nat.factorial_succ]
              norm_num
            rw [s]
            have j: y.factorial ∣ (x - 1).factorial := by
              apply Nat.factorial_dvd_factorial
              omega
            have eq: x * (x - 1).factorial / y.factorial = x * ((x - 1).factorial / y.factorial) := by
              set a:= (x - 1).factorial
              set b:= y.factorial
              zify at j
              zify
              qify
              rw [Rat.intCast_div]
              rw [Rat.intCast_div]
              field_simp
              exact j
              norm_cast
              norm_cast at j
              have e: a ∣ x * a := by simp
              apply dvd_trans j e
            rw [eq]
            simp
          apply exists_eq_mul_right_of_dvd at i
          obtain ⟨k, hk⟩ := i
          rw [hk]
          clear * - hx
          have o: (x * k).Coprime (1 + x * k) := by
            apply Nat.Coprime.symm
            rw [← Nat.coprime_self_sub_right]
            rw [show 1 + x * k - x * k = 1 by omega]
            apply Nat.coprime_one_right
            omega
          apply Nat.Coprime.coprime_mul_right at o
          exact o

        have s:= Nat.Coprime.eq_one_of_dvd g f
        replace s: x.factorial / y.factorial = 0 := by omega  -- this is easy to see wrong
        simp at s
        rcases s with s | s
        .
            have t:= Nat.factorial_ne_zero y
            tauto
        .
            rw [Nat.factorial_lt] at s
            omega
            omega

      -- case: y > x
      .
        have h':= h
        replace l: x < y := by omega
        clear r
        have d: x.factorial ∣y.factorial := by
          apply Nat.factorial_dvd_factorial
          linarith
        have eq: y.factorial = x.factorial * (y.factorial / x.factorial) := by  -- similar as above
          symm
          rw [Nat.mul_div_eq_iff_dvd]
          exact d
        rw [eq] at h
        replace h: x.factorial * (1 + y.factorial / x.factorial) = x ^ y := by linarith
        have s1: x.factorial = x * (x - 1).factorial := by
          rw [show x = x - 1 + 1 by omega]
          rw [Nat.factorial_succ]
          norm_num
        have s2: x ^ y = x * (x ^ (y - 1)) := by
          nth_rewrite 1 [show y = y - 1 + 1 by omega]
          ring
        rw [s1, s2] at h
        clear s1 s2
        replace h: (x - 1).factorial * (1 + y.factorial / (x * (x - 1).factorial)) = x ^ (y - 1) := by nlinarith
        have f: x - 1 ∣ x ^ (y - 1) := by   -- this is where we derive the value of x
          have s: x - 1 ∣ (x - 1).factorial := by
            apply Nat.dvd_factorial
            omega
            omega
          have t: (x - 1).factorial ∣ x ^ (y - 1) := by
            rw [← h]
            simp
          apply dvd_trans s t

        have g: (x - 1).Coprime (x ^ (y - 1)) := by
          apply Nat.Coprime.pow_right
          clear * - hx
          rw [← Nat.coprime_self_sub_left]
          rw [show x - (x - 1) = 1 by omega]
          apply Nat.coprime_one_left
          omega

        have s:= Nat.Coprime.eq_one_of_dvd g f
        replace s: x = 2 := by omega
        simp [s] at h'
        have ly: y < 4 := by -- then we show that y ≤ 3 by mod4
          by_contra! ly
          have m: (2 + y.factorial) % 4 = 2 ^ y % 4 := by
            rw [h']
          have m1: (2 + y.factorial) % 4 = 2 := by
            rw [Nat.add_mod]
            have r: y.factorial % 4 = 0 := by
              apply Nat.mod_eq_zero_of_dvd
              apply Nat.dvd_factorial
              norm_num
              exact ly
            simp [r]
          have m2: 2 ^ y % 4 = 0 := by
            apply Nat.mod_eq_zero_of_dvd
            rw [show 4 = 2 ^ 2 by norm_num]
            rw [Nat.pow_dvd_pow_iff_le_right]
            omega
            omega
          simp [m1, m2] at m
        replace ly: y = 3 := by omega  -- hence y = 3
        right
        omega


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h
    .
      simp [h]
    .
      simp [h]
      decide