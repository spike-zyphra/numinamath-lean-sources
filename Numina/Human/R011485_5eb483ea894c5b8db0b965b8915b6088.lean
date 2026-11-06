import Mathlib

/- x y and z are prime numbers and satisfy x ^ y + 1 = z
Find the value of x + y + z -/

theorem number_theory_628800 {x y z: ℕ} (px: Nat.Prime x) (py: Nat.Prime y) (pz: Nat.Prime z)
  (h: x ^ y + 1 = z): x + y + z = 9 := by

  -- we first show that x = 2 by mod 2
  have hx: x = 2 := by
    by_contra! o
    have ox: Odd x := by
      apply Nat.Prime.odd_of_ne_two
      exact px
      exact o
    -- then z is even
    have ez: Even z := by
      rw [← h]
      rw [Nat.even_add_one]
      simp
      apply Odd.pow
      exact ox
    -- then z = 2
    have vz: z = 2 := by
      by_contra! t
      have c: Odd z := by
        apply Nat.Prime.odd_of_ne_two
        exact pz
        exact t
      absurd c
      simp [ez]
    simp [vz] at h
    rw [pow_eq_one_iff_of_nonneg] at h
    .
      rw [h] at px
      norm_num at px
    .
      omega
    .
      by_contra! o
      simp [o] at py
      norm_num at py
      
  -- then we must have y = 2 by mod 3
  have hy: y = 2 := by
    by_contra! o
    have oy: Odd y := by
      apply Nat.Prime.odd_of_ne_two
      exact py
      exact o
    simp [hx] at *
    clear px hx o
    have s: z % 3 = 0 := by
      rw [← h]
      rw [Nat.add_mod]
      rw [show 1 % 3 = 1 by rfl]
      apply Odd.exists_bit1 at oy
      obtain ⟨k, hk⟩ := oy
      simp only [hk]
      rw [show 2 ^ (2 * k + 1) = 2 ^ (2 * k) * 2 by rfl]
      rw [show 2 ^ (2 * k) = 4 ^ k by apply Nat.pow_mul]
      rw [Nat.mul_mod]
      rw [show 2 % 3 = 2 by rfl]
      rw [Nat.pow_mod]
      rw [show 4 % 3 = 1 by rfl]
      rw [show 1 ^ k = 1 by simp]
    apply Nat.dvd_of_mod_eq_zero at s
    -- then we must have z = 3
    rw [Nat.prime_dvd_prime_iff_eq] at s
    simp [← s] at h
    rw [Nat.pow_eq_self_iff] at h
    rw [h] at py
    norm_num at py
    norm_num
    norm_num
    exact pz

  -- finally we show that z = 5
  have hz: z = 5 := by
    simp [hx, hy] at h
    omega

  -- compute the sum
  simp [hx, hy, hz]