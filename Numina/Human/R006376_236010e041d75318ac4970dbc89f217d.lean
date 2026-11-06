import Mathlib

/-Let $K$ be an integer greater than or equal to 2.
An expression is formed by taking a base of 7, raising it to the power of 7,
then raising the result (the previous outcome) to the power of 7, and so on, until a total of $K$ sevens are used in the calculation.
This expression can be written as $(\dots((7^7)^7)\dots)^7$, where the number of sevens appearing in the expression is $K$.
This expression is mathematically equivalent to $7^{(7^{K-1})}$.
Find the last two digits of this expression.
Show that if $K$ is even, the last two digits are 43, and if $K$ is odd, the last two digits are 07.-/

theorem number_theory_636422 (K: ℕ) (h: 2 ≤ K): 7 ^ (7 ^ (K - 1)) % 100 = if Even K then 43 else 7 := by

  -- note that 7 ^ 4 % 100 = 1
  set a:= 7 ^ (K - 1)
  by_cases r: Even K

  -- case when K is even
  .
    simp [r]
    have s: 4 ∣ a + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod]
      suffices a % 4 = 3 by
        simp [this]
      simp [a]
      rw [even_iff_exists_two_mul] at r
      obtain ⟨s, hs⟩ := r
      set j:= s - 1
      replace hs: K = 2 * j + 2 := by
        omega
      simp [hs]
      ring_nf
      rw [Nat.mul_mod]
      suffices 7 ^ (j * 2) % 4 = 1 by
        simp [this]
      rw [show j * 2 = 2 * j by ring]
      rw [Nat.pow_mul]
      rw [Nat.pow_mod]
      simp

    apply exists_eq_mul_right_of_dvd at s
    obtain ⟨u, s⟩ := s
    set v:= u - 1
    replace s: a = 4 * v + 3 := by
      clear_value a
      omega
    clear_value a
    rw [s]
    ring_nf
    rw [Nat.mul_mod]
    suffices 7 ^ (v * 4) % 100 = 1 by
      simp [this]
    rw [show v * 4 = 4 * v by ring]
    rw [Nat.pow_mul]
    rw [Nat.pow_mod]
    simp

  -- case when K is odd
  .
    simp [r]
    have s: 4 ∣ a + 3 := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod]
      suffices a % 4 = 1 by
        simp [this]
      simp [a]
      simp at r
      apply Odd.exists_bit1 at r
      obtain ⟨s, hs⟩ := r
      simp [hs]
      rw [Nat.pow_mul]
      rw [Nat.pow_mod]
      simp
    apply exists_eq_mul_right_of_dvd at s
    obtain ⟨u, s⟩ := s
    set v:= u - 1
    replace s: a = 4 * v + 1 := by
      clear_value a
      omega
    clear_value a
    rw [s]
    ring_nf
    rw [Nat.mul_mod]
    suffices 7 ^ (v * 4) % 100 = 1 by
      simp [this]
    rw [show v * 4 = 4 * v by ring]
    rw [Nat.pow_mul]
    rw [Nat.pow_mod]
    simp
