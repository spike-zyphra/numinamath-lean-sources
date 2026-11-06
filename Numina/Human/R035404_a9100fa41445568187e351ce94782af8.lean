import Mathlib

/-- Positive integers $a$, $b$, and $2009$, with $a < b < 2009$, form a geometric sequence with an
integer ratio. What is $a$?

$\mathrm{(A)}\ 7 \qquad \mathrm{(B)}\ 41 \qquad \mathrm{(C)}\ 49 \qquad \mathrm{(D)}\ 289 \qquad
\mathrm{(E)}\ 2009$ -/
theorem number_theory_97831 {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hb : b < 2009) (h : ∃ k : ℕ, b = a * k ∧ 2009 = b * k) :
    a = 41 := by

  -- Let $k$ be the ratio of the sequence $a$, $b$, and $2009$. So, we have $b = a k$ and $2009 = b k$.
  rcases h with ⟨k, hbak, hbk⟩

  -- $k$ cannot be $0$ because $b$ is positive.
  have : k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hbak
    omega

  -- $k$ cannot be $1$ because $a$ is less than $b$.
  have : k ≠ 1 := by
    intro h
    rw [hbak, h, mul_one] at hab
    omega

  -- From the equation, $2009 = b k$, $k$ is a divisor of $2009$.
  have hk : k ∣ 2009 := by use b; rw [hbk]; ring

  -- Combining the two equations, we have $2009 = a k^2$.
  have hak : 2009 = a * k^2 := by rw [hbk, hbak]; ring

  -- Notice that $2009 = 7^2 * 41$ where 7 and 41 are prime numbers.
  have : 2009 = 7^2 * 41 := by norm_num
  have : Nat.Prime 7 := by norm_num
  have : Nat.Prime 41 := by norm_num

  -- The number of 41's in the prime factorization of $2009$ is $1$.
  have : (7^2 * 41).factorization 41 = 1 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow,
        Nat.Prime.factorization ‹_›, Nat.Prime.factorization ‹_›]
    simp

  -- The number of 7's in the prime factorization of $2009$ is $2$.
  have : (7^2 * 41).factorization 7 = 2 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow,
        Nat.Prime.factorization ‹_›, Nat.Prime.factorization ‹_›]
    simp

  -- Wee have $7^2 \cdot 41 = a \cdot k^2$.
  replace hak : 7^2 * 41 = a * k^2 := by linarith

  -- First, let's show that 41 does not divide $k$.
  have h41k : ¬ 41 ∣ k := by
    -- For a contradiction, assume that $41$ divides $k$.
    intro h
    -- Then, the number of $41$'s in the prime factorization of $k$ is at least $1$.
    rw [Nat.Prime.dvd_iff_one_le_factorization ‹_› ‹_›] at h

    -- On the one hand, the number of $41$'s in the prime factorization of $2009$ is $1$.
    -- On the other hand, the number of $41$'s in the prime factorization of $a k^2$ is at least $2$
    -- by our assumption.
    have : (a * k^2).factorization 41 ≥ 2 := by
      calc _ = a.factorization 41 + (k^2).factorization 41 := by rw [Nat.factorization_mul (by omega) (by nlinarith)]; rfl
           _ ≥ (k^2).factorization 41 := by omega
           _ = 2 * k.factorization 41 := by rw [Nat.factorization_pow]; rfl
           _ ≥ _ := by omega
    -- This is a contradiction.
    rw [←hak] at this
    linarith

  -- We claim that 7 divides $k$.
  have : 7 ∣ k := by
    -- For a contradiction, assume that $7$ does not divide $k$.
    by_contra!

    -- This means that the number of $7$'s in the prime factorization of $k$ is $0$.
    have : k.factorization 7 = 0 := by
      rw [Nat.Prime.dvd_iff_one_le_factorization ‹_› ‹_›] at this
      omega

    -- Let's also show that 7^2 divides $a$.
    have : 7^2 ∣ a := by
      -- To that end, we can show that the number of $7$'s in the prime factorization of $a$ is 2.
      rw [Nat.Prime.pow_dvd_iff_le_factorization ‹_› (by omega)]
      apply le_of_eq

      -- This follows because the number of $7$'s in the prime factorization of $2009$ is $2$.
      -- and the number of $7$'s in the prime factorization of $k^2$ is $0$.
      calc _ = (7^2 * 41).factorization 7 := by omega
           _ = (a * k^2).factorization 7 := by rw [hak]
           _ = a.factorization 7 + (k^2).factorization 7 := by rw [Nat.factorization_mul (by omega) (by nlinarith)]; rfl
           _ = a.factorization 7 + 2 * k.factorization 7 := by rw [Nat.factorization_pow]; rfl
           _ = a.factorization 7 + 2 * 0 := by rw [‹k.factorization 7 = 0›]
           _ = _ := by ring

    -- Write $a = 7^2 m$ for some natural number $m$.
    rcases this with ⟨m, hm⟩

    -- Substituting $a = 7^2 m$ into the equation $2009 = a k^2$, we have $2009 = 7^2 m k^2$.
    rw [hm] at hak
    -- We can simplify this to $41 = m k^2$.
    have : 41 = m * k^2 := by linarith
    -- Therefore, $k$ divides $41$.
    have : k ∣ 41 := by
      calc _ ∣ k^2 := by exact Dvd.intro_left (k.pow 1) rfl
           _ ∣ m * k^2 := by exact Nat.dvd_mul_left (k ^ 2) m
           _ = _ := by rw [this]
    -- Because $41$ is a prime number, $k$ must be equal to $1$ or $41$.
    rw [Nat.dvd_prime ‹_›] at this
    -- However, both cases are impossible.
    rcases this with (rfl | rfl)
    · contradiction
    · contradiction

  -- Write $k = 7 k_0$ for some natural number $k_0$.
  rcases this with ⟨k0, hkk0⟩

  -- Substituting $k = 7 k_0$ into the equation $7^2 41 = a k^2$, we get $7^2 41 = a 7^2 k_0^2$.
  rw [hkk0] at hak
  -- We can simplify this to $41 = a k_0^2$.
  replace hak : 41 = a * k0^2 := by linarith

  -- Now, to conclude, we will show that $k_0 = 1$.
  suffices k0 = 1 by rwa [this, one_pow, mul_one, Eq.comm] at hak

  -- From the equation $41 = a k_0^2$, $k_0$ divides $41$.
  have : k0 ∣ 41 := by
    calc _ ∣ k0^2 := by exact Dvd.intro_left (k0.pow 1) rfl
         _ ∣ a * k0^2 := by exact Nat.dvd_mul_left (k0 ^ 2) a
         _ = _ := by rw [hak]
  -- Because $41$ is a prime number, $k_0$ must be equal to $1$ or $41$.
  rw [Nat.dvd_prime ‹_›] at this

  -- The first case is just what we want.
  rcases this with (hk0 | hk0)
  · exact hk0

  -- So, let's consider the second case and show that it is impossible.
  exfalso
  -- Substituting $k_0 = 41$ into the equation $41 = a k_0^2$, we get $41 = a 41^2$.
  rw [hk0] at hak
  -- This simplifies to $1 = 41 a$.
  replace hak : 1 = 41 * a := by linarith

  -- This is a contradiction because 41 does not divide $1$.
  omega