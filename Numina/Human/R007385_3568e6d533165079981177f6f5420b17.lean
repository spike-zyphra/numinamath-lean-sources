import Mathlib

open Nat Set

/- For a given positive integer $n$, we define $\varphi(n)$ to be the number of positive integers less than or equal to $n$ which share no common prime factors with $n$. Find all positive integers $n$ for which

$$
\varphi(2019 n)=\varphi\left(n^{2}\right)
$$ -/
theorem number_theory_610084:
  ∀ n > 0, φ (2019 * n) = φ (n ^ 2) → n = 1346 ∨ n = 2016 ∨ n = 2019 := by
  intro n hn
  intro h

  let a := (2019).gcd n

  -- we have 673 is a prime number
  have prime_673 : Nat.Prime 673 := by
    norm_num

  -- we have gcd 2019 n ∈ {1, 3, 673, 2019}
  have h1: a = 1 ∨ a = 3 ∨ a=673 ∨ a = 2019 := by
    -- gcd 2019 n | 2019
    have h1_1: a ∣ 2019 := by apply Nat.gcd_dvd_left

    -- 2019 = 3 * 673 where 3 and 673 are prime numbers
    have h1_2 : 2019 = 3 * 673 := by norm_num
    rw [h1_2] at h1_1

    -- so a = y * z where y | 3 and z | 673
    rw [dvd_mul] at h1_1
    let ⟨y, z, hy, hz, hyz⟩ := h1_1
    rw [Nat.dvd_prime Nat.prime_three] at hy
    rw [Nat.dvd_prime prime_673] at hz
    rcases hy with hy | hy
    . rcases hz with hz | hz
      simp [hy, hz] at hyz; simp [hyz]
      simp [hy, hz] at hyz; simp [hyz]
    . rcases hz with hz | hz
      simp [hy, hz] at hyz; simp [hyz]
      simp [hy, hz] at hyz; simp [hyz]

  -- sure a > 0
  have ha: a > 0 := by
    simp [a, Nat.gcd_pos_of_pos_left]

  -- for any a, b, we have φ (a * b) = φ a * φ b * a.gcd b / φ (a.gcd b)
  have h2:  ∀a b, a.gcd b > 0 -> φ (a * b) = φ a * φ b * a.gcd b / φ (a.gcd b) := by
    intro a b hb
    rw [← totient_gcd_mul_totient_mul a b]
    field_simp [hb]
  -- rewrite h with φ (2019 * n) = φ 2019 * φ n * Nat.gcd 2019 n / φ (Nat.gcd 2019 n) = φ
  rw [h2 2019 n ha] at h

  -- we have φ n > 0 from n > 0
  have hnp: φ n ≠ 0 := by
     simp [totient_pos] ; positivity

  -- we have φ (n^2) = φ n * n
  have h3: φ (n^2) = φ n * n := by
    rw [sq]
    have h3_1: φ (n.gcd n) * φ (n*n) = φ n * φ n * (n.gcd n) := by
      rw [totient_gcd_mul_totient_mul]
    simp at h3_1
    rw [mul_assoc, Nat.mul_right_inj hnp] at h3_1
    exact h3_1
  rw [h3] at h

  -- compute some totient values for constants
  have hp3: φ 3 = 2 := by simp[Nat.totient_prime, Nat.prime_three]
  have hp673: φ 673 = 672 := by simp[Nat.totient_prime, prime_673]
  have hp2019: φ 2019 = 1344 := by
    have h4_1: 2019 = 3 * 673 := by norm_num
    have h4_2: Coprime 3 673 := by norm_num
    rw [h4_1, totient_mul]
    simp [hp3, hp673]
    exact h4_2

  simp [a] at h1
  -- we will examine the equality in four cases
  rcases h1 with (h1 | h1 | h1 | h1)
  . -- gcd 2019 n = 1, we have φ 2019 * φ n = φ n * n
    simp [h1] at h
    -- so n = φ 2019 = 1344
    nth_rewrite 2 [mul_comm] at h; rw [Nat.mul_left_inj hnp, hp2019] at h
    -- but we get gcd 2019 1344 = 3 ≠ 1
    have hna: a = 3 := by
      simp [a, ← h]
    -- so there is no answer in this case
    simp [h1, a] at hna
  . -- gcd 2019 n = 3, we can show that n = 2016 in this case
    have : 2016 = n := by
      -- φ 2019 * n * 3 / 2 = φ n * n
      field_simp [a, h1, hp3, hp2019] at h
      -- φ n * 2016 = φ n * n
      rw [← Nat.mul_right_comm] at h ; norm_num at h; rw [mul_comm 4032, Nat.mul_div_assoc] at h
      apply Nat.mul_left_cancel (by positivity) h
      -- n = 2016
      norm_num
    simp [this]
  . -- gcd 2019 n = 673, we can show that n = 1346 in this case
    have : 1346 = n := by
      -- φ 2019 * n * 673 / 672 = φ n * n
      field_simp [a, h1, hp673, hp2019] at h
      -- φ n * (2713536 / 672) = φ n * n
      rw [← Nat.mul_right_comm] at h ; norm_num at h ; rw [mul_comm 904512, Nat.mul_div_assoc] at h
      apply Nat.mul_left_cancel (by positivity) h
      -- n = 1346
      norm_num
    simp [this]
  . -- gcd 2019 n = 2019, we can show that n = 2019 in this case
    have : 2019 = n := by
      -- φ 2019 * φ n * 2019 / φ 2019 = φ n * n
      field_simp [a, h1, hp2019] at h
      -- so φ n * 2019 = φ n * n
      rw [← Nat.mul_right_comm] at h ; norm_num at h; rw [mul_comm 2713536, Nat.mul_div_assoc] at h
      apply Nat.mul_left_cancel (by positivity) h
      -- thus n = 2019
      norm_num
    simp [this]
