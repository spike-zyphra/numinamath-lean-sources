import Mathlib

/-Let $S_0$ be an integer. Let $a, b, c, d$ be natural numbers representing digits, so $0 \le a, b, c, d \le 9$.
Suppose $a \ne 0$ and the sum of these digits is $a+b+c+d = S_0$. (This implies $1 \le S_0 \le 36$, as $a \ne 0$
means the minimum sum is $1+0+0+0=1$ and the maximum sum is $9+9+9+9=36$.)
Let $N$ be the four-digit number $1000a + 100b + 10c + d$, and let $N_{rev}$ be its reverse $1000d + 100c + 10b + a$.
Show that the sum $N + N_{rev}$ is divisible by $11 \cdot \gcd(81, 10 S_0)$.-/

theorem number_theory_634905 (S0 N Nrev a b c d: ℕ) (l: 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9)
    (h1: S0 = a + b + c + d) (h2: N = 1000 * a + 100 * b + 10 * c + d)
    (h3: Nrev = 1000 * d + 100 * c + 10 * b + a): (11 * Nat.gcd 81 (10 * S0)) ∣ (N + Nrev) := by

    have e: N + Nrev = 110 * S0 + 891 * (a + d) := by
      simp [h1, h2, h3]
      ring

    clear h2
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    .
      suffices Nat.Coprime 11 81 ∧ Nat.gcd 81 (10 * S0) ∣ 81 by
        apply Nat.Coprime.of_dvd_right this.2 this.1
      constructor
      .
        norm_num
      .
        apply Nat.gcd_dvd_left
    .
      rw [e]
      rw [show 110 * S0 + 891 * (a + d) = 11 * (10 * S0 + 81 * (a + d)) by ring]
      simp
    .
      have i: Nat.gcd 81 (10 * S0) = Nat.gcd 81 S0 := by
        apply Nat.Coprime.gcd_mul_left_cancel_right
        norm_num
      rw [i]
      clear i
      rw [e]
      clear e h3
      by_cases r: 3 ∣ S0

      -- case 3 ∣ S0
      .
        apply exists_eq_mul_right_of_dvd at r
        obtain ⟨k, rfl⟩ := r
        have l1: k ≤ 12 := by omega
        apply Nat.dvd_add
        .
          suffices Nat.gcd 81 (3 * k) ∣ 3 * k by
            have u: 3 * k ∣ 110 * (3 * k) := by simp
            apply dvd_trans this u
          apply Nat.gcd_dvd_right
        .
          suffices Nat.gcd 81 (3 * k) ∣ 81 by
            have u: 81 ∣ 891 * (a + d) := by
              rw [show 891 * (a + d) = 81 * (11 * (a + d)) by ring]
              simp
            apply dvd_trans this u
          apply Nat.gcd_dvd_left

      -- case 3 ∤ S0
      .
        suffices Nat.gcd 81 S0 = 1 by
          rw [this]
          simp
        apply Nat.Coprime.gcd_eq_one
        rw [show 81 = 3 ^ 4 by norm_num]
        apply Nat.Coprime.pow_left
        rw [Nat.Prime.coprime_iff_not_dvd]
        tauto
        norm_num