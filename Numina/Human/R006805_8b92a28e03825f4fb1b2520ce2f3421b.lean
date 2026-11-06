import Mathlib
/- Let $p$ be a prime number such that $p \le 9$.
Theorem: A natural number $n$ is a four-digit number (meaning $1000 \le n \le 9999$) and the product of its base-10 digits is $p$ if and only if $n$ is one of the numbers:
$1000p + 111$,
$1000 + 100p + 11$,
$1100 + 10p + 1$, or
$1110 + p$. -/
theorem number_theory_641334 (p a b c d : ℕ) (hp : Nat.Prime p) (h1 : p ≤ 9) (ha1 : 1 ≤ a) (ha2 : a ≤ 9) (hb : b ≤ 9) (hc : c ≤ 9) (hd : d ≤ 9) (h2 : a * b * c * d = p) : 1000 * a + 100 * b + 10 * c + d = 1000 * p + 111 ∨ 1000 * a + 100 * b + 10 * c + d = 1000 + 100 * p + 11 ∨ 1000 * a + 100 * b + 10 * c + d = 1100 + 10 * p + 1 ∨ 1000 * a + 100 * b + 10 * c + d = 1110 + p:= by
  -- Since p is prime, it's greater than 1
  have h : p > 1:= by exact Nat.Prime.one_lt hp
  -- Since the product of digits equals p, p divides their product
  have h3 : p ∣ a * b * c * d:= by rw [h2]
  -- By prime property, p must divide either (abc) or d
  replace h3 : p ∣ a * b * c ∨ p ∣ d:= by exact (Nat.Prime.dvd_mul hp).mp h3
  rcases h3 with h3 | h3
  .
    -- If p divides abc, then p divides either (ab) or c
    replace h3 : p ∣ a * b ∨ p ∣ c:= by exact (Nat.Prime.dvd_mul hp).mp h3
    .
      rcases h3 with h3 | h3
      .
        -- If p divides ab, then p divides either a or b
        replace h3 : p ∣ a ∨ p ∣ b:= by exact (Nat.Prime.dvd_mul hp).mp h3
        rcases h3 with h3 | h3
        .
          -- Case where p divides a
          rcases h3 with ⟨k, hk⟩
          subst a
          -- Since product equals p, other digits must be 1
          replace h2 : k * b * c * d = 1:= by
            have g1 : p ≠ 0:= by omega
            rw [show p * k * b * c * d = p * (k * b * c * d) by ring] at h2
            exact (Nat.mul_eq_left g1).mp h2
          simp at h2
          rcases h2 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
          simp
        .
          -- Case where p divides b
          rcases h3 with ⟨k, hk⟩
          subst b
          -- Since product equals p, other digits must be 1
          replace h2 : k * a * c * d = 1:= by
            have g1 : p ≠ 0:= by omega
            rw [show a * (p * k) * c * d = p * (k * a * c * d) by ring] at h2
            exact (Nat.mul_eq_left g1).mp h2
          simp at h2
          rcases h2 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
          simp
      .
        -- Case where p divides c
        rcases h3 with ⟨k, hk⟩
        subst c
        -- Since product equals p, other digits must be 1
        replace h2 : k * a * b * d = 1:= by
          have g1 : p ≠ 0:= by omega
          rw [show a * b * (p * k) * d = p * (k * a * b * d) by ring] at h2
          exact (Nat.mul_eq_left g1).mp h2
        simp at h2
        rcases h2 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
        simp
  .
    -- Case where p divides d
    rcases h3 with ⟨k, hk⟩
    subst d
    -- Since product equals p, other digits must be 1
    replace h2 : a * b * c * k = 1:= by
      have g1 : p ≠ 0:= by omega
      rw [show a * b * c * (p * k) = p * (a * b * c * k) by ring] at h2
      exact (Nat.mul_eq_left g1).mp h2
    simp at h2
    rcases h2 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    simp
