import Mathlib

/- Compute the sum of all 2-digit prime numbers $p$ such that there exists a prime number $q$ for which $100 q+p$ is a perfect square.-/
theorem number_theory_610405 :
    ∑ᶠ p ∈ {p : ℕ | p ∈ Finset.Ico 10 100 ∧ Nat.Prime p ∧ ∃ q, Nat.Prime q ∧ IsSquare (100 * q + p)}, p = 179 := by
  -- It suffices to show that the only such prime numbers are 29, 61 and 89.
  suffices {p : ℕ | p ∈ Finset.Ico 10 100 ∧ Nat.Prime p ∧ ∃ q, Nat.Prime q ∧ IsSquare (100 * q + p)} = ({29, 61, 89} : Finset ℕ) by
    rw [this, finsum_mem_coe_finset]
    simp
  -- Simplify the goal into two parts.
  ext p
  simp
  constructor
  . rintro ⟨⟨h₀, h₁⟩, hp, q, hq, ⟨m, h₂⟩⟩
    -- We will show that p % 4 = 1.
    have h₃ : (100 * q + p : ℤ) % 4 = 1 := by
      zify at h₂
      rw [h₂, <-pow_two]
      apply Int.sq_mod_four_eq_one_of_odd
      by_contra!
      simp at this
      rw [even_iff_two_dvd] at this
      replace this : 2 ∣ m * m := this.trans (by apply Nat.dvd_mul_right)
      norm_cast at h₂
      replace h₂ : 2 ∣ p := by
        omega
      -- We get p = 2, which is a contradiction since we assumed that p is a 2-digit prime.
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hp] at h₂
      omega
    replace h₃ : p % 4 = 1 := by
      omega
    -- Show that p % 10 = 0 ∨ p % 10 = 1 ∨ p % 10 = 4 ∨ p % 10 = 5 ∨ p % 10 = 6 ∨ p % 10 = 9.
    have h₄ : (100 * q + p) % 10 = 0 ∨ (100 * q + p) % 10 = 1 ∨ (100 * q + p) % 10 = 4 ∨ (100 * q + p) % 10 = 5 ∨ (100 * q + p) % 10 = 6 ∨ (100 * q + p) % 10 = 9 := by
      have (a : ℕ) : a % 10 = 0 ∨ a % 10 = 1 ∨ a % 10 = 2 ∨ a % 10 = 3 ∨ a % 10 = 4 ∨ a % 10 = 5 ∨ a % 10 = 6 ∨ a % 10 = 7 ∨ a % 10 = 8 ∨ a % 10 = 9 := by
        omega
      rw [h₂]
      rcases this m with (h | h | h | h | h | h | h | h | h | h)
      <;> simp [h, Nat.mul_mod, Nat.add_mod]
    rw [show (100 * q + p) % 10 = p % 10 by omega] at h₄
    -- We can list the possibilities of p.
    replace h₃ : p = 21 ∨ p = 25 ∨ p = 29 ∨ p = 41 ∨ p = 45 ∨ p = 49 ∨ p = 61 ∨ p = 65 ∨ p = 69 ∨ p = 81 ∨ p = 85 ∨ p = 89 := by
      omega
    rcases h₃ with (h | h | h | h | h | h | h | h | h | h | h | h)
    <;> first | tauto | norm_num [h] at hp
    -- It suffices only to show that p = 41 does not qualify, i.e., assume p = 41 and try to derive a contradiction.
    -- Show that q % 2 ≠ 1.
    have h₅ : q % 2 ≠ 1 := by
      by_contra!
      -- Examine the equation h₂ modulo 8.
      have h₅ : m * m % 8 = 0 ∨ m * m % 8 = 1 ∨ m * m % 8 = 4 := by
        have (a : ℕ) : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
          omega
        rcases this m with (h | h | h | h | h | h | h | h)
        <;> simp [h, Nat.mul_mod, Nat.add_mod]
      rw [<-h₂] at h₅
      -- It contradicts the fact that q % 2 = 1 (so 100 * q % 8 = 5) and p % 8 = 1.
      omega
    -- We have 2 ∣ q, hence q = 2, but 241 is not a square.
    replace h₅ : 2 ∣ q := by
      omega
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hq] at h₅
    norm_num [h, <-h₅] at h₂
    -- Since 15² < 241 < 16², we have 241 is not a square.
    linarith only [show 15 < m by nlinarith, show m < 16 by nlinarith]
  . -- Now we show that p = 29, 61 or 89 are valid.
    rintro (hp | hp | hp)
    <;> norm_num [hp]
    . -- Case p = 29. We take q = 7 and 729 = 27².
      use 7, by norm_num, 27
    . -- Case p = 61. We take q = 3 and 361 = 19².
      use 3, by norm_num, 19
    . -- Case p = 89. We take q = 2 and 289 = 17².
      use 2, by norm_num, 17
