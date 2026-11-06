import Mathlib

/- Find all prime numbers $p$ such that

$$
(x+y)^{19}-x^{19}-y^{19}
$$

is a multiple of $p$ for any positive integers $x, y$. -/
theorem number_theory_604311 :
  { p : ℕ | p.Prime ∧ ∀ x y : ℤ, x > 0 → y > 0 → (p : ℤ) ∣ ((x + y) ^ 19 - x ^ 19 - y ^ 19) } = {2, 3, 7, 19} := by
  ext p
  simp
  constructor
  -- First, we prove that if p satisfies the condition, then p must be one of 2, 3, 7, 19
  . rintro ⟨hp, H⟩
    -- Substitute x = 1 and y = 1 into the condition
    have h₁ := H 1 1 (by norm_num) (by norm_num)
    -- Substitute x = 2 and y = 1 into the condition
    have h₂ := H 2 1 (by norm_num) (by norm_num)
    -- Simplify the expressions
    norm_num at h₁ h₂
    -- Convert the expressions to ℕ
    norm_cast at h₁ h₂
    -- We know that p must divide the gcd of the two expressions
    have h₃ : p ∣ Nat.gcd 524286 1161737178 := Nat.dvd_gcd h₁ h₂
    -- Calculate the prime factors of the gcd
    simp at h₃
    replace h₃ : p ∈ Nat.primeFactors 798 := Nat.mem_primeFactors.mpr ⟨hp, h₃, by norm_num⟩
    rw [show Nat.primeFactors 798 = {2, 3, 7, 19} by native_decide] at h₃
    simp at h₃
    exact h₃
  . -- Now, we prove that if p is one of 2, 3, 7, 19, then it satisfies the condition
    rintro hp
    -- We capture the common characteristic of the primes
    -- They all satisfy p - 1 ∣ 18
    obtain ⟨k, hk⟩ : p - 1 ∣ 18 := by
      rcases hp with rfl | rfl | rfl | rfl
      all_goals
        decide
    replace hp : p.Prime := by
      rcases hp with rfl | rfl | rfl | rfl
      all_goals
        decide
    use hp
    -- We prove that p divides x^19 - x for any integer x
    have H (x : ℤ) : ↑p ∣ x ^ 19 - x := by
      -- Two cases: either p divides x or it doesn't
      by_cases h : ↑p ∣ x
      . -- If p divides x, then p divides x^19 and x
        exact Int.dvd_sub (dvd_pow h (by simp)) h
      . -- If p doesn't divide x, then p and x are coprime
        rw [← Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)] at h
        -- We use Fermat's Little Theorem to show that x^(p-1) ≡ 1 (mod p)
        have H := Int.ModEq.pow_card_sub_one_eq_one hp h.symm
        -- Take the k-th power of both sides and simplify
        apply Int.ModEq.pow k  at H
        simp [← pow_mul, ← hk] at H
        -- Multiply both sides by x and simplify
        apply Int.ModEq.mul_left x at H
        ring_nf at H
        exact Int.ModEq.dvd H.symm
    -- Now x ^ 19 has the same remainder as x modulo p
    -- So are y ^ 19 and y, and (x + y) ^ 19 and x + y
    -- The rest part is trivial
    rintro x y - -
    obtain ⟨kx, hkx⟩ := H x
    obtain ⟨ky, hky⟩ := H y
    obtain ⟨kz, hkz⟩ := H (x + y)
    rw [show (x + y) ^ 19 - x ^ 19 - y ^ 19 = p * (kz - kx - ky) by linear_combination hkz - hkx - hky]
    exact Int.dvd_mul_right _ _
