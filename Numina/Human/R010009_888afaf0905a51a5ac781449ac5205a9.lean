import Mathlib

/- Let $p$ and $q$ be two consecutive odd prime numbers. Prove that $p+q$ is a product of at least three positive integers greater than 1 (not necessarily different). -/
theorem number_theory_240677 {p q : ℕ} (hp : p.Prime ∧ Odd p) (hq : q.Prime ∧ Odd q) (hpq : p < q) (h : ¬∃ r : ℕ, p < r ∧ r < q ∧ r.Prime) :
    ∃ a b c, a > 1 ∧ b > 1 ∧ c > 1 ∧ a * b * c = p + q := by
  -- Note that q - p is even.
  have h₀ : Even (q - p : ℤ) := by
    apply Odd.sub_odd
    simp [hq.2]
    simp [hp.2]
  norm_cast at h₀
  rw [Int.subNatNat_of_le] at h₀
  simp at h₀
  -- Write q - p = 2k.
  obtain ⟨k, h₀⟩ := h₀
  rw [<-two_mul] at h₀
  -- Note that p + k is not a prime.
  let r := p + k
  have h₁ : ¬Nat.Prime r := by
    by_contra!
    -- Assume on the contrary that r = p + k is a prime, then it contradicts with our assumption that p and q are consecutive primes.
    absurd h
    use r
    refine ⟨by omega, by omega, this⟩
  apply Nat.exists_dvd_of_not_prime at h₁
  obtain ⟨s, h₁, h₂, h₃⟩ := h₁
  rw [dvd_iff_exists_eq_mul_right] at h₁
  obtain ⟨t, h₁⟩ := h₁
  -- We get p + (p + 2k) = 2 * (p + k) = 2 * s * t.
  use 2, s, t
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  . -- Verify that s > 1.
    by_contra!
    -- Assume on the contrary that s ≤ 1, then s = 0 because s ≠ 1, contradiction.
    replace this : s = 0 := by
      omega
    simp_all
  . -- Verify that t > 1.
    by_contra!
    -- Assume on the contrary that t ≤ 1, then t = 0 or 1, contradiction.
    replace this : t = 0 ∨ t = 1 := by
      omega
    rcases this with (h₄ | h₄)
    . simp [h₄, r] at h₁
      norm_num [h₁.1] at hp
    . simp_all
  . -- Verify that 2st = p + q.
    rw [show q = p + 2 * k by omega, mul_assoc, <-h₁]
    simp [r]
    omega
  . -- Verify that 2 ≤ r.
    simp [r]
    calc
      2 ≤ p := Nat.Prime.two_le hp.1
      _ ≤ p + k := by simp
  . -- Verify that p ≤ q.
    exact le_of_lt hpq