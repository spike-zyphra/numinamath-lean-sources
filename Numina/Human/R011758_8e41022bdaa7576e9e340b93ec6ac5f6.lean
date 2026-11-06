import Mathlib

/- 1. (8 points) If the difference between two prime numbers is exactly 2, these two prime numbers are called a pair of twin primes.
For example, 3 and 5 are a pair of twin primes, and 29 and 31 are also a pair of twin primes. In number theory research, twin primes are one of the hottest research topics. Chinese-American mathematician Yitang Zhang has made remarkable achievements in this field, and his story has inspired more young students to devote themselves to mathematical research. Among the integers not exceeding 100, a total of _ 8 pairs of twin primes can be found. -/
theorem number_theory_291954 : Set.ncard {(p, q) : ℕ×ℕ | p ≤ q ∧ q ≤ 100 ∧ p.Prime ∧ q.Prime ∧ |(p : ℤ) - q| = 2} = 8 := by
  suffices {(p, q) : ℕ×ℕ | p ≤ q ∧ q ≤ 100 ∧ p.Prime ∧ q.Prime ∧ |(p : ℤ) - q| = 2} = Finset.filter (λ((p, q) : ℕ×ℕ) ↦ (p ≤ q ∧ p.Prime ∧ q.Prime ∧ |(p : ℤ) - q| = 2)) (Finset.Icc 0 100 ×ˢ Finset.Icc 0 100) by
    rw [this, Set.ncard_coe_Finset]
    native_decide
  ext ⟨p, q⟩
  constructor <;> simp
  · intro h₁ h₂ h₃ h₄ h₅
    use by omega
  · intro h₁ h₂ h₃ h₄ h₅ h₆
    use by omega
