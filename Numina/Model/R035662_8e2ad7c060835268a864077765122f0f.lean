import Mathlib

theorem number_theory_230574 {p : ℕ} (hp : Nat.Prime p) (a k : ℕ) :
    ∑ i ∈ Finset.range (a + 1), p^(i * k) = ∑ d in (p^a).divisors, d^k := by 
  have h1 : Fact p.Prime := ⟨hp⟩
  rw [Nat.divisors_prime_pow hp a]
  have h2 : ∑ i ∈ Finset.range (a + 1), p ^ (i * k) = ∑ i in Finset.range (a + 1), (p ^ i) ^ k := by
    congr
    funext i
    ring_nf
  rw [h2]
  simp [Finset.sum_image]