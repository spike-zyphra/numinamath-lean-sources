import Mathlib

open Sym2 Finset

/- The set of ways to write `n` as the sum of two prime numbers.
   We use `Sym2` to represent the unordered pair. -/
def waysSumOfTwoPrimes (n : ℕ) : Set (Sym2 ℕ) :=
    { s(x, y) | (x : ℕ) (y : ℕ) (_ : x.Prime) (_ : y.Prime) (_ : x + y = n) }

/- The set of ways to write `n` as the sum of two prime numbers, represented as a `Finset`. -/
def waysSumOfTwoPrimesFinset (n : ℕ) : Finset (Sym2 ℕ) :=
    (((Icc 0 n) ×ˢ (Icc 0 n)).filter (fun (x, y) => x.Prime ∧ y.Prime ∧ x + y = n)).image Sym2.mk

/- Lemma: The two representations are equivalent. -/
lemma lemma_1 (n : ℕ) :
    waysSumOfTwoPrimesFinset n = waysSumOfTwoPrimes n := by
  -- Logically trivial, since `x` and `y` are both bounded by `n`.
  ext p
  simp only [waysSumOfTwoPrimesFinset, coe_image, coe_filter, mem_product, mem_Icc, zero_le,
    true_and, Set.mem_image, Set.mem_setOf_eq, Prod.exists, waysSumOfTwoPrimes, exists_prop,
    exists_and_left]
  constructor
  . rintro ⟨a, b, ⟨⟨⟨ha₁, hb₁⟩, ha₂, hb₂, hn⟩, rfl⟩⟩
    use a, ha₂, b, hb₂
  . rintro ⟨x, hx, y, hy, hn, rfl⟩
    use x, y
    simp only [and_self, and_true, hx, hy, hn]
    exact ⟨Nat.le.intro hn, by omega⟩

/- Find the smallest integer that can be written as the sum of two prime numbers in two different ways. -/
theorem number_theory_623331 :
    IsLeast {n | ∃ w₁ ∈ waysSumOfTwoPrimes n, ∃ w₂ ∈ waysSumOfTwoPrimes n, w₁ ≠ w₂} 10 := by
  simp [← lemma_1]
  constructor
  . -- We can compute waysSumOfTwoPrimesFinset 10 to {s(3, 7), s(5, 5)}.
    -- So there are two ways to write 10 as the sum of two prime numbers.
    native_decide
  . -- We check all n < 10.
    rintro n hn
    contrapose! hn
    -- We can compute all the waysSumOfTwoPrimesFinset n for n < 10.
    -- And check that there is only one way for each.
    revert n
    native_decide
