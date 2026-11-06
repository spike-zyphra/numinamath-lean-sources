import Mathlib

/- a) Show that if \( a \) and \( b \) are positive integers with \( (a, b) = 1 \), then \( (a^n, b^n) = 1 \) for all positive integers \( n \)-/
theorem number_theory_4516_1 {a b : ℕ} (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hn : 0 < n):
    (a^n).Coprime (b^n) := by
  have hanpos : 0 < a^n := Nat.pow_pos ha
  have hbnpos : 0 < b^n := Nat.pow_pos hb
  -- as a,b coprime we have primeFactors of a,b are disjoint
  -- further primeFactors of a is the same of a^n, primeFactors of b is the same of b^n
  -- hence primeFactors of a^n,b^n are disjoint
  -- which means a^n,b^n are coprime
  rwa [← Nat.disjoint_primeFactors ha.ne' hb.ne',
    ← Nat.primeFactors_pow a hn.ne',
    ← Nat.primeFactors_pow b hn.ne',
    Nat.disjoint_primeFactors hanpos.ne' hbnpos.ne'] at hab

/- b) Use part (a) to prove that if \( a \) and \( b \) are integers such that \( a^n \mid b^n \) where \( n \) is a positive integer, then \( a \mid b \).-/
theorem number_theory_4516_2 {a b n : ℕ} (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) (hab : a^n ∣ b^n) : a ∣ b := by
  have hanpos : 0 < a^n := Nat.pow_pos ha
  have hbnpos : 0 < b^n := Nat.pow_pos hb
  -- a^n | b^n means for prime p, `Nat.factorization a^n` ≤ `Nat.factorization b^n`
  rw [← Nat.factorization_le_iff_dvd hanpos.ne' hbnpos.ne', Nat.factorization_pow,
    Nat.factorization_pow] at hab
  -- similiar, a | b means for prime p, `Nat.factorization a` ≤ `Nat.factorization b`
  rw [← Nat.factorization_le_iff_dvd ha.ne' hb.ne']
  -- as `Nat.factorization a^n` = `n*Nat.factorization a`, desired conclusion is duduced.
  rw [Finsupp.le_def] at hab ⊢
  intro i
  specialize hab i
  simp at hab
  nlinarith
