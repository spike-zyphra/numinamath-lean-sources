import Mathlib

/- Let $a, b, c, d$ be positive integers such that $a b=c d$. Prove that $a+b+c+d$ is not prime.-/
theorem number_theory_239017 {a b c d : ℕ} (hpos : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) (h : a * b = c * d) :
    ¬(a + b + c + d).Prime := by
  -- As $a b=c d$, we get $a(a+b+c+d)=(a+c)(a+d)$.
  have key : a * (a + b + c + d) = (a + c) * (a + d) := by ring_nf; rw [h]; ring
  have : a + b + c + d ∣ (a + c) * (a + d) := ⟨a, by rw [← key, mul_comm]⟩
  -- If $a+b+c+d$ were a prime,
  intro hp
  rcases hpos with ⟨apos, bpos, cpos, dpos⟩
  -- then it would be a factor in either $a+c$ or $a+d$,
  rcases hp.dvd_mul.mp this with H | H
  -- which are both smaller than $a+b+c+d$.
  . have := Nat.le_of_dvd (by positivity) H; omega
  . have := Nat.le_of_dvd (by positivity) H; omega
