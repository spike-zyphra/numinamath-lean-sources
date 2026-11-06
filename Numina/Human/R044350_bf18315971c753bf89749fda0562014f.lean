import Mathlib

/- Show that if \( a \) and \( b \) are integers, then the arithmetic progression \( a, a+b, a+2b, \ldots \) contains an arbitrary number of consecutive composite terms.-/
theorem number_theory_4592 (a b : ℕ) (h : 1 ≤ b) :
    ∀ k : ℕ, ∃ m : ℕ, ¬Nat.Prime (a+m*b) ∧ m > k  := by
  intro k
  -- consider a=0
  cases a
  simp
  use(k+2)*2
  constructor
  rw[mul_assoc]
  apply Nat.not_prime_mul
  linarith
  linarith
  linarith
  --consider a=1
  rename_i a
  cases a
  simp
  -- consider (b*(k+1)+1)^2=1+b*(2k+2+(k+1)^2*b)
  use (2*k+2+(k+1)^2*b)
  have h1:1+(2*k+2+(k+1)^2*b)*b=(b*(k+1)+1)^2:=by ring
  rw[h1]
  constructor
  apply Nat.Prime.not_prime_pow
  linarith
  nlinarith
  -- consider a>=2
  rename_i a
  use (a+2)*(k+1)
  have h1:a + 1 + 1 + (a + 2)*(k+1) * b = (a+2)*((k+1)*b+1):= by ring
  rw[h1]
  constructor
  apply Nat.not_prime_mul
  linarith
  simp
  linarith
  nlinarith
