import Mathlib

/- Bob sends a secret message to Alice using her RSA public key $n = 400000001.$ Eve wants to listen in on their conversation. But to do this, she needs Alice's private key, which is the factorization of $n.$ Eve knows that $n = pq,$ a product of two prime factors. Find $p$ and $q.$ -/
theorem number_theory_77447 {n : ℕ} (hn : n = 400000001) :
    ∃ p q, p.Prime ∧ q.Prime ∧ p * q = n ∧ p = 20201 ∧ q = 19801 := by 
  use 20201, 19801
  norm_num [hn]
  <;> decide