import Mathlib

/- Show that if \( n \) is a positive integer, then
\[
\phi(2n) =
\begin{cases}
\phi(n) & \text{if } n \text{ is odd} \\
2\phi(n) & \text{if } n \text{ is even}
\end{cases}
\]-/
theorem number_theory_4866
    (n : ℕ)
    (hn : n > 0)
    : Nat.totient (2 * n) = if Even n then 2 *  Nat.totient n else  Nat.totient n := by
  -- **Case 1: \( n \) is odd.**
  by_cases h:Even n
  simp[h]
  have h2:=Nat.totient_gcd_mul_totient_mul 2 n
  simp at h2
  cases h
  rename_i q hq
  ring_nf at hq
  -- find gcd 2 n = 2
  have hgcd:(Nat.gcd 2 n)=2:= by rw[hq];simp
  rw [hgcd] at h2
  simp at h2
  linarith

  -- **Case 2: \( n \) is even.**
  simp [h]
  suffices hcop: n.Coprime 2
  --use (m * n).totient = m.totient * n.totient
  have hrw:=Nat.totient_mul hcop
  simp at hrw
  rw[mul_comm]
  exact hrw
  --prove n.Coprime 2
  have h: Odd n := by aesop
  simp
  exact h
