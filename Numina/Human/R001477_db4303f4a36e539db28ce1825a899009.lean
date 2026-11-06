import Mathlib

open Finset

/-30. (SWE 2) ${ }^{\mathrm{IMO} 5}$ For which positive integers $n$ does there exist a positive integer $N$ such that none of the integers $1+N, 2+N, \ldots, n+N$ is the power of a prime number?-/
theorem other_24247 : ∀ n, ∃ N, ∀ i ∈ range n, ¬ IsPrimePow (1 + i + N) := by
-- Prove by contradiction, assume that for any $N$, there exists some index $i$ such that $1+i+N$ is a prime power
  intro n; by_contra! h; simp [isPrimePow_def] at h
-- According to the reference anser, specialize the assumption at $N=(n+1).factorial^2+1$ and
-- assume there is an index $j$ and a prime $p$ such that $1+j+N$ is equal to $p^k$ for some $k$
  obtain ⟨j, ⟨jlt, ⟨p, ⟨ppr, ⟨k, ⟨kpos, pkpow⟩⟩⟩⟩⟩⟩ := h ((n + 1).factorial ^ 2 + 1)
  have := ppr.nat_prime.two_le
  ring_nf at pkpow; have : 2 + j ∣ 2 + j + (1 + n).factorial ^ 2 := by
    rw [← Nat.dvd_add_iff_right (show _ by rfl)]; apply dvd_pow
    apply Nat.dvd_factorial; any_goals linarith
-- Prove that $2+j$ is equal to $p^r$ for some $r$ by showing $2+j$ divides $1+j+N$
  rw [← pkpow] at this; obtain ⟨r, ⟨rle, prpow⟩⟩ := (Nat.dvd_prime_pow ppr.nat_prime).mp this
  have rpos : 1 ≤ r := by by_contra!; simp at this; simp [this] at prpow; linarith
-- It suffices to show that $p^(r+1)$ divides $2+j$ since the latter is equal to $p^r$
  suffices : p ^ (r + 1) ∣ 2 + j
  · rw [prpow, Nat.pow_dvd_pow_iff_le_right] at this; simp at this; linarith
  replace rle : r + 1 ≤ k := by
    by_contra!; replace this : r = k := by linarith
    rw [this] at prpow; simp [prpow] at pkpow; suffices : 0 < (1 + n).factorial; linarith
    positivity
-- Prove that $p^(r+1)$ divides $2+j$
  rw [← Nat.pow_dvd_pow_iff_le_right (show 1<p by linarith), pkpow] at rle
  apply (Nat.dvd_add_iff_left _).mpr rle; rw [pow_succ, pow_two, ← prpow]
  apply Nat.mul_dvd_mul; apply Nat.dvd_factorial; any_goals linarith
  apply Nat.dvd_factorial; linarith; rw [Nat.lt_iff_add_one_le] at jlt; calc
    _ ≤ p ^ r := by apply Nat.le_self_pow; linarith
    _ ≤ _ := by linarith