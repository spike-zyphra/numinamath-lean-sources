import Mathlib

/-- Prove that among $2^{1}-1, 2^{2}-1, 2^{3}-1, \cdots, 2^{n-1}-1$
    there is at least one number divisible by $n$, where $n$ is an odd number greater than 1. -/
theorem number_theory_211102 (n : ℕ) (hn : Odd n ∧ n > 1) :
    ∃ i ∈ Finset.Icc 1 (n - 1), n ∣ (2 ^ i - 1) := by
  obtain ⟨hn1,hn2⟩ := hn
  -- Consider the Euler totient of n, $\varphi(n)$. We show it fulfills the conditions.
  exists n.totient
  constructor
  · rw[Finset.mem_Icc]
    · constructor
      -- It is positive since at least 1 is coprime to n.
      · exact Nat.totient_pos.mpr (by linarith)
      -- It is by definition smaller than n.
      · exact Nat.le_sub_one_of_lt $ Nat.totient_lt _ hn2
  -- It remains to be seen that $n \mid 2^{\varphi(n)} - 1$, or equivalently,
  -- $2^{\varphi(n)} \equiv 1$ modulo $n$. But since $n$ and $2$ are coprime,
  -- this is the statement of Euler's totient theorem.
  · have := Nat.ModEq.pow_totient (x := 2) (n := n) (Odd.coprime_two_left hn1)
    symm at this
    have le : 1 ≤ 2 ^ n.totient := Nat.two_pow_pos _
    rwa[Nat.modEq_iff_dvd' le] at this