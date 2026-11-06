import Mathlib

/- How many positive integers $n$ are there such that $n!(2n+1)$ and $221$ are relatively prime?

$
\textbf{(A)}\ 10
\qquad\textbf{(B)}\ 11
\qquad\textbf{(C)}\ 12
\qquad\textbf{(D)}\ 13
\qquad\textbf{(E)}\ \text{None of the above}
$ -/
theorem number_theory_36814 :
    Set.encard {n : ℕ | 0 < n ∧ (n.factorial * (2 * n + 1)).Coprime 221} = 10 := by
  -- We can list all the solutions.
  suffices H : {n : ℕ | 0 < n ∧ (n.factorial * (2 * n + 1)).Coprime 221} = ({1, 2, 3, 4, 5, 7, 9, 10, 11, 12} : Finset ℕ) by
    rw [H, Set.encard_coe_eq_coe_finsetCard]
    simp
  ext n
  constructor
  -- We check the ten numbers are indeed solutions by simple computation.
  swap
  {
    simp only [Set.mem_setOf_eq, Finset.mem_coe]
    revert n
    native_decide
  }
  -- If n satisfies the condition, then n must be in the interval (0, 13).
  intro ⟨hn, h⟩
  have H : n ∈ Finset.Ioo 0 13 := by
    simp [hn]
    -- Otherwise, n ≥ 13
    -- So 13 ∣ n!
    -- Then n! * (2n + 1) is divisible by 13, thus not coprime to 221.
    by_contra! hn'
    apply Nat.dvd_factorial (by simp) at hn'
    have h₁ : 13 ∣ n.factorial * (2 * n + 1) := Dvd.dvd.mul_right hn' _
    have h₂ : Nat.Coprime 13 221 := Nat.Coprime.coprime_dvd_left h₁ h
    simp [Nat.Coprime] at h₂
  -- We can check the twelve cases by `native_decide`.
  clear hn
  revert h
  revert n
  native_decide
