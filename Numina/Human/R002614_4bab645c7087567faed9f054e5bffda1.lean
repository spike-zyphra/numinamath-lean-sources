import Mathlib


/-- For how many positive integers $n$ is $\frac{n}{30-n}$ also a positive integer?

$\textbf{(A)}\ 4\qquad\textbf{(B)}\ 5\qquad\textbf{(C)}\ 6\qquad\textbf{(D)}\
7\qquad\textbf{(E)}\ 8$ -/
theorem number_theory_96414 :
    Set.ncard {n : ℕ | 0 < n ∧ ∃ k : ℕ, 0 < k ∧ n = k * (30 - n)} = 7 := by

  -- Let $s$ be the set of positive integers $n$ such that $\frac{n}{30-n}$ is a positive integer.
  set s := {n : ℕ | 0 < n ∧ ∃ k : ℕ, 0 < k ∧ n = k * (30 - n)}

  -- We know that $n \le 30$ or else $30-n$ will be negative, resulting in a negative fraction.
  have h1 {n} (hn : n ∈ s) : n < 30 := by
    simp [s] at hn
    rcases hn with ⟨hn, k, hk, hnk⟩
    contrapose! hn
    calc _ = k * (30 - n) := by nth_rw 1 [hnk]
         _ ≤ k * 0 := by gcongr; omega
         _ = 0 := by rfl

  -- We also know that $n \ge 15$ or else the fraction's denominator will exceed its numerator
  -- making the fraction unable to equal a positive integer value.
  have h2 {n} (hn : n ∈ s) : 15 ≤ n := by
    simp [s] at hn
    rcases hn with ⟨hn, k, hk, hnk⟩

    replace hk : 1 ≤ k := by exact hk

    have : n ≥ 30 - n := by
      calc _ = k * (30 - n) := by nth_rw 1 [hnk]
           _ ≥ 1 * (30 - n) := by gcongr
           _ = _ := by rw [one_mul]

    omega

  -- Therefore, $s$ is just the set of integers between 15 and 30 such that $30-n$ divides $n$.
  let t := {n ∈ Finset.Ico 15 30 | 30 - n ∣ n}
  have : s = t := by
    ext n
    constructor
    · intro hn
      simp [t]
      refine ⟨⟨h2 hn, h1 hn⟩, ?_⟩
      simp [s] at hn
      rcases hn with ⟨hn, k, hk, hnk⟩
      exact Dvd.intro_left k (id (Eq.symm hnk))
    · intro hn
      simp [t] at hn
      rcases hn with ⟨hn, k, hnk⟩
      simp [s]
      refine ⟨by linarith, k, ?_, by nth_rw 1 [hnk]; ring⟩
      by_contra! hk
      simp at hk
      subst hk
      simp at hnk
      omega

  -- Substituting all values $n$ from $15$ to $30$ gives us integer values for $n=15, 20, 24, 25,
  -- 27, 28, 29$. Counting them up, we have $\boxed{\textbf{(D)}\ 7}$ possible values for $n$.
  rw [this, Set.ncard_coe_Finset]
  decide