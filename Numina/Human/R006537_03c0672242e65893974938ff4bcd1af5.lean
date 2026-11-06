import Mathlib

/-"Let $S$ and $K$ be positive integers. Donuts are fried in batches of $20$. Donuts are sold in boxes of $S$.
Assume that $S$ and $K$ are such that there is a unique integer $N$ satisfying both:
1. $N$ is a multiple of 20.
2. $K \cdot S \le N < (K+1) \cdot S$. (This is equivalent to $N \operatorname{div} S = K$, where $\operatorname{div}$ is integer division).
If Donut Haven fries $N$ donuts (the total amount), how many donuts are left over after packing $K$ boxes (i.e., what is the value of $N - K \cdot S$)? Show the answer is $(-K \cdot S) \bmod 20$."
-/

theorem number_theory_638226 (S K N: ℤ) (h3: 20 ∣ N) (h4: K * S ≤ N) (h5: N < (K + 1) * S)
  (h6: ∀ N', 20 ∣ N' → K * S ≤ N' → N' < (K + 1) * S → N' = N): N - K * S = (-K * S) % 20 := by

  -- it suffices to show that N - K * S is less than 20
  suffices N - K * S < 20 by
    have u: N - K * S = (N - K * S) % 20 := by
      symm
      apply Int.emod_eq_of_lt
      omega
      tauto
    rw [u]
    clear u
    rw [Int.sub_emod]
    apply Int.emod_eq_zero_of_dvd at h3
    simp [h3]
    omega

  by_contra! l
  replace h3: 20 ∣ N - 20 := by
    apply Int.dvd_sub
    exact h3
    norm_num
  specialize h6 (N - 20) h3 (by omega) (by omega)
  omega