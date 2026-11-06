import Mathlib


/- Let $k$ and $l$ be non-negative integers. A sequence of integers $(a_n)_{n \ge 0}$ is defined by $a_0=1$ and $a_{n+1}=a_n^2+1$ for each $n \ge 0$.
Determine $\operatorname{gcd}(a_k, a_l)$. Show that this value is equal to $a_g$, where $g = \operatorname{gcd}(k+1, l+1)-1$.-/
theorem number_theory_640350 {k l: ℕ} (a: ℕ → ℕ)
  (ha0: a 0 = 1) (ha: ∀n, a (n+1) = (a n)^2 + 1):
  Nat.gcd (a k) (a l) = a (Nat.gcd (k+1) (l+1) - 1) := by

  -- observe that (an, a_{n+k+1}) is gcd (an, ak)
  have h1' (n m: ℕ): ∃ j:ℕ, a (n+m+1) = j * a n + a m := by
    induction' m with m ih
    · use (a n)
      simp [ha, ha0, pow_two]
    · rw [← add_assoc, ha (n+m+1)]
      rcases ih with ⟨j, hj⟩
      use ((a n)*j^2 + 2*j*(a m))
      rw [ha m, hj]
      ring
  have h1 (n m: ℕ): Nat.gcd (a n) (a (n+m+1)) = Nat.gcd (a n) (a m) := by
    rcases (h1' n m) with ⟨j, hj⟩
    rw [hj]
    apply Nat.gcd_mul_right_add_right

  -- gcd (an, a_{k(n+1)-1}) = an
  have h2' {n i: ℕ} (hi: 0 < i): (a n).gcd (a (i*(n+1) - 1)) = a n := by
    induction' i,hi using Nat.le_induction with i hi ih
    · simp
    · have: (i+1)*(n+1)-1 = (i*(n+1)-1) + n + 1 := by
        rw [Nat.add_one_mul]
        simp only [Nat.add_succ_sub_one]
        have: 1 ≤ i*(n+1) := by
          simp only [Nat.succ_eq_add_one, zero_add] at hi
          refine Right.one_le_mul hi ?_
          simp
        omega
      rw [this, Nat.gcd_comm]
      replace (m:ℕ): (a (m+n+1)).gcd (a n) = (a m).gcd (a n) := by
        rw [show m+n+1 = n+m+1 by ring, Nat.gcd_comm, h1, Nat.gcd_comm]
      rw [this, Nat.gcd_comm, ih]
  have h2 {n i: ℕ} (hi: 0 < i) (hn: 0 < n):
    (a (n-1)).gcd (a (i*n-1)) = a (n-1) := by
    nth_rw 2 [show n = n-1+1 by omega]
    apply h2' hi

  -- we claim gcd (an, a_{m+k(n+1)}) = gcd (an, am)
  have h3 {n m j: ℕ} (hj: 0 < j):
    (a n).gcd (a (m + j*(n+1))) = (a n).gcd (a m) := by
    induction' j,hj using Nat.le_induction with j hj ih
    · simp [← add_assoc, add_comm m n, h1]
    · rw [show m+(j+1)*(n+1) = n + (m+j*(n+1)) + 1 by ring]
      rw [h1, ih]

  -- consider k mod l+1, l mod k+1, use Euclidean algorithm.

  set K := k+1 with K_def
  set L := l+1 with L_def
  suffices (a (K-1)).gcd (a (L-1)) = (a (K.gcd L - 1)) by
    rw [← this]
    simp [K_def, L_def]
  have Kpos: 0 < K := by simp [K_def]
  have Lpos: 0 < L := by simp [L_def]

  revert Kpos Lpos
  induction' K,L using Nat.gcd.induction with k k l kpos ih
  · simp
  · intro kpos lpos
    by_cases hdvd: k ∣ l
    · rcases hdvd with ⟨j, hj⟩
      have jpos: 0 < j := by
        rw [hj] at lpos
        exact Nat.pos_of_mul_pos_left lpos
      rw [hj, mul_comm k j, h2 jpos kpos, Nat.gcd_mul_left_right]
    · have: 0 < l % k := by
        exact Nat.emod_pos_of_not_dvd hdvd
      simp only [this, kpos, forall_const, ← Nat.gcd_rec] at ih
      rw [← ih, Nat.gcd_comm _ (a (k-1))]
      by_cases hkl: l ≤ k
      · by_cases hh: k = l
        · simp [hh] at hdvd
        · rw [Nat.mod_eq_of_lt]
          exact Nat.lt_of_le_of_ne hkl fun a => hh (id (Eq.symm a))
      · push_neg at hkl
        -- consider l mod k.
        obtain ⟨j, hj⟩: ∃ j, l-1 = (l % k - 1) + j*k ∧ 0 < j := by
          use l/k
          constructor
          · suffices l = l % k + l/k*k by
              omega
            exact Eq.symm (Nat.mod_add_div' l k)
          · refine Nat.div_pos_iff.mpr ?_
            exact ⟨kpos, hkl.le⟩
        rw [hj.left]
        nth_rw 3 [show k = k-1+1 by omega]
        apply h3 hj.right
