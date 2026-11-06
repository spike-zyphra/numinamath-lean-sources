import Mathlib

/- Let \( n \) be a positive integer. We define a sequence of positive integers \( n_1, n_2, n_3, \ldots \) recursively, where \( n_1 = \phi(n) \) and \( n_{k+1} = \phi(n_k) \) for \( k = 1, 2, 3, \ldots \). Show that there exists a positive integer \( r \) such that \( n_r = 1 \).-/
theorem number_theory_4876
    (n : ℕ)
    (posn : n > 0)
    (nseq : ℕ → ℕ)
    (nseqdef : nseq 1 = Nat.totient n ∧ ∀ k ≥ 1, nseq (k + 1) = Nat.totient (nseq k))
    : (∃ r > 0, nseq r = 1) := by
  --prove by contradition
  by_contra h
  push_neg at h
  -- prove nseq r >=2
  have h2:∀ r, r > 0 → nseq r ≥ 2 := by
    intro r hr
    have h1:= h r hr
    by_cases h0:nseq r = 0
    -- prove nseq k>0
    have hge0:∀ k ≥ 1, nseq k > 0 := by
      intro k hk
      cases k
      trivial
      rename_i k
      -- use induction to prove nseq k >0
      induction k
      simp
      rw [nseqdef.1]
      simp
      linarith
      rename_i k hk2
      rw [nseqdef.2 (k+1) (by linarith)]
      simp
      apply hk2
      linarith
    have hr:r ≥ 1 := by linarith
    have h3:= hge0 r hr
    linarith
    omega
  -- 4. **Termination of the Sequence**: Since \( n_k \) is a sequence of positive integers that is strictly decreasing, it must eventually reach 1. The only positive integer that can be reached after a finite number of steps is 1, because \( n_k \) cannot become negative or zero.
  have hdown: ∀ m ≥ 1, nseq (m+1)< nseq m := by
    intro m hm
    rw[nseqdef.2 m hm]
    apply Nat.totient_lt
    have h3:= h2 m (by linarith)
    omega
  have hdown2: ∀ m ≥ 1, nseq (m+1)≤ (nseq m) -1 := by
    intro m hm
    have h3:= hdown m hm
    omega
  -- prove after k step, nseq decreases by k
  have hdown3(m k:ℕ)(hm: 1 ≤ m): nseq (m+k)≤ (nseq m) -k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc]
      have hg1:= h2 (m+k+1) (by linarith)
      have hg2:= hdown2 (m+k) (by linarith)
      omega --magic
  -- find contradiction
  have h4:= hdown3 1 (nseq 1) (by linarith)
  have h5:= h2 (1 + nseq 1) (by linarith)
  omega
