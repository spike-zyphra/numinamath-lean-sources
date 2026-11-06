import Mathlib

open scoped BigOperators
/-Suppose  $a_1,a_2, \dots$  is an infinite strictly increasing sequence of positive integers and  $p_1, p_2, \dots$  is a sequence of distinct primes such that  $p_n \mid a_n$  for all  $n \ge 1$ . It turned out that  $a_n-a_k=p_n-p_k$  for all  $n,k \ge 1$ . Prove that the sequence  $(a_n)_n$  consists only of prime numbers.-/

theorem number_theory_8878
  (a : ℕ → ℤ)
  (p : ℕ → ℤ)
  (h₀ : ∀ n, 0 < a n)
  (h₁ : StrictMono a)
  (h₂ : ∀ n, Prime (p n))
  (h₃ : ∀ n, p n ∣ a n)
  (h₄ : ∀ n k, a n - a k = p n - p k) :
  ∀ n, Prime (a n) := by
    intro n
    -- prove a0 = p0
    by_cases h: (a 0) = (p 0)
    -- prove an = pn
    have h2:= h₄ n 0
    rw [h] at h2
    simp at h2
    -- use h₂
    rw[h2]
    exact h₂ n
    -- cases 2 p0 ≠ a0
    apply False.elim

    -- show StrictMono (p n)
    have h₅: StrictMono p := by
      intro n k h
      have h1:= h₄ n k
      have h2:= h₄ k n
      have h3:= h₁ h
      linarith
    -- prove exist n such that pn > d
    have hinf: ∀n,(p n) ≥  (p 0) + n := by
      intro n
      induction n
      simp
      rename_i n hn2
      -- consider inductive case
      have hn1: n < n+1:= by linarith
      have hnnge1:= h₅ hn1
      have hnnge2: (p (n+1)) ≥ (p n) + 1 := by linarith
      -- use trans
      apply ge_trans hnnge2
      -- apply ge_add
      have :(p n) + 1 ≥ (p 0) + n + 1 := by linarith
      rw [add_assoc] at this
      norm_cast

    -- prove forall n, ∃ k, pk > n
    have h₆: ∀ n:ℕ  , ∃ k, (p k) > n := by
      intro n
      by_cases h: (p 0)>= 0
      use (n+1)
      have h1:= hinf (n+1)
      omega
      -- p0<0
      use (Int.natAbs (p 0) + n + 1)
      have h1:= hinf (Int.natAbs (p 0) + n + 1)
      simp at h1
      -- consider |p0|=-p0
      have h2:= Int.sign_mul_abs (p 0)
      have hsign: (p 0).sign = -1 := by apply Int.sign_eq_neg_one_of_neg; linarith
      rw [hsign] at h2
      -- simp h1
      rw [← h2] at h1
      ring_nf at h1
      simp at h1
      -- use >= n+1
      simp
      suffices hn: 1+n ≤ p ((p 0).natAbs + n + 1)
      linarith
      -- prove 1+n ≤ p ((p 0).natAbs + n + 1)
      have habs:|p 0| = - (p 0):= by linarith
      have heq: |p 0|.natAbs= (p 0).natAbs := by rw [habs];simp
      rw [heq] at h1
      have h5: 1 + (p 0).natAbs + n = (p 0).natAbs + n + 1 := by linarith
      rw [h5] at h1
      exact h1


    generalize eq: (a 0) - (p 0) = d
    -- find m to prove contradiction
    have h6:= h₆ (d.natAbs)
    rcases h6 with ⟨m, hm⟩

    have h3:= h₄ m 0
    -- prove an = pn - d
    have h4:a m = p m + d := by rw[← eq]; linarith
    -- have pn | an
    have h5:= h₃ m
    rcases  h5 with ⟨k, hk⟩
    rw [hk] at h4
    -- find d
    have h6:d=(p m)*(k-1) := by linarith
    -- prove k!=1
    by_cases hk0: k=1
    rw [hk0] at h6
    simp at h6
    rw [h6] at eq
    apply h
    linarith
    -- use abslut value of h6
    have habs: |d|=|p m * (k - 1)| := by rw [h6]
    rw [abs_mul] at habs
    -- prove |k-1| >= 1
    have :k-1 ≠ 0:= by by_contra ha;apply hk0;linarith
    have hk1:= Int.one_le_abs (this)
    -- prove |d| < |p m|
    have h7: |d| < |p m| := by
      -- use p m  > 0
      have h8:0 < p m := by linarith
      norm_cast at hm
      -- prove pm = |p m|
      have h9:= Int.sign_mul_abs (p m)
      rw [← h9] at hm
      simp at hm
      -- use sign=1
      have hsign: (p m).sign = 1:= by apply Int.sign_eq_one_of_pos;linarith
      rw [hsign] at hm
      linarith

    -- prove contradiction
    have h8: |d| * 1  < |p m| * |k - 1| := by apply Int.mul_lt_mul;exact h7;exact hk1;decide;simp
    simp at h8
    -- use habs to rewrite
    rw [habs] at h8
    linarith
