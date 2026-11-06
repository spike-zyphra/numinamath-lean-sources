import Mathlib


/- Let $K$ be a positive integer. Consider the sequence of integers $\{f(n)\}_{n=1}^{\infty}$ defined by:
- $f(1)=1$.
- If $n$ is an even natural number, $f(n)=f(n / 2)$.
- If $n>1$ is an odd natural number and $f(n-1)$ is an odd integer, then $f(n)=f(n-1)-1$.
- If $n>1$ is an odd natural number and $f(n-1)$ is an even integer, then $f(n)=f(n-1)+1$.

Theorem: The value of $f\left(2^{K}-1\right)$ is $1$ if $K$ is odd, and $0$ if $K$ is even. -/
theorem number_theory_637257 (K : ℕ) (hK : K > 0) (f : ℕ → ℕ)
    (hf1 : f 1 = 1)
    (hfeven : ∀ n ≥ 2, Even n → f n = f (n / 2))
    (hfodd1 : ∀ n ≥ 2, Odd n → Odd (f (n - 1)) → f n = f (n - 1) - 1)
    (hfodd2 : ∀ n ≥ 2, Odd n → Even (f (n - 1)) → f n = f (n - 1) + 1) :
    (Odd K → f (2 ^ K - 1) = 1) ∧ (Even K → f (2 ^ K - 1) = 0) := by


  -- induction on K.
  induction' K,hK using Nat.le_induction with K hk ih
  · simp [hf1]
  · -- obviously, 2^(k+1) - 1 is odd and ≥ 2.
    have h1: 2^(K+1) - 1 ≥ 2 := by
      suffices 2^(K+1) ≥ 2^2 by omega
      apply Nat.pow_le_pow_right (by norm_num) (by simp [hk])
    have h2: Odd (2^(K+1) - 1) := by
      have: Even (2^(K+1)) := by
        refine Even.pow_of_ne_zero ?_ (by omega)
        exact Nat.even_iff.mpr rfl
      refine Nat.Even.sub_odd Nat.one_le_two_pow this ?_
      exact Nat.odd_iff.mpr rfl
    -- 2^(K+1) - 2 is even, and f (2^(K+1)-2) = f (2^K-1)
    have h3: Even (2^(K+1) - 1 - 1) := by
      refine Odd.tsub_odd h2 ?_
      exact Nat.odd_iff.mpr rfl
    have h4: f (2^(K+1)-1-1) = f (2^K - 1) := by
      have: 2^(K+1)-1-1 ≥ 2 := by
        suffices 2^(K+1) ≥ 2^2 by omega
        apply Nat.pow_le_pow_right (by norm_num) (by simp [hk])
      rw [hfeven (2^(K+1)-1-1) this h3]
      congr 1
      omega
    -- consider parity of K, and use inductive hypothesis.
    by_cases hK: Odd K
    · simp only [hK, forall_const, isEmpty_Prop, Nat.not_even_iff_odd,
      IsEmpty.forall_iff, and_true] at ih
      rw [ih] at h4
      have: Odd (f (2^(K+1)-1-1)) := by
        rw [h4]
        exact Nat.odd_iff.mpr rfl
      simp [hK, hfodd1 _ h1 h2 this, h4]
    · rw [Nat.not_odd_iff_even] at hK
      simp only [isEmpty_Prop, Nat.not_odd_iff_even, hK,
      IsEmpty.forall_iff, forall_const, true_and] at ih
      rw [ih] at h4
      have: Even (f (2^(K+1)-1-1)) := by
        rw [h4]
        exact Nat.even_iff.mpr rfl
      simp [hK, hfodd2 _ h1 h2 this, h4]