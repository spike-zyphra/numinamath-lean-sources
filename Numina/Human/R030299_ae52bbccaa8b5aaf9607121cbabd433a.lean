import Mathlib

/- 15. N1 (ROM) Let $k$ be a positive integer. Prove that there are infinitely many perfect squares of the form $n 2^{k}-7$, where $n$ is a positive integer.-/
theorem number_theory_24603 {k : ℕ} (hk : 0 < k) : Set.Infinite {m : ℤ | IsSquare m ∧ ∃ n : ℕ, 0 < n ∧ m = n * 2 ^ k - 7} := by
  -- lemma to simplify $(k+k)/2$.
  have add_self_div_two (k : ℕ) : (k + k) / 2 = k := by
    rw [← two_mul, mul_div_cancel_left₀ _ (by norm_num)]
  -- Given any positive integer k, there exists $a_k$ such that $a_k^2$ has the form $n*2^k-7$.
  have ⟨m, n, hnpos, hmpos, _, hmn⟩ : ∃ m : ℤ, ∃ n : ℕ, 0 < n ∧ 0 < m ∧ Odd m ∧ m ^ 2 = n * 2 ^ k - 7 := by
    change 1 ≤ k at hk
    -- 15. We show by induction on $k$ that there exists a positive integer $a_{k}$
    -- for which $a_{k}^{2} \equiv-7\left(\bmod 2^{k}\right)$.
    induction' k, hk using Nat.le_induction with k hk ih
    . -- base case : k = 1
      use 1, 4
      norm_num
    rcases le_or_lt k 2
    . interval_cases k
      . -- small case : k = 1 inside $2^(k+1)$
        use 1, 2
        norm_num
      -- small case : k = 2 inside $2^(k+1)$
      use 1, 1
      norm_num
    -- Now suppose that $a_{k}^{2} \equiv-7$ $\left(\bmod 2^{k}\right)$ for some $k>3$.
    -- Then either $a_{k}^{2} \equiv-7\left(\bmod 2^{k+1}\right)$
    -- or $a_{k}^{2} \equiv 2^{k}-7$ $\left(\bmod 2^{k+1}\right)$.
    rcases ih with ⟨m, n, hn, hm, hmodd, hmn⟩
    rcases Nat.even_or_odd n with hneven | hnodd
    . -- In the former case, take $a_{k+1}=a_{k}$.
      use m, n / 2
      rcases hneven with ⟨n', hn'⟩
      constructor
      . omega
      refine ⟨hm, hmodd, ?_⟩
      convert hmn using 1
      rw [hn', add_self_div_two]
      congr 1
      rw [pow_succ]
      push_cast
      ring
    -- In the latter case, set $a_{k+1}=a_{k}+2^{k-1}$.
    use m + 2 ^ (k - 1)
    -- Then $a_{k+1}^{2}=a_{k}^{2}+2^{k} a_{k}+2^{2 k-2} \equiv
    -- a_{k}^{2}+2^{k} \equiv-7(\bmod$ $2^{k+1}$ ) because $a_{k}$ is odd.
    have ⟨p, hp⟩ : Even (n + m + 2 ^ (k - 2)) := by
      rcases hnodd with ⟨n', hn'⟩
      rcases hmodd with ⟨m', hm'⟩
      use n' + m' + 1 + 2 ^ (k - 3)
      rw [hn', hm', show k - 2 = k - 3 + 1 by omega]
      push_cast
      ring
    have hppos : 0 < p := by
      suffices 0 < p + p by linarith
      rw [← hp]
      positivity
    let p' := p.natAbs
    use p'
    constructor
    . omega
    constructor
    . positivity
    constructor
    . apply Even.odd_add
      . use 2 ^ (k - 2)
        rw [show k - 1 = k - 2 + 1 by omega, pow_succ]
        ring
      exact hmodd
    ring_nf
    rw [mul_assoc, ← pow_succ, show k - 1 + 1 = k by omega, hmn,
      show (k - 1) * 2 = k + (k - 2) by omega, pow_add, mul_assoc, mul_comm _ 2,
      ← mul_assoc, mul_comm _ 2]
    have : 2 * (p' : ℤ) = p + p := by
      rw [← two_mul]
      congr
      simp [p']
      omega
    rw [this, ← hp]
    ring
  -- The statement of the problem follows,
  -- since every $a_{k}+r 2^{k}(r=0,1, \ldots)$ also satisfies this condition.
  set f : ℕ → ℤ := fun i => (m + i * 2 ^ k) ^ 2 with hf
  apply Set.infinite_of_injective_forall_mem (f := f)
  . -- It's clear that `f` is injective.
    intro i j hij
    simp [hf] at hij
    rw [sq_eq_sq₀ (by positivity) (by positivity)] at hij
    simp at hij
    exact hij
  -- Every number in `f` satisfies requirement.
  intro i
  simp [hf]
  refine ⟨IsSquare.sq _, ?_⟩
  -- Suffices to show that `2^k` divides `f(i)+7`.
  suffices 2 ^ k ∣ (m + i * 2 ^ k) ^ 2 + 7 by
    rcases this with ⟨u, hu⟩
    lift u to ℕ using by nlinarith
    use u
    refine ⟨by nlinarith, ?_⟩
    linear_combination hu
  -- It'c clear that `2^k` divides `(m+i2^k)^2+7` since `2^k` divides `m^2+7`.
  rw [← Int.modEq_zero_iff_dvd]
  have : m ^ 2 + 7 ≡ 0 [ZMOD 2 ^ k] := by rw [Int.modEq_zero_iff_dvd]; use n; linear_combination hmn
  refine Int.ModEq.trans ?_ this
  gcongr
  nth_rw 2 [← add_zero m]
  gcongr
  rw [← mul_zero (i : ℤ)]
  gcongr
  rw [Int.ModEq, Int.emod_self, eq_comm]
  rfl
