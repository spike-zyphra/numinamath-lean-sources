import Mathlib


/-- For each positive integer $n$, let $f(n) = n^4 - 360n^2 + 400$.
    What is the sum of all values of $f(n)$ that are prime numbers?
    (A) 794 (B) 796 (C) 798 (D) 800 (E) 802 -/    
theorem algebra_93744 {f : ℤ → ℤ} (hf : ∀ n > 0, f n = n^4-360*n^2+400):
    ∑' n : {n | f n > 0 ∧ n > 0 ∧ Prime (f n)}, f n = 802 := by
  -- We can guess the factorization $f(n) = (n^2-20n+20)(n^2+20n+20)$.
  have hf2 : ∀ n > 0 , f n = (n^2 - 20 * n + 20)*(n^2 + 20 * n + 20) := by
    intro n gt
    rw[hf n gt]
    ring
  -- Note that the latter term is always positive for positive n.
  have hpos : ∀ n > 0, 0 < f n ↔ 0 < n^2 - 20 * n + 20 := by
    intro n hn
    rw[hf2 n hn]
    rw[mul_pos_iff_of_pos_right (by positivity)]
  -- So let us investigate when f(n) can be prime.
  have hone : ∀ n > 0, 0 < f n → Prime (f n) → n^2 - 20 * n + 20 = 1 := by
    intro n hn hfn hprime
    rw[hf2 n hn, prime_mul_iff, Int.isUnit_iff, Int.isUnit_iff] at hprime
    -- That can only occur when $n^2+20n+20 = \pm 1$, $n^2-20n+20$ is prime,
    rcases hprime with ⟨_,(h|h)⟩|⟨(h|h), _⟩
    -- where the first equation clearly cannot hold for positive n,
    · have : 20 < n^2 + 20 * n + 20 := by
        change 0 + 20 < n^2 + 20 * n + 20
        apply add_lt_add_right
        positivity
      rw[h] at this
      contradiction
    · have : 0 < n^2 + 20 * n + 20 := by positivity
      rw[h] at this
      contradiction
    -- or $n^2+20n+20$ is prime and $n^2-20n+20 = \pm 1$.
    · exact h
    -- The -1 case is also impossible: Since for $n \ge 20$, $n^2-20n+20$ is
    -- positive, it suffices to check n=1,...,19. By manual calculations we can see
    -- that $n^2-20n+20$ is never -1 for these $n$ either.
    · have : n < 20 := by
        by_contra! hn'
        have : 0 < n^2 - 20 * n + 20 := by
          have : 20 * n ≤ n^2 := by rw[sq]; apply mul_le_mul_of_nonneg_right hn' hn.le
          linarith
        rw[h] at this
        contradiction
      interval_cases n <;> norm_num at h
  -- Hence $n^2+20n+20$ is prime and $n^2-20n+20 = 1$.
  have hfactors : ∀ n > 0, 0 < f n → Prime (f n) → n = 1 ∨ n = 19 := by
    intro n hn hfn hprime
    have := hone n hn hfn hprime
    -- But the latter equation simplifies to $(n-1)(n-19) = 0$.
    have : n^2 - 20 * n + 19 = 0 := by linarith
    have : (n - 1) * (n - 19) = 0 := by rw[← this]; ring
    simpa only [mul_eq_zero, sub_eq_zero] using this
  -- So n=1 or n=19. Indeed, f(1) = 41 and f(19) = 761 are prime.
  have : {n | f n > 0 ∧ n > 0 ∧ Prime (f n)} = {1,19} := by
    ext n
    constructor
    · intro ⟨hfn,hn,hprime⟩
      apply hfactors n hn hfn hprime
    · rintro (rfl|rfl)
      · simp only [gt_iff_lt, Set.mem_setOf_eq, zero_lt_one, hf2, one_pow, mul_one, Int.reduceSub,
        Int.reduceAdd, one_mul, Nat.ofNat_pos, true_and]
        norm_num
      · simp[hf2]
        norm_num
  -- Therefore the sum over these f(n) equals 802.
  rw[this, ← Finset.coe_pair]
  simp only [Finset.coe_sort_coe, Finset.tsum_subtype, Finset.mem_singleton, OfNat.one_ne_ofNat,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
  rw[hf2 1 (by norm_num), hf2 19 (by norm_num)]
  norm_num