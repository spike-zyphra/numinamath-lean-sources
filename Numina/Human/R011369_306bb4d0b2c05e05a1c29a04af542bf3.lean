import Mathlib


/- 20. (USS 3) ${ }^{\text {IMO6 }}$ Let $f(x)=x^{2}+x+p, p \in \mathbb{N}$. Prove that if the numbers $f(0), f(1), \ldots, f([\sqrt{p / 3}])$ are primes, then all the numbers $f(0), f(1), \ldots$, $f(p-2)$ are primes. -/
theorem number_theory_24081 (p : ℕ) (hp : p ≠ 0) {f : ℕ → ℕ} (hf : ∀ x, f x = x ^ 2 + x + p)
     (h : ∀ i ∈ Finset.Icc 0 ⌊Real.sqrt (p / 3)⌋₊, Nat.Prime (f i)) :
    ∀ i ∈ Finset.Icc 0 (p - 2), Nat.Prime (f i) := by

  -- suppose on the contrary, denote y the smallest one does not satisfy the condition.
  -- denote q the minimum prime factor of y.
  simp only [Finset.mem_Icc, zero_le, true_and]
  intro y yle
  by_contra! not_prime_fy
  induction' y using Nat.strong_induction_on with y ih
  let q := (f y).minFac

  -- easy to exclude y=0 case.
  by_cases hy0: y = 0
  · apply not_prime_fy (h y ?_)
    simp [hy0]
  have ypos: 0 < y := by omega

  -- y ≤ p-2, y ≠ 0, so p ≥ 3
  have pge: p ≥ 3 := by
    have: y ≥ 1 := by omega
    omega

  -- therefore we may consider y ≥ 2, q > 1 case.
  have qgt: q > 1 := by
    refine Nat.Prime.one_lt ?_
    refine Nat.minFac_prime ?_
    apply ne_of_gt ?_
    rw [hf]
    apply Nat.lt_add_left _ (by omega)

  -- we claim y < q.
  have hq1: y < q := by
    by_contra! qle
    let r := y-q
    -- q ≤ y ≤ p-2 < f(r)
    have h1: q < f r := by
      have: q ≤ p - 2 := qle.trans yle
      refine lt_of_le_of_lt this ?_
      rw [hf r]
      refine Nat.lt_add_left _ ?_
      simp [Nat.zero_lt_of_ne_zero hp]
    -- then we obtain q divide f(r), contradiction to minimality of y.
    have h2: q ∣ f r := by
      have hh1: q ∣ f y := Nat.minFac_dvd (f y)
      have hh2: y = (q + r) := by omega
      have hh3: f y = q * (q+2*r+1) + f r := by
        rw [hf y, hf r, hh2]
        ring
      rw [hh3] at hh1
      refine (Nat.dvd_add_iff_right ?_).mpr hh1
      apply Nat.dvd_mul_right
    have h3: ¬ Nat.Prime (f r) := by
      by_contra!
      rw [this.dvd_iff_eq qgt.ne'] at h2
      simp [h2] at h1
    apply ih r ?_ ?_ h3
    <;> omega

  -- next, we prove q > 2y
  have hq2: q > 2*y := by
    by_contra! qle
    -- q > y, then q ≥ y+1
    let r := q - y - 1
    have req: q = y+r+1 := by omega
    have hr1: r < q := by omega
    have hr2: r < y := by omega
    -- again, we can prove this r contradicts minimality of y.
    refine ih r hr2 (by omega) ?_
    by_contra! h1
    -- we find q divide f(r)
    have h2: q ∣ f r := by
      have: ∀x, x ≤ y → f y = (y-x) * (y+x+1) + f x := by
        intro x hx
        zify
        rw [Nat.cast_sub hx]
        rw [hf y, hf x]
        push_cast
        ring
      specialize this r hr2.le
      rw [← req] at this
      have hh: q ∣ f y := (Nat.minFac_dvd (f y))
      rw [this] at hh
      refine (Nat.dvd_add_iff_right ?_).mpr hh
      apply Nat.dvd_mul_left
    rw [h1.dvd_iff_eq qgt.ne'] at h2
    have h3: f r > q := by
      rw [req, hf r, add_assoc (r^2) _ _]
      suffices (r+p) > y+r+1 by
        exact Nat.lt_add_left (r ^ 2) this
      replace yle: y < p-1 := by
        omega
      omega
    simp [h2] at h3
  replace hq2: q ≥ 2*y+1 := by exact hq2

  -- therefore f(y) ≥ q^2 ≥ (2y+1)^2
  have hy: f y ≥ (2*y+1)^2 := by
    have h1: f y ≥ q^2 := by
      apply Nat.minFac_sq_le_self ?_ not_prime_fy
      simp [hf, ypos]
    have h2: q^2 ≥ (2*y+1)^2 := by
      rwa [ge_iff_le, Nat.pow_le_pow_iff_left (by norm_num)]
    exact h2.trans h1

  -- then 3(y^2+y) ≤ p-1, y < √(p/3), contradiction
  replace hy: 3 * (y^2+y) ≤ p - 1 := by
    zify at hy ⊢
    rw [Nat.cast_sub (by omega)]
    rw [hf] at hy
    push_cast at hy ⊢
    linarith only [hy]
  replace hy: y ≤ ⌊√(p/3)⌋₊ := by
    apply Nat.le_floor
    rw [Real.le_sqrt (by positivity) (by positivity)]
    replace hy: 3 * (y^2 + 1) ≤ p - 1 := by
      apply le_trans ?_ hy
      refine Nat.mul_le_mul_left 3 ?_
      simpa only [add_le_add_iff_left] using ypos
    replace hy: 3*y^2 ≤ p := by
      have: p-1 ≤ p := by simp
      apply le_trans (le_trans ?_ hy) this
      simp
    rify at hy
    linarith only [hy]
  absurd not_prime_fy
  apply h y ?_
  simp only [Nat.cast_nonneg, Finset.mem_Icc, zero_le, true_and, hy]