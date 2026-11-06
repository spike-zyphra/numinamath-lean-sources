import Mathlib

/- For each positive integer $p$, let $b(p)$ denote the unique positive integer $k$
such that $|k - \sqrt{p}| < \frac{1}{2}$. For example, $b(6) = 2$ and $b(23) = 5$.
If $S = \sum_{p = 1}^{2007} b(p)$, find the remainder when $S$ is divided by $1000$. -/
theorem number_theory_93361 {b : ℕ → ℕ}
    (hb : ∀ (p : ℕ), 0 < p → 0 < b p ∧ |b p - √p| < 1 / 2)
    (hbunique : ∀ (p : ℕ), 0 < p → ∀ (k : ℕ), 0 < k ∧ |k - √p| < 1 / 2 → b p = k) :
    (∑ p ∈ Finset.Icc 1 2007, b p) % 1000 = 955 := by

  -- First, we can characterize b: it has value k on intervals
  -- of the form (k - 1) * k < p ≤ k * (k + 1).
  let subrange k := Finset.Ioc ((k - 1) * k) (k * (k + 1))

  have hbsubrange {p k : ℕ} (hp: 0 < p) (hk : 0 < k) : b p = k ↔ p ∈ subrange k := by
    have : b p = k ↔ |k - √p| < 1 / 2 := by
      constructor
      . intro hbk
        rw [← hbk]
        exact (hb p hp).2
      . intro hk_sqrt
        exact hbunique p hp k ⟨hk, hk_sqrt⟩
    rw [this]
    have : (k - 1 : ℕ) = (k - 1 : ℝ) := by simp [hk]
    have h2 : (k - 1) * k < p ↔ k - √p < 1 / 2 := by
      rw [sub_lt_comm, Real.lt_sqrt (by linarith)]
      constructor
      . rw [← Nat.succ_le]
        rify [hk]
        intro h
        linarith
      . rify [hk]
        intro h
        linarith
    have h1 : p ≤ k * (k + 1) ↔ -(1 / 2) < k - √p := by
      rw [neg_lt_sub_iff_lt_add', Real.sqrt_lt' (by linarith)]
      constructor
      . rify
        intro h
        linarith
      . rw [← Nat.lt_succ]
        rify
        intro h
        linarith
    simp only [subrange, Finset.mem_Ioc]
    rw [abs_lt, and_comm, h1, h2]

  -- Each interval is of length 2k.
  have subrange_card {k} : (subrange k).card = 2 * k := by
    simp [subrange]
    move_mul [k]
    rw [← Nat.sub_mul]
    by_cases h : k = 0
    . simp [h]
    . rw [show k - 1 = (k + 1) - 2 by omega]
      rw [Nat.sub_sub_self (show 2 ≤ k + 1 by omega)]

  -- Note that if k = 44, k(k + 1) = 1980, so if k < 45 then all such p are in
  -- [1, 2007].
  have hpmax {p k} (hrange : p ∈ subrange k) : k < 45 ↔ p ≤ 1980 := by
    obtain ⟨hl, hr⟩ := by simp [subrange] at hrange; exact hrange
    constructor
    . intro h
      calc
        p ≤ k * (k + 1) := hr
        _ ≤ 44 * 45 := Nat.mul_le_mul (by omega) (by omega)
        _ = 1980 := by norm_num
    . intro h
      contrapose h
      simp
      calc
        1980 = 44 * 45 := by norm_num
        _ ≤ (k - 1) * k := Nat.mul_le_mul (by omega) (by omega)
        _ < p := hl

  -- So, let's handle these first and the remaining numbers later.
  have hsum1 : ∑ p ∈ Finset.Icc 1 1980, b p = 58740 := by
    -- We partition the summation domain into ranges of this form, where $b$ is constant on each partition.
    have hpartition : ∑ p ∈ Finset.Icc 1 1980, b p = ∑ ⟨k, p⟩ ∈ (Finset.range 45).sigma subrange, k := by
      refine Finset.sum_bij (fun p _ => ⟨b p, p⟩) ?_ ?_ ?_ ?_
      any_goals simp
      . intro p hp1 hp2
        have hp : 0 < p := by omega
        have hrange : p ∈ subrange (b p) := (hbsubrange hp (hb p hp).1).mp rfl
        and_intros
        . rw [hpmax hrange]
          exact hp2
        . exact hrange
      . rintro ⟨k, p⟩
        simp
        intro hk hrange
        obtain ⟨hl, hr⟩ := by simp [subrange] at hrange; exact hrange
        have hp : 0 < p := by omega
        have hkz : 0 < k := by_contradiction fun h => by
          have : k = 0 := by omega
          rw [this] at hr
          omega
        have : b p = k := (hbsubrange hp hkz).mpr hrange
        rw [← hpmax hrange]
        exact ⟨⟨by omega, hk⟩, this⟩

    -- Now we can compute the sum, where for the last step we could use the standard
    -- sum-of-squares formula n * (n + 1) * (2n + 1) / 6.
    calc
     ∑ p ∈ Finset.Icc 1 1980, b p = ∑ ⟨k, p⟩ ∈ Finset.sigma (Finset.range 45) subrange, k := hpartition
     _ = ∑ k ∈ Finset.range 45, ∑ p ∈ subrange k, k := Finset.sum_sigma _ _ _
     _ = ∑ k ∈ Finset.range 45, 2 * k ^ 2 := by simp_rw [Finset.sum_const, subrange_card]; simp; ring_nf
     _ = 2 * ∑ k ∈ Finset.range 45, k ^ 2 := Finset.sum_nsmul _ _ _
     _ = 2 * 29370 := by norm_num
     _ = 58740 := by norm_num

  -- Now we deal with the remaining numbers. These all have b(p) = 45.
  have hsum2 : ∑ p ∈ Finset.Icc 1981 2007, b p = 1215 := by
    have : ∀ p ∈ Finset.Icc 1981 2007, b p = 45 := by
      simp
      intro p hp1 hp2
      rw [hbsubrange (by omega) (by omega)]
      simp [subrange]
      omega
    rw [Finset.sum_const_nat this]
    simp

  -- Finally, we can combine the two sums to get the final answer.
  have hdomain_disjoint : Disjoint (Finset.Icc 1 1980) (Finset.Icc 1981 2007) := by
    rw [Finset.disjoint_left]
    intro n
    simp
    omega
  have : Finset.Icc 1 2007 = Finset.disjUnion (Finset.Icc 1 1980) (Finset.Icc 1981 2007) hdomain_disjoint := by
    ext n
    simp
    omega
  rw [this, Finset.sum_disjUnion hdomain_disjoint, hsum1, hsum2]
  simp