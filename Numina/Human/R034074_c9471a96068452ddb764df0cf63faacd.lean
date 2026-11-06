import Mathlib


/- Trouver toutes les fonctions $\mathrm{f}: \mathbb{N} \rightarrow \mathbb{N}$ telles que $2 m n+m f(m)+n f(n)$ est un carré parfait pour tous entiers positifs $m$ et $n$. -/
theorem number_theory_607523 (f : ℕ → ℕ) :
    (∀ m n : ℕ, 0 < m → ∃ k : ℕ, k^2 = 2 * m * n + m * f m + n * f n) ↔
    ∀ k : ℕ, 0 < k → f k = k := by
  
  -- to simplify, let's suppose F(m,n) = 2mn + mf(m) + nf(n)
  set F : ℕ → ℕ → ℕ := fun m n => 2*m*n + m * f m + n * f n with F_def

  -- set n=0, F(m,0) = mf(m)
  have Fm0 (m:ℕ): F m 0 = m * f m := by
    simp [F_def]

  -- if pn is perfect square and p is prime, then exist a, n = pa^2.
  have ex_of_pn_sq {p n: ℕ} (pp: Nat.Prime p) (h: ∃ k:ℕ, k^2 = p*n):
    ∃ a:ℕ, n = p*a^2 := by
    rcases h with ⟨k,hk⟩
    have: p ∣ k^2 := by
      rw [hk]
      apply Nat.dvd_mul_right
    replace: p ∣ k := pp.dvd_of_dvd_pow this
    rcases this with ⟨a, rfl⟩
    have: (p*a)^2 = p * (p*a^2) := by ring
    simp only [this, mul_eq_mul_left_iff, pp.ne_zero, or_false] at hk
    use a
    rw [hk]

  -- we claim if F (p,0) and F(p,1) are perfect square for enough large prime p,
  -- then f(p) = p.
  have hfp {p:ℕ} (pp: Nat.Prime p) (h1: ∃ k:ℕ, k^2 = F p 0)
    (h2: ∃ k:ℕ, k^2 = F p 1)(hp: p > f 1 - (1:ℤ))
    (fpnz: f p ≠ 0):
    f p = p := by
    rw [Fm0 p] at h1
    replace h1 := ex_of_pn_sq pp h1
    rcases h1 with ⟨a,ha⟩
    -- F p 1 = 2p + pf(p) + 1f(1) = 2p + (ap)^2 + f(1)
    have h3: F p 1 = (a*p)^2 + 2*p + f 1 := by
      simp only [F_def, ha]
      ring
    -- obviously, F p 1 > (ap)^2
    have h4: F p 1 > (a*p)^2 := by
      rw [h3, add_assoc]
      simp [pp.pos]
    -- then F p 1 ≥ (ap)^2, since it's perfect square.
    replace h4: F p 1 ≥ (a*p+1)^2 := by
      rcases h2 with ⟨k,hk⟩
      rw [← hk] at h4 ⊢
      replace h4: k > (a*p) := by
        apply (Nat.pow_lt_pow_iff_left (by norm_num)).mp h4
      replace h4: k ≥ a*p+1 := by exact h4
      apply (Nat.pow_le_pow_iff_left (by norm_num)).mpr h4
    -- (ap)^2 + 2p + f1 ≥ (ap+1)^2, simplify,
    -- 2p + f1 ≥ 2ap + 1, (f1-1) ≥ 2p(a-1)
    rw [h3] at h4
    replace h4: 2*(a-1) * p ≤ f 1 - (1:ℤ) := by
      zify at h4
      linarith only [h4]
    -- f1 - 1 is constant, but p can be arbitrarily large.
    -- so coefficient a-1 must be 0, or, a=1, f(p) = p.
    have h5: a < 2 := by
      by_contra! age
      have: 2*(a-1)*(p:ℤ) ≥ p := by
        apply (le_mul_iff_one_le_left (by simp [pp.pos])).mpr ?_
        zify at age
        linarith only [age]
      replace := this.trans h4
      linarith only [this, hp]
    -- a < 2, and easy to prove a ≠ 0, then a = 1.
    replace h5: a = 1 := by
      have: a ≠ 0 := by
        rintro rfl
        simp [ha] at fpnz
      clear * - h5 this
      omega
    -- therefore f(p) = p
    simp [ha, h5]

  constructor

  · intro h

    replace h: ∀ (m n:ℕ), 0 < m → ∃ k, k^2 = F m n := by
      simp only [F_def]
      exact h

    -- given F m n perfect square, we can exclude f(p) = 0 case for prime p.
    -- otherwise 2p^2 is perfect square, contradiction.

    -- a^2 ≠ 2 for any natural number a.
    have not_sq_2 {a:ℕ}: a^2 ≠ 2 := by
      rintro ha
      have h1: 1 < a := by
        have: 1^2 < a^2 := by
          rw [ha]
          norm_num
        apply (Nat.pow_lt_pow_iff_left (by norm_num)).mp this
      have h2: a < 2 := by
        have: a^2 < 2^2 := by
          rw [ha]
          norm_num
        apply (Nat.pow_lt_pow_iff_left (by norm_num)).mp this
      omega

    -- if we suppose f(p) = 0, then we can reach a contradiction.
    have fnz {p:ℕ} (pp: Nat.Prime p): f p ≠ 0 := by
      -- otherwise, F p 1 = f1 + 2p
      rintro h1
      have h2: F p p = 2*p^2 := by
        simp only [F_def, h1]
        ring
      rcases (h p p pp.pos) with ⟨k,hk⟩
      rw [h2] at hk
      have h3: p ∣ k := by
        have: p ∣ k^2 := by
          rw [hk, pow_two, ← mul_assoc]
          apply Nat.dvd_mul_left
        exact Nat.Prime.dvd_of_dvd_pow pp this
      rcases h3 with ⟨a,ha⟩
      rw [ha] at hk
      have: a^2 = 2 := by
        replace hk: a^2 * p^2 = 2 * p^2 := by
          linarith only [hk]
        simp only [mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff, pp.ne_zero, or_false] at hk
        exact hk
      absurd this
      apply not_sq_2

    -- Now we claim for enough large p, if f(p) = p, then f(k) = k.
    have feq {p k: ℕ} (pp: Nat.Prime p) (fpeq: f p = p) (hk: 0 < k)
      (hp1: p > k^2+1) (hp2: p > k * f k):
      f k = k := by
      have h1: F p k = p^2 + 2*k*p + k * f k := by
        simp only [F_def, fpeq]
        ring
      -- (p+k-1)^2 < F p k
      have h2: (p+k-1:ℤ)^2 < F p k := by
        have: (p+k-1:ℤ)^2 = p^2 + 2*k*p + (k^2+1-2*k-2*p) := by ring
        rw [this, h1]
        push_cast
        simp only [add_lt_add_iff_left, gt_iff_lt]
        replace: k^2+1 - 2*k-2*p < (0:ℤ) := by
          zify at hp1
          linarith only [hp1]
        apply lt_of_lt_of_le this ?_
        positivity
      -- F p k < (p+k+1)^2
      have h3: F p k < (p+k+1)^2 := by
        have: (p+k+1)^2 = p^2 + 2*k*p + p + (p + (k+1)^2) := by ring
        rw [this]
        replace: F p k < p^2 + 2*k*p + p := by
          rw [h1]
          linarith only [hp2]
        apply lt_trans this (by simp)
      -- then F p k = (p+k)^2
      have h4: F p k = (p+k)^2 := by
        specialize h p k pp.pos
        rcases h with ⟨a,ha⟩
        rw [← ha] at h2 h3 ⊢
        have ha1: p+k-1 < a := by
          zify
          rw [Nat.cast_sub (by linarith only [pp.one_le])]
          push_cast
          apply (pow_lt_pow_iff_left₀ ?_ (by simp) (by norm_num)).mp h2
          linarith only [pp.one_le]
        have ha2: a < p+k+1 := by
          apply (Nat.pow_lt_pow_iff_left (by norm_num)).mp h3
        have ha3: a = p+k := by
          clear * - ha1 ha2
          omega
        rw [ha3]
      -- then fk = k.
      rw [h4] at h1
      replace h1: k*k = k*f k := by
        linarith only [h1]
      exact Nat.eq_of_mul_eq_mul_left hk h1.symm

    -- now we claim f(k) = k holds for any k ≥ 1.
    -- since we can always find a large enough prime p.
    intro k kpos

    -- prime number is unbounded, so exist arbitrarily large p.
    obtain ⟨p, pp, hp1, hp2, hp3⟩:
      ∃ p, Nat.Prime p ∧ p > k^2+1 ∧ p > k * f k ∧ p > f 1 := by
      have: ∃ n, n > k^2+1 ∧ n > k * f k ∧ n > f 1 := by
        use (max (k^2+1) (max (k * f k) (f 1)))+1
        refine ⟨?_, ?_, ?_⟩
        all_goals
          refine Order.lt_add_one_iff.mpr ?_
          simp
      rcases this with ⟨n, hn⟩
      rcases (Nat.exists_infinite_primes n) with ⟨p, hp, pp⟩
      use p
      refine ⟨pp, ?_, ?_, ?_⟩
      all_goals
        apply lt_of_lt_of_le ?_ hp
        simp [hn]

    -- from calculations before, such p satisfy F p k = (p+k)^2, therefore f(k) = k.
    apply feq pp ?_ kpos hp1 hp2
    apply hfp pp ?_ ?_ ?_ (fnz pp)
    · apply h _ _ pp.pos
    · apply h _ _ pp.pos
    · zify at hp3
      linarith only [hp3]

  · -- verification
    intro hf
    intro m n mpos
    by_cases hn: n = 0
    · simp only [hn, mul_zero, hf m mpos,
      zero_add, zero_mul, add_zero, pow_two]
      use m
    · replace hn: 0 < n := Nat.zero_lt_of_ne_zero hn
      simp only [hf m mpos, hf n hn]
      use (m+n)
      ring