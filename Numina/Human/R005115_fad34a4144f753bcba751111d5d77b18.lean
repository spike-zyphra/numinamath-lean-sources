import Mathlib

/- Trouver tous les quadruplets (p,q,r,n) d'entiers strictement positifs vérifiant les trois conditions suivantes:
p et q sont premiers,
p+q n'est pas divisible par 3, p+q = r (p-q)^n -/
theorem number_theory_605607 {p q r n: PNat}:
  (Nat.Prime p ∧ Nat.Prime q ∧ ¬ 3 ∣ (p+q:ℕ) ∧
    p+q = r * (p-q:ℤ)^(n:ℕ)) ↔
  ( (p=2 ∧ q=3 ∧ r=5 ∧ Even (n:ℕ)) ∨  (p=3 ∧ q=2 ∧ r=5) ∨
    (p=3 ∧ q=5 ∧ r=2 ∧ n=2) ∨ (p=5 ∧ q=3 ∧
      ((r=1 ∧ n=3) ∨ (r=2 ∧ n=2) ∨ (r=4 ∧ n=1)))  ) := by

  constructor
  · rintro ⟨pp, pq, not_3_dvd, heq⟩
    -- p ≠ q, otherwise p+q is 0
    have pneq: p ≠ q := by
      rintro rfl
      simp at heq
    have pneq': (p:ℕ) ≠ q := by
      norm_cast
    
    -- n ≥ 1, so p-q divide p+q
    have hdvd: (p-q:ℤ) ∣ p+q := by
      have: (p-q:ℤ)^(n:ℕ) ∣ (p+q) := by
        rw [heq]
        apply Int.dvd_mul_left
      apply Int.dvd_trans ?_ this
      exact dvd_pow (by simp) (by simp)
    
    -- p-q divide p-q + p+q = 2p, therefore p-q divide 2
    have hdvd': p-(q:ℤ) ∣ 2 := by
      have h1: (p:ℤ) - q ∣ 2*p := by
        have: (p:ℤ)-q + (p+q) = 2*p := by ring
        rw [← this]
        exact dvd_add_self_left.mpr hdvd
      -- similarly, p-q divide 2q.
      have h2: (p:ℤ) - q ∣ 2*q := by
        have: -((p:ℤ)-q) + (p+q) = 2*q := by ring
        rw [← this]
        apply Int.dvd_add ?_ hdvd
        apply dvd_neg.mpr dvd_rfl
      have h3: (p:ℤ) - q ∣ Int.gcd (2*p) (2*q) := by
        exact Int.dvd_gcd h1 h2
      have h4: Int.gcd (2*p) (2*q) = 2 := by
        rw [Int.gcd_mul_left]
        simp only [Int.reduceAbs, Int.gcd_natCast_natCast, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀,
        PNat.coprime_coe]
        refine PNat.coprime_coe.mp ?_
        exact (Nat.coprime_primes pp pq).mpr pneq'
      rwa [h4] at h3
    
    -- we claim impossible for p,q both ≠ 3.
    have: p=3 ∨ q=3 := by
      by_contra!
      rcases this with ⟨pne3, qne3⟩
      -- consider p and q modulo 3
      -- p,q mod 3 is 1 or 2, cannot be 0.
      have {x: ℕ} (hx: Nat.Prime x) (xne: x ≠ 3):
        x ≡ 1 [MOD 3] ∨ x ≡ 2 [MOD 3] := by
        -- x mod 3 is 0,1,2.
        mod_cases h: x % 3
        · have h1: 3 ∣ x := by
            exact Nat.dvd_of_mod_eq_zero h
          have h2: x = 3 := by
            rwa [← Nat.Prime.dvd_iff_eq hx (by norm_num)]
          simp [h2] at xne
        · left; exact h
        · right; exact h
      
      -- we claim p,q mod 3 both eq 1 or eq 2.
      have h1: (p ≡ 1 [MOD 3] ∧ q ≡ 1 [MOD 3]) ∨
        (p ≡ 2 [MOD 3] ∧ q ≡ 2 [MOD 3]) := by
        -- impossible for p mod3 1, q mod3 2; or p mod3 2, q mod3 1
        have mod_eq_zero (h: (p ≡ 1 [MOD 3] ∧ q ≡ 2 [MOD 3]) ∨
          (p ≡ 2 [MOD 3] ∧ q ≡ 1 [MOD 3])): p+q ≡ 0 [MOD 3] := by
          rcases h with  h | h
          all_goals
            replace h := Nat.ModEq.add h.left h.right
            exact h
        rcases (this pp (by norm_cast)) with (p1 | p2)
        · -- suppose p mod 3 is 1.
          left
          rcases (this pq (by norm_cast)) with (q1 | q2)
          · exact ⟨p1, q1⟩
          · absurd not_3_dvd
            refine Nat.dvd_of_mod_eq_zero (mod_eq_zero ?_)
            simp [p1, q2]
        · -- suppose p mod 3 is 2.
          right
          rcases (this pq (by norm_cast)) with (q1 | q2)
          · absurd not_3_dvd
            refine Nat.dvd_of_mod_eq_zero (mod_eq_zero ?_)
            simp [p2, q1]
          · exact ⟨p2, q2⟩
      replace h1: (p ≡ 1 [ZMOD 3] ∧ q ≡ 1 [ZMOD 3]) ∨
        (p ≡ 2 [ZMOD 3] ∧ q ≡ 2 [ZMOD 3]) := by
        have cast_to_zmod {x : PNat} {y: ℕ}
          (h: x ≡ y [MOD 3]): x ≡ y [ZMOD 3] := by
          refine Int.modEq_iff_dvd.mpr ?_
          exact Nat.modEq_iff_dvd.mp h
        rcases h1 with h1 | h1
        <;> rcases h1 with ⟨hp , hq⟩
        · left; constructor <;> apply cast_to_zmod (by assumption)
        · right; constructor <;> apply cast_to_zmod (by assumption)
      
      -- but either case, 3 divide p-q, therefore divide p+q
      rcases h1 with h1 | h1
      all_goals
        replace h1: p ≡ q [ZMOD 3] :=
          Int.ModEq.trans h1.left h1.right.symm
        absurd not_3_dvd
        zify
        apply Dvd.dvd.trans ?_ hdvd
        exact Int.ModEq.dvd h1.symm

    -- p=3 or q=3, p-q divide 2, thus we have four cases:
    replace: (p=2 ∧ q=3) ∨ (p=3 ∧ q=2) ∨ (p=3 ∧ q=5) ∨ (p=5 ∧ q=3) := by
      have h1: (p:ℤ) - q ≤ 2 := by
        apply Int.le_of_dvd (by norm_num) hdvd'
      have h2: (p:ℤ) - q ≥ -2 := by
        have: - (p-q:ℤ) ∣ 2 := by
          exact Int.neg_dvd.mpr hdvd'
        replace := Int.le_of_dvd (by norm_num) this
        linarith only [this]
      have h3 {x: PNat} (hx: x ≤ 5): x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
        have h31: (x:ℕ) ≤ 5 := by exact hx
        have h32: (x:ℕ) = 1 ∨ x = (2:ℕ) ∨ x = (3:ℕ) ∨ x = (4:ℕ) ∨ x = (5:ℕ) := by
          clear * - h31
          have h32: 0 < (x:ℕ) := by exact PNat.pos x
          interval_cases (x:ℕ)
          all_goals simp
        norm_cast at h32
      rcases this with (rfl | rfl)
      · norm_num at h2
        rcases (h3 h2) with (rfl | rfl | rfl | rfl | rfl)
        all_goals norm_cast at hdvd
      · norm_num at h1
        rcases (h3 h1) with (rfl | rfl | rfl | rfl | rfl)
        all_goals norm_cast at hdvd

    -- (p-q)^n > 0, since p+q and r both > 0
    have hpos: 0 < (p-q:ℤ)^(n:ℕ) := by
      have: (r:ℤ) * (p-q)^(n:ℕ) > 0 := by
        rw [← heq]
        apply add_pos (by simp) (by simp)
      apply (pos_iff_pos_of_mul_pos this).mp (by simp)
    -- also, (p-q)^n ≤ (p+q)
    have hle: (p-q: ℤ)^(n:ℕ) ≤ p+q := by
      apply Int.le_of_dvd (by simp [add_pos])
      rw [heq]
      apply Int.dvd_mul_left
    rcases this with (hpq | hpq | hpq | hpq)
    all_goals rcases hpq with ⟨rfl, rfl⟩

    · -- 5 = r (-1)^n, then r = 5 and n = 1
      norm_num at heq hpos ⊢
      replace h1: Even (n:ℕ) := by
        by_contra!
        have: (-1)^(n:ℕ) = -1 := by
          refine Odd.neg_one_pow ?_
          exact Nat.not_even_iff_odd.mp this
        simp [this] at hpos
      simp only [Int.reduceNeg, h1, Even.neg_pow,
      one_pow, mul_one] at heq
      norm_cast at heq
      exact ⟨heq.symm, h1⟩

    · -- 5 = r
      norm_num at heq
      norm_cast at heq
      right; left
      simp [heq]

    · -- 8 = r (-2)^n
      norm_num at heq hpos hle ⊢
      -- (-2)^n ≤ 8, then n ≤ 3
      have nle: n ≤ (3:ℕ) := by
        have h1: (-2:ℤ)^(n:ℕ) = 2^(n:ℕ) := by
          refine Even.neg_pow ?_ 2
          by_contra!
          rw [Nat.not_even_iff_odd] at this
          absurd hpos
          push_neg; apply le_of_lt
          apply Odd.pow_neg this (by norm_num)
        have h2: (2:ℤ)^(n:ℕ) ≤ 2^3 := by
          rw [← h1]
          norm_num
          exact hle
        rwa [pow_le_pow_iff_right₀ (by norm_num)] at h2
      have neq: (n:ℕ) = 2 := by
        have nge: (n:ℕ) ≥ 1 := by exact NeZero.one_le
        interval_cases (n:ℕ)
        any_goals simp at hpos
        rfl
      simp only [Int.reduceNeg, neq, even_two,
      Even.neg_pow, Int.reducePow] at heq
      have req: r = (2:ℤ) := by linarith only [heq]
      norm_cast at neq req

    · -- 8 = r 2^n
      norm_num at heq ⊢
      have nle: n ≤ (3:ℕ) := by
        have: (2:ℤ)^(n:ℕ) ≤ 2^3 := by
          norm_num
          apply Int.le_of_dvd (by norm_num) ?_
          rw [heq]
          apply Int.dvd_mul_left
        rwa [pow_le_pow_iff_right₀ (by norm_num)] at this
      have nge: (n:ℕ) ≥ 1 := by exact NeZero.one_le
      have neq: n = (1:ℕ) ∨ n = (2:ℕ) ∨ n = (3:ℕ) := by
        interval_cases (n:ℕ)
        all_goals simp
      have req: (r:ℤ) = 8 / 2^(n:ℕ) := by
        rw [heq]
        refine Eq.symm (Int.mul_ediv_cancel ↑↑r ?_)
        simp
      rcases neq with hn | hn | hn
      all_goals
        norm_num [hn] at req
        norm_cast at hn req
        simp [hn, req]

  · -- verification
    rintro (hpq | hpq | hpq | hpq)
    · rcases hpq with ⟨rfl, rfl, rfl, hn⟩
      norm_num
      simp [hn]
    · rcases hpq with ⟨rfl, rfl, rfl⟩
      norm_num
    · rcases hpq with ⟨rfl, rfl, rfl, rfl⟩
      norm_num
    · rcases hpq with ⟨rfl, rfl, ( h | h | h ) ⟩
      all_goals
        rcases h with ⟨rfl, rfl⟩
        norm_num