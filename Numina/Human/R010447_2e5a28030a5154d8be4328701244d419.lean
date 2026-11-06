import Mathlib

/- How many pairs of positive integers $(a,b)$ are there such that $\gcd(a,b)=1$ and \[ \frac{a}{b}+\frac{14b}{9a}
\]is an integer? -/
theorem number_theory_23093 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ Nat.gcd a b = 1 ∧ ∃ k : ℤ, (a / b : ℚ) + 14 * b / (9 * a) = k}.ncard = 4 := by
  -- if a/b + 14b/9a = k and denote u=a/b, then 9u^2-9uk+14=0
  have h1 (a b:ℕ)(ha: a > 0)(hb: b > 0)(k:ℤ): (a/b:ℚ)+14*b/(9*a) = k →
    9*(a/b:ℚ)^2-9*(a/b:ℚ)*k+14 = 0 := by
    intro h
    have aqnz: (a:ℚ) ≠ 0 := by exact Nat.cast_ne_zero.mpr ha.ne'
    have bqnz: (b:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    have hh1: (a/b:ℚ) - k + 14*b/(9*a) = 0 := by linarith [h]
    have hh2: 9*(a/b:ℚ) *  ((a/b:ℚ) - k + 14*b/(9*a)) =
      9*(a/b:ℚ)^2-9*(a/b:ℚ)*k+14 := by
      field_simp [aqnz, bqnz]; ring
    rw [← hh2, hh1]; simp
  -- solve 9u^2-9uk+14=0. for it to have rational root, discriminant must be perfect square.
  have h2(k:ℤ): (∃(u:ℚ),9*u^2-9*u*k+14 = 0) ↔ ∃s:ℚ, 9*k^2-56 = s^2:= by
    have hh1: (∃ u:ℚ, 9*u^2-9*u*k+14 = 0) ↔ (∃ u:ℚ, 9*u*u + (-9*k)*u + 14 = 0) := by
      constructor <;> intro h
      <;> rcases h with ⟨u,hu⟩ <;> rw [← hu] <;> use u <;> ring
    have hh3: discrim (9:ℚ) (-9*k) 14 = 3^2 * (9*k^2-56) := by
      rw [discrim]; ring
    have hh4: (∃ s:ℚ, 9*k^2-56 = s^2) ↔ ∃ s:ℚ, s^2 = 3^2 * (9*k^2-56) := by
      constructor <;> intro h
      · rcases h with ⟨a,ha⟩
        use 3*a
        rw [ha]; ring
      · rcases h with ⟨a,ha⟩
        use (a/3)
        have: (a/3)^2 = a^2 / 3^2 := by ring
        rw [this, ha]; ring
    rw [hh1, hh4, ← hh3]
    constructor <;> intro h
    · rcases h with ⟨u,hu⟩
      use (2*9*u+(-9*k))
      symm
      rw [mul_assoc] at hu
      apply discrim_eq_sq_of_quadratic_eq_zero hu
    · rcases h with ⟨s, hs⟩
      rw [pow_two] at hs
      convert exists_quadratic_eq_zero (by norm_num) ⟨s, hs.symm⟩ using 1
      ext x; ring_nf
  -- if an integer have rational square root, then it has integer square root, or, is perfect square.
  have h3(m:ℤ): (∃(s:ℚ), m = s^2) → ∃ s:ℤ, 0 ≤ s ∧ m = s^2 := by
    intro h
    have hh1: IsSquare (m:ℚ) := by
      exact (isSquare_iff_exists_sq (m:ℚ)).mpr h
    have hh2: IsSquare m := by
      exact Rat.isSquare_intCast_iff.mp hh1
    rcases (IsSquare.exists_sq m hh2) with ⟨c,hc⟩
    by_cases hh3: 0 ≤ c
    · use c
    · use (-c)
      push_neg at hh3
      constructor; linarith [hh3]
      rw [hc]; simp
  --9k^2-56 is perfect square, then exists some positive integer s, such that (3k-s)(3k+s) = 56
  have h4(k:ℤ): (∃s:ℚ, 9*k^2-56 = s^2) → ∃s:ℤ, 0 ≤ s ∧ (3*k-s)*(3*k+s) = 56
    := by
    intro h
    have hh1: 9*(k:ℚ)^2-56 = ↑(9*k^2-56 : ℤ) := by simp
    rw [hh1] at h
    rcases (h3 (9*k^2-56) h) with ⟨s,hs⟩
    use s
    simp [hs.left]
    linarith [hs.right]
  -- if (3k-s)(3k+s) = 56, then k can only be 5 or 3.
  have h5(k:ℤ)(kpos: 0 < k): (∃ s:ℤ, 0 ≤ s ∧ (3*k-s)*(3*k+s) = 56) →
    k = 5 ∨ k = 3 := by
    -- both 3k-s, 3k+s divide 56. 56 = 7x8, prime factors are 2 and 7.
    have hh1: ∀n:ℤ, 0 ≤ n → n ≤ 56 → n ∣ 56 →
      (n=1 ∨ 2 ∣ n ∨ 7 ∣ n) := by decide
    rintro ⟨s,hs⟩
    have hh2: 3*k+s ∣ 56 := by
      rw [← hs.right]
      exact Int.dvd_mul_left (3 * k - s) (3 * k + s)
    have hh3: 3*k+s ≤ 56 := by
      apply Int.le_of_dvd (by norm_num) hh2
    have hh4 := hh1 (3*k+s) (by linarith [kpos, hs.left]) hh3 hh2
    -- hh4 has three cases. and before going on, we single out some cases.
    have case14_28: (3*k+s = 14 → k = 3) ∧ (3*k+s = 28 → k = 5) := by
      constructor <;> intro heq
      <;> rw [heq] at hs
      <;> linarith [hs.right, heq]
    have case56: ¬ (3*k+s=56) := by
      by_contra! eq56
      rw [eq56] at hs
      exfalso; omega
    rcases hh4 with eq1 | dv2 | dv7
    · -- k > 0, obviously, 3k+s cannot be 1.
      omega
    · -- factors of 56 and divided by 2, are 2,4,8,14,28,56.
      have hh5: ∀n:ℤ, 0 ≤ n → n ≤ 56 → n ∣ 56 → 2 ∣ n →
        n=2 ∨ n=4 ∨ n=8 ∨ n=14 ∨ n=28 ∨ n=56 := by decide
      have hh6 := hh5 (3*k+s) (by linarith [kpos,hs.left])
        hh3 hh2 dv2
      have kge: 3*k ≥ 3 := by linarith [kpos]
      rcases hh6 with eq2 | eq4 | eq8 | eq14 | eq28 | eq56
      · --k >0, 3k+s ≥ 3, cannot be 2
        linarith [kge, eq2]
      · -- if 3k+s=4, since 3k is multiple of 3, only solution is k=1,s=1.
        have tt1: k=1 := by omega
        have tt2: s = 1 := by omega
        -- but k=1,s=1 does not have (3k-s)(3k+s)=56
        rw [tt1, tt2] at hs; norm_num at hs
      · --3k+s=8, then 3k-s=7, 2s=1, impossible.
        have: 3*k-s=7 := by
          rw [eq8] at hs
          linarith [hs.right]
        exfalso; omega
      · right; apply case14_28.left eq14
      · left; apply case14_28.right eq28
      · exfalso; apply case56 eq56
    · -- factors of 56 and divided by 7, are 7,14,28,56
      have hh5: ∀n:ℤ, 0 ≤ n → n ≤ 56 → n ∣ 56 → 7 ∣ n →
        n=7 ∨ n=14 ∨ n=28 ∨ n=56 := by decide
      have hh6 := hh5 (3*k+s) (by linarith [hs.left, kpos])
        hh3 hh2 dv7
      rcases hh6 with eq7 | eq14 | eq28 | eq56
      · --3k+s=7, then 3k-s = 56/7=8
        have: 3*k-s=8 := by
          rw [eq7] at hs
          linarith [hs.right]
        -- but 3k-s should < 3k+s, contradiction
        exfalso; omega
      · right; apply case14_28.left eq14
      · left; apply case14_28.right eq28
      · exfalso; apply case56 eq56
  -- and when k=5 or k=3, solve the equation 9u^2-9uk+14=0, we have 4 solutions in total.
  have h6(k:ℤ)(u:ℚ): k=5 ∨ k=3 → 9*u^2-9*u*k+14 = 0 →
    u = 1/3 ∨ u = 14/3 ∨ u = 2/3 ∨ u = 7/3 := by
    intro keq eq1
    have hh1: (9:ℚ) ≠ 0 := by simp
    rcases keq with k5 | k3
    · have eq2: 9*(u*u) + (-45*u)+14 = 0 := by
        rw [← eq1, k5]; ring
      have hh2: discrim (9:ℚ) (-45) 14 = 39*39 := by
        rw [discrim]; norm_num
      have := (quadratic_eq_zero_iff hh1 hh2 u).mp eq2
      simp at this; norm_num at this
      tauto
    · have eq2: 9*(u*u) + (-27*u) + 14 = 0 := by
        rw [← eq1, k3]; ring
      have hh2: discrim (9:ℚ) (-27) 14 = 15*15 := by
        rw [discrim]; norm_num
      have := (quadratic_eq_zero_iff hh1 hh2 u).mp eq2
      norm_num at this
      tauto
  -- proceed to the problem, and simplify the set.
  have h7: {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ Nat.gcd a b = 1 ∧ ∃ k : ℤ, (a / b : ℚ) + 14 * b / (9 * a) = k} = {(1,3),(2,3),(7,3),(14,3)} := by
    ext ⟨a,b⟩
    simp
    constructor <;> intro h
    · have nabs(n:ℕ): (n:ℤ).natAbs = n := by simp
      have bpos := Int.ofNat_pos.mpr h.right.left
      have aqpos: 0 < (a:ℚ) := by
        apply Nat.cast_pos.mpr h.left
      have bqpos: 0 < (b:ℚ) := by
        apply Nat.cast_pos.mpr h.right.left
      have copab: Nat.Coprime a b := by
        exact h.right.right.left
      have hh1: (a/b:ℚ) = 1/3 ∨ (a/b:ℚ) = 14/3
        ∨ (a/b:ℚ)=2/3 ∨ (a/b:ℚ) = 7/3 := by
        rcases h.right.right.right with ⟨k,hk⟩
        have kpos: 0 < k := by
          have: 0 < (k:ℚ) := by
            rw [← hk]
            apply add_pos
            · apply div_pos aqpos bqpos
            · apply div_pos (by linarith [bqpos]) (by linarith [aqpos])
          apply Int.cast_pos.mp this
        apply h6 k (a/b:ℚ)
        · apply h5 k kpos (h4 k ((h2 k).mp ?_))
          use (a/b:ℚ)
          apply h1 a b h.left h.right.left k hk
        · apply h1 a b h.left h.right.left k hk
      have hh2{x y c d:ℕ}: (x:ℤ) = c ∧ (y:ℤ) = d → x = c ∧ y = d := by
        intro h
        norm_cast at h
      have hh3{c d:ℕ}: (a/b:ℚ) = c/d → (Nat.Coprime c d → 0 < d → a = c ∧ b = d) := by
        intro h copcd dpos
        apply hh2
        apply Rat.div_int_inj bpos (by simp [dpos])
        · rw [nabs a, nabs b]
          apply copab
        · rw [nabs c, nabs d]
          apply copcd
        · simp [h]
      rcases hh1 with hh1 | hh1 | hh1 | hh1
      <;> have := hh3 hh1 (by norm_num) (by norm_num)
      all_goals tauto
    · rcases h with hab | hab | hab | hab
      <;> rw [hab.left, hab.right] <;> norm_num
      · use 5; simp
      · use 3; simp
      · use 3; simp
      · use 5; simp
  -- thus 4 pairs in total.
  rw [h7]
  simp [Set.ncard, Set.encard]
