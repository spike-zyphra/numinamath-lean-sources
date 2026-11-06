import Mathlib

/- Different prime numbers are coprime -/
lemma prime_coprime (p q : ℕ) : p.Prime → q.Prime → q ≠ p → p.Coprime q := by
  intros hp hq n
  refine (Nat.disjoint_primeFactors ?_ ?_).mp ?_
  . exact Nat.Prime.ne_zero hp
  . exact Nat.Prime.ne_zero hq
  . rw [Nat.Prime.primeFactors hp, Nat.Prime.primeFactors hq]
    simp
    assumption

/- no two prime numbers x y, such that y = x + 19 -/
lemma no_two_prime_diff_19 :
  ¬∃ x y : ℕ, x.Prime ∧ y.Prime ∧ y = x + 19 := by
  rintro ⟨x, y, hx, hy, h_eq⟩
  by_cases h : x ≤ 2
  · have : x = 2 := by
      interval_cases x <;> tauto
    rw [this] at h_eq
    have h21 : y = 21 := by omega
    rw [h21] at hy
    norm_num at hy
  · push_neg at h
    have h1 : x % 2 = 1 := by
      by_contra h2
      push_neg at h2
      have h3 : x % 2 = 0 := by omega
      have h4 : ¬ x.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ x by omega)
        omega
        omega
      contradiction
    have h2 : y % 2 = 0 := by
      omega
    have h3 : ¬ y.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ y by omega)
      omega
      omega
    contradiction

/- Find all prime pairs $(x, y)$ satisfying $x^{y}-y^{x}=$ $x y^{2}-19$. -/
theorem number_theory_249846 (x y : ℕ) (hx : x.Prime) (hy : y.Prime) :
    (x^y - y^x : ℤ) = x * y^2 - 19 ↔ (x = 2 ∧ y = 3) ∨ (x = 2 ∧ y = 7) :=
by
  constructor; swap
  . rintro (h|h) <;> rw [h.1, h.2] <;> simp
  intro H
  rcases em (x = y) with (h|h)
  . rw [h] at H
    ring_nf at H
    have eq : y ^ 3 = 19 := by linarith
    have : 2 < y ∧ y < 3 := by
      by_contra h
      have : 2 ≥ y ∨ y ≥ 3 := by
        by_contra x
        push_neg at x
        apply h
        assumption
      rcases this with (h|h)
      . have : y^3 ≤ 2^3 := Nat.pow_le_pow_left h 3
        rw [eq] at this
        simp at this
      . have : y^3 ≥ 3^3 := Nat.pow_le_pow_left h 3
        rw [eq] at this
        simp at this
    cases this
    interval_cases y
  -- Using Fermat's little theorem
  have xyMy : x^y ≡ x [MOD y] := by
    have : y.totient = y - 1 := Nat.totient_prime hy
    have : x ^ (y - 1) ≡ 1 [MOD y] := by
      rw [←this]
      -- Fermat-Euler totient theorem, a generalization version of FLT
      apply Nat.ModEq.pow_totient
      exact (Nat.coprime_primes hx hy).mpr h
    have : x ^ (y - 1) * x ≡ 1 * x [MOD y] := Nat.ModEq.mul this rfl
    rw [show x ^ (y - 1) * x = x ^ y by
          apply Nat.pow_pred_mul
          exact Nat.Prime.pos hy
       ] at this
    simp at this
    assumption
  -- And we have the similar for y
  have yxMx : y^x ≡ y [MOD x] := by
    have : x.totient = x - 1 := Nat.totient_prime hx
    have : y ^ (x - 1) ≡ 1 [MOD x] := by
      rw [←this]
      -- Fermat-Euler totient theorem, a generalization version of FLT
      apply Nat.ModEq.pow_totient
      exact (Nat.coprime_primes hy hx).mpr fun a ↦ h (id (Eq.symm a))
    have : y ^ (x - 1) * y ≡ 1 * y [MOD x] := Nat.ModEq.mul this rfl
    rw [show y ^ (x - 1) * y = y ^ x by
          apply Nat.pow_pred_mul
          exact Nat.Prime.pos hx
       ] at this
    simp at this
    assumption
  have H1x : x ^ y ≡ -19 [ZMOD y] := by
    have : (x ^ y : ℤ) = x * y ^ 2 - 19 + y ^ x := by
      linarith
    rw [this, show (x * y ^ 2 : ℤ) = y * (x * y) by linarith, sub_add_comm]
    trans y^x - 19
    . apply Int.modEq_add_fac_self
    . rw [show (y ^ x : ℤ) = y * y ^ (x - 1) by
            have : x = x - 1 + 1 := by
              rw [Nat.sub_add_cancel]
              apply Nat.Prime.pos
              assumption
            rw [this, Nat.add_sub_cancel]
            exact Int.pow_succ' (↑y) (x - 1)
         , Int.sub_eq_add_neg, add_comm]
      apply Int.modEq_add_fac_self
  have H1y : y ^ x ≡ 19 [ZMOD x] := by
    have : (y ^ x : ℤ) = - x * y ^ 2 + 19 + x ^ y := by
      linarith
    rw [this, show (- x * y ^ 2 : ℤ) = x * (- y ^2) by linarith, add_comm, add_comm (x * - y^2 : ℤ), ←add_assoc]
    trans x^y + 19
    . apply Int.modEq_add_fac_self
    .
      rw [show (x ^ y : ℤ) = x * x ^ (y - 1) by
            have : y = y - 1 + 1 := by
              rw [Nat.sub_add_cancel]
              apply Nat.Prime.pos
              assumption
            rw [this, Nat.add_sub_cancel]
            exact Int.pow_succ' (↑x) (y - 1)
         , add_comm]
      apply Int.modEq_add_fac_self
  -- Thus we have
  have H2x : x ≡ -19 [ZMOD y] := by
    trans x ^ y
    . symm
      simp [Int.ModEq]
      simp [Nat.ModEq] at xyMy
      zify at xyMy
      assumption
    . assumption
  have H2y : y ≡ 19 [ZMOD x] := by
    trans y ^ x
    . symm
      simp [Int.ModEq]
      simp [Nat.ModEq] at yxMx
      zify at yxMx
      assumption
    . assumption
  have yDx : y ∣ x + 19 := by
    simp [Int.ModEq] at H2x
    apply_fun (fun (x : ℤ) => x + 19 % y) at H2x
    apply_fun (fun (x : ℤ) => x % y) at H2x
    rw [←Int.add_emod, ←Int.add_emod] at H2x
    simp at H2x
    zify
    assumption
  have xDy: (x : ℤ) ∣ y - 19 := by
    simp [Int.ModEq] at H2y
    apply_fun (fun (a : ℤ) => a - 19 % x) at H2y
    apply_fun (fun (a : ℤ) => a % x) at H2y
    rw [←Int.sub_emod, ←Int.sub_emod] at H2y
    simp at H2y
    assumption

  -- Now we check each cases,
  rcases em (x = 2) with (h1|h1)
  . -- The answer case, all the other cases are false.
    rw [h1] at yDx
    simp at yDx
    have : y = 3 ∨ y = 7 := by
      have : y ≤ 21 :=  Nat.le_of_dvd (by norm_num) yDx
      interval_cases y <;> norm_num at h1 yDx <;> tauto
    tauto
  -- Now we show that other cases are impossible.
  exfalso
  rcases em (y = 2) with (h2|h2)
  . rw [h2] at H xDy
    simp at xDy
    have : x ∣ 17 := by zify; assumption
    have : x ≤ 17 := Nat.le_of_dvd (by norm_num) this
    -- so x must be 17
    have : x = 17 := by
      interval_cases x <;> norm_num at h2 xDy <;> tauto
    subst this
    -- when x = 17, y = 2, we have False.
    simp at H
  . -- x ≥ 3 and y ≥ 3
    have : x ≥ 3 ∧ y ≥ 3 := by
      by_contra h
      have : x < 3 ∨ y < 3 := by
        by_contra h'
        push_neg at h'
        apply h
        exact h'
      rcases this with (h|h)
      . have : x ≥ 2 := Nat.Prime.two_le hx
        interval_cases x; tauto
      . have : y ≥ 2 := Nat.Prime.two_le hy
        interval_cases y; tauto
    exfalso
    -- multiply both sides of $y \mid (x + 19)$ and $x \mid (y - 19)$
    have : (x * y : ℤ) ∣ (x + 19) * (y - 19) := by
      zify at yDx
      rw [mul_comm]
      apply Int.mul_dvd_mul
      assumption
      assumption
    -- Do more simplification, we left two cases (x = 19 or y = 19)
    -- we will back to these left two cases later.
    have : (x * y : ℤ) ∣ y - x - 19 ∨ x = 19 ∨ y = 19 := by
      rw [show ((x + 19) * (y - 19) : ℤ) = x*y + 19 * (y - x - 19) by linarith] at this
      have H : (x * y : ℤ) ∣ 19 * (y - x - 19) := dvd_add_self_left.mp this
      rcases em (x = 19 ∨ y = 19) with ((h19|h19)|h19)
      . tauto
      . tauto
      have : Nat.gcd (x * y) 19 = 1 := by
        apply Nat.coprime_mul_iff_left.mpr
        constructor
        . apply prime_coprime
          assumption
          decide
          tauto
        . apply prime_coprime
          assumption
          decide
          tauto
      left
      apply Int.dvd_of_dvd_mul_right_of_gcd_one
      assumption
      assumption
    rcases this with (h|h|h)
    . -- (x * y : ℤ) ∣ y - x - 19
      have : y ≤ x + 19 := by
        apply Nat.le_of_dvd
        simp
        assumption
      have : (y - x - 19 : ℤ) ≤ 0 := by
        rw [show (0 : ℤ) = x + 19 - x - 19 by simp]
        linarith
      let E : ℤ := - (y - x - 19)
      have Ege0 : E ≥ 0 := by simp [E]; linarith
      let En : ℕ := E.natAbs
      have Eneq : En = E := Eq.symm (Int.eq_natAbs_of_zero_le Ege0)
      have h3 : En ≥ x * y := by
        have : x * y ∣ En := by
          zify
          rw [Eneq]
          simp [E]
          let ⟨c,h⟩ := h
          use - c
          linarith
        apply Nat.le_of_dvd
        . by_contra h
          have : En = 0 := by omega
          rw [this] at Eneq
          simp [E] at Eneq
          have : y = 19 + x := by
            zify
            linarith
          apply no_two_prime_diff_19
          use x, y
          rw [add_comm] at this
          tauto
        . assumption
      simp [E] at Eneq
      have : y ≥ 3 := by linarith
      have h4 : x * y ≥ 3 * x := by
        rw [mul_comm 3 x]
        exact Nat.mul_le_mul_left x this
      have : (19 - (y - x) : ℤ) ≤ x + 16 := by
        rw [show (x + 16 : ℤ) = x + 19 - 3 by omega]
        omega
      zify at h3
      rw [Eneq] at h3
      have : (x * y : ℤ) ≤ x + 16 := by linarith
      have : 3 * x ≤ x + 16 := by
        zify
        zify at h4
        omega
      have : x ≤ 8 := by linarith
      interval_cases x <;> try norm_num at hx
      . apply h1; rfl
      . simp at yDx
        have : y = 1 ∨ y = 2 ∨ y = 11 ∨ y = 22 := by
          have : y ≤ 22 := by exact Nat.le_of_dvd (by norm_num) yDx
          interval_cases y <;> tauto
        rcases this with (h|h|h|h) <;> subst h <;> try contradiction
      . simp at yDx
        have : y ≤ 24 := by
          exact Nat.le_of_dvd (by norm_num) yDx
        interval_cases y <;> norm_num at hy yDx; omega
      . simp at yDx
        have : y ≤ 26 := by
          exact Nat.le_of_dvd (by norm_num) yDx
        interval_cases y <;> norm_num at hy yDx; omega
    . subst h
      simp at yDx
      have : y ≤ 38 := by
        exact Nat.le_of_dvd (by norm_num) yDx
      interval_cases y <;> norm_num at hy yDx;
      . omega
      . apply h
        rfl
    . subst h
      have : 19 ∣ x := Nat.dvd_add_self_right.mp yDx
      let ⟨c, h⟩ := this
      rcases c with (_|_|c)
      . subst h; norm_num at hx
      . subst h; simp at h
      . subst h
        have h1 : ¬ Nat.Prime (19 * (c + 1 + 1)) := by
          apply Nat.not_prime_mul
          all_goals omega
        exfalso; apply h1; assumption
