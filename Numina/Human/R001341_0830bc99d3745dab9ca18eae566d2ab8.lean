import Mathlib

/-- Find all integer solutions of the equation  $$ \frac{x^{7}-1}{x-1}=y^{5}-1 $$  (Russia) -/
theorem Number_Theory_n5 {x y : ℤ} (hx : x ≠ 1) :
    ¬ (x^7 - 1 : ℚ)/(x - 1) = y^5 - 1 := by
  -- The equation has no integer solutions.
  have h_aux1 : x^7 - 1 = (x - 1) * (1 + x + x^2 + x^3 + x^4 + x^5 + x^6) := by
    ring
  have h_aux2 : (x^7 - 1 : ℚ)/(x - 1) = 1 + x + x^2 + x^3 + x^4 + x^5 + x^6 := by
    qify at hx
    field_simp [show (x : ℚ) - 1 ≠ 0 by contrapose! hx; linarith]
    ring
  have h_aux3 : y^5 - 1 = (y - 1) * (1 + y + y^2 + y^3 + y^4) := by
    ring
  -- To show this, we first prove a lemma.
  -- Lemma. If $x$ is an integer and $p$ is a prime divisor of $\frac{x^{7}-1}{x-1}$ then either $p \equiv 1(\bmod 7)$ or $p=7$.
  have h_lemma (p : ℕ) (hp : Nat.Prime p) (h : (p : ℤ) ∣ (x^7 - 1)/(x - 1)) : p ≡ 1 [MOD 7] ∨ p = 7 := by
    -- Proof. Both $x^{7}-1$ and $x^{p-1}-1$ are divisible by $p$, by hypothesis and by Fermat's little theorem, respectively.
    have h1 : (p : ℤ) ∣ (x^7 - 1) := by
      have : x^7 - 1 = (x^7 - 1) / (x - 1) * (x - 1) := by
        rw [Int.ediv_mul_cancel]
        simp [h_aux1]
      rw [this]
      apply h.mul_right
    have h2 : (p : ℤ) ∣ (x^(p - 1) - 1) := by
      apply Int.ModEq.dvd
      symm
      apply Int.ModEq.pow_card_sub_one_eq_one hp (n := x)
      symm
      rw [Prime.coprime_iff_not_dvd (by exact Nat.prime_iff_prime_int.mp hp)]
      intro h2
      apply Int.dvd_iff_dvd_of_dvd_sub at h1
      apply dvd_pow at h2
      specialize h2 (show 7 ≠ 0 by norm_num)
      rw [h1] at h2
      norm_cast at h2
      simp only [Nat.dvd_one] at h2
      simp [h2, Nat.not_prime_one] at hp
    -- Suppose that 7 does not divide $p-1$.
    suffices ¬ 7 ∣ (p - 1) → p = 7 by
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (hp.one_le)]
      tauto
    intro h3
    -- Then $\operatorname{gcd}(p-1,7)=1$, so there exist integers $k$ and $m$ such that $7 k+(p-1) m=1$.
    obtain ⟨k, m, h4⟩ : ∃ (k : ℤ) (m : ℤ), 7 * k + (p - 1) * m = 1 := by
      suffices IsCoprime (7 : ℤ) (p - 1) by
        simp only [IsCoprime] at this
        simp_rw [mul_comm]
        exact this
      rw [Prime.coprime_iff_not_dvd]
      · zify [hp.one_le] at h3
        exact h3
      · norm_num
    -- We therefore have $$ x \equiv x^{7 k+(p-1) m} \equiv\left(x^{7}\right)^{k} \cdot\left(x^{p-1}\right)^{m} \equiv 1 \quad(\bmod p) $$
    have h5 : x ≡ 1 [ZMOD p] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      have : Fact (Nat.Prime p) := ⟨hp⟩
      calc
        _ = (x : ZMod p) ^ (1 : ℤ) := by
          simp
        _ = (x : ZMod p) ^ (7 * k + (p - 1) * m : ℤ) := by
          rw [h4]
        _ = _ := by
          simp only [← ZMod.intCast_eq_intCast_iff_dvd_sub, Int.cast_one, Int.cast_pow, ← zpow_natCast, Nat.cast_ofNat] at h1 h2
          zify [hp.one_le] at h2
          rw [zpow_add₀, zpow_mul, zpow_mul]
          swap
          · intro h3
            simp only [h3] at h1
            norm_num at h1
          simp [← h1, ← h2]
    -- and so $$ \frac{x^{7}-1}{x-1}=1+x+\cdots+x^{6} \equiv 7 \quad(\bmod p) $$
    have h6 : (x^7 - 1)/(x - 1) ≡ 7 [ZMOD p] := by
      rw [h_aux1, Int.mul_ediv_cancel_left _ (by omega)]
      rw [show (7 : ℤ) = (7 : ℕ) by simp]
      rw [← ZMod.intCast_eq_intCast_iff] at h5 ⊢
      simp only [Int.cast_add, Int.cast_one, h5, Int.cast_pow, one_pow, Nat.cast_ofNat,
        Int.cast_ofNat]
      ring
    -- It follows that $p$ divides 7 , hence $p=7$ must hold if $p \equiv 1(\bmod 7)$ does not, as stated.
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rw [show (7 : ℤ) = (7 : ℕ) by simp, ← ZMod.intCast_eq_intCast_iff, h] at h6
    simp only [Nat.cast_ofNat, Int.cast_ofNat] at h6
    symm at h6
    rw [show (7 : ZMod p) = (7 : ℕ) by simp, ZMod.natCast_zmod_eq_zero_iff_dvd] at h6
    rwa [← Nat.prime_dvd_prime_iff_eq hp]
    norm_num
  -- The lemma shows that each positive divisor $d$ of $\frac{x^{7}-1}{x-1}$ satisfies either $d \equiv 0(\bmod 7)$ or $d \equiv 1(\bmod 7)$.
  have h1 (d : ℤ) (hd_pos : 0 < d) (hd : d ∣ (x^7 - 1)/(x - 1)) : d ≡ 0 [ZMOD 7] ∨ d ≡ 1 [ZMOD 7] := by
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hd_pos.le
    subst hn
    rw [show (7 : ℤ) = (7 : ℕ) by simp, show (0 : ℤ) = (0 : ℕ) by simp, show (1 : ℤ) = (1 : ℕ) by simp]
    simp only [Int.natCast_modEq_iff, ← ZMod.eq_iff_modEq_nat]
    simp only [Nat.cast_zero, Nat.cast_one]
    simp only [Nat.cast_pos] at hd_pos
    have := Nat.factorization_prod_pow_eq_self (n := n) (by omega)
    apply_fun Nat.cast (R := ZMod 7) at this
    simp only [Finsupp.prod, Nat.support_factorization, Nat.cast_prod, Nat.cast_pow] at this
    by_cases h7 : 7 ∈ n.primeFactors
    · left
      rw [← Finset.mul_prod_erase _ _ h7] at this
      reduce_mod_char at this
      -- have : n.factorization 7 ≠ 0 := by exact Finsupp.mem_support_iff.mp h7
      have _ : Fact (1 < 7) := ⟨by norm_num⟩
      rw [zero_pow_eq_zero.mpr (Finsupp.mem_support_iff.mp h7)] at this
      simp only [zero_mul] at this
      exact this.symm
    · right
      rw [← this]
      trans ∏ x ∈ n.primeFactors, 1
      swap
      · simp
      apply Finset.prod_congr rfl
      intro q hq
      simp only [Nat.mem_primeFactors, ne_eq] at hq
      obtain ⟨hq1, hq2, hq3⟩ := hq
      zify at hq2
      specialize h_lemma q hq1 (hq2.trans hd)
      have hq4 : q ≠ 7 := by
        intro hq4
        simp only [Nat.mem_primeFactors, show Nat.Prime 7 by norm_num, ne_eq, true_and, not_and,
          Decidable.not_not] at h7
        simp only [hq4, Nat.cast_ofNat] at hq2
        norm_cast at hq2
        solve_by_elim
      simp only [← ZMod.eq_iff_modEq_nat, Nat.cast_one, hq4, or_false] at h_lemma
      simp [h_lemma]
  -- Now assume that $(x, y)$ is an integer solution of the original equation.
  intro h
  have h' : (x^7 - 1)/(x - 1) = y^5 - 1 := by
    qify
    rw [Rat.intCast_div]
    · qify
      assumption
    rw [h_aux1]
    apply Int.dvd_mul_right
  -- Notice that $y-1 > 0$, because $\frac{x^{7}-1}{x-1} > 0$ for all $x \neq 1$.
  have h2 : 0 < y - 1 := by
    have : 0 < (x ^ 7 - 1) / (x - 1) := by
      apply Int.lt_or_gt_of_ne at hx
      rw [h_aux1, Int.mul_ediv_cancel_left _ (by omega)]
      rcases hx with hx | hx
      · have (m : ℕ) : 0 ≤ x ^ (2 * m + 2) + x ^ (2 * m + 1) := by
          calc
            _ ≤ x ^ (2 * m + 1) * (x + 1) := by
              by_cases hx0 : x = 0
              · simp [hx0]
              apply Int.mul_nonneg_of_nonpos_of_nonpos _ (by omega)
              rw [Odd.pow_nonpos_iff]
              · omega
              · exact odd_two_mul_add_one m
            _ = _ := by ring_nf
        have h_le_1 := this 0
        have h_le_2 := this 1
        have h_le_3 := this 2
        simp only [mul_zero, zero_add, pow_one, mul_one, Nat.reduceAdd,
          Nat.reduceMul] at h_le_1 h_le_2 h_le_3
        linarith
      · replace hx : 0 < x := by linarith
        linarith [Lean.Omega.Int.pos_pow_of_pos x 2 hx, Lean.Omega.Int.pos_pow_of_pos x 3 hx,
          Lean.Omega.Int.pos_pow_of_pos x 4 hx, Lean.Omega.Int.pos_pow_of_pos x 5 hx,
          Lean.Omega.Int.pos_pow_of_pos x 6 hx]
    rw [h'] at this
    replace this : 1 < y ^ 5 := by linarith
    rw [one_lt_pow_iff_of_nonneg] at this
    · linarith
    · contrapose! this
      suffices y ^ 5 < 0 by linarith
      apply Odd.pow_neg (by rw [Nat.odd_iff]) this
    · norm_num
  -- Since $y-1$ divides $\frac{x^{7}-1}{x-1}=y^{5}-1$, we have $y \equiv 1(\bmod 7)$ or $y \equiv 2(\bmod 7)$ by the previous paragraph.
  have h3 : y ≡ 1 [ZMOD 7] ∨ y ≡ 2 [ZMOD 7] := by
    have : y - 1 ∣ (x^7 - 1)/(x - 1) := by
      rw [h', h_aux3]
      apply Int.dvd_mul_right
    specialize h1 (y - 1) h2 this
    rcases h1 with h1 | h1
    · left
      apply Int.ModEq.add_right_cancel' (-1) h1
    · right
      exact Int.ModEq.add_right_cancel' (-1) h1
  -- In the first case, $1+y+y^{2}+y^{3}+y^{4} \equiv 5(\bmod 7)$, and in the second $1+y+y^{2}+y^{3}+y^{4} \equiv 3(\bmod 7)$.
  -- Both possibilities contradict the fact that the positive divisor $1+y+y^{2}+y^{3}+y^{4}$ of $\frac{x^{7}-1}{x-1}$ is congruent to 0 or 1 modulo 7 .
  rcases h3 with h3 | h3
  · have h4 : 1 + y + y^2 + y^3 + y^4 ≡ 5 [ZMOD 7] := by
      rw [show (7 : ℤ) = (7 : ℕ) by simp, ← ZMod.intCast_eq_intCast_iff] at h3 ⊢
      simp only [Int.cast_add, Int.cast_one, h3, Int.cast_pow, one_pow, Int.cast_ofNat]
      reduce_mod_char
    specialize h1 (1 + y + y^2 + y^3 + y^4) ?_ (by rw [h', h_aux3]; apply Int.dvd_mul_left)
    · replace h2 : 0 < y := by linarith
      linarith [Lean.Omega.Int.pos_pow_of_pos y 2 h2, Lean.Omega.Int.pos_pow_of_pos y 3 h2,
        Lean.Omega.Int.pos_pow_of_pos y 4 h2, Lean.Omega.Int.pos_pow_of_pos y 5 h2]
    rcases h1 with h1 | h1
    · have := h4.symm.trans h1
      simp [Int.ModEq] at this
    · have := h4.symm.trans h1
      simp [Int.ModEq] at this
  · have h4 : 1 + y + y^2 + y^3 + y^4 ≡ 3 [ZMOD 7] := by
      rw [show (7 : ℤ) = (7 : ℕ) by simp, ← ZMod.intCast_eq_intCast_iff] at h3 ⊢
      simp only [Int.cast_add, Int.cast_one, h3, Int.cast_ofNat, Int.cast_pow]
      reduce_mod_char
    specialize h1 (1 + y + y^2 + y^3 + y^4) ?_ (by rw [h', h_aux3]; apply Int.dvd_mul_left)
    · replace h2 : 0 < y := by linarith
      linarith [Lean.Omega.Int.pos_pow_of_pos y 2 h2, Lean.Omega.Int.pos_pow_of_pos y 3 h2,
        Lean.Omega.Int.pos_pow_of_pos y 4 h2, Lean.Omega.Int.pos_pow_of_pos y 5 h2]
    rcases h1 with h1 | h1
    · have := h4.symm.trans h1
      simp [Int.ModEq] at this
    · have := h4.symm.trans h1
      simp [Int.ModEq] at this
  -- So the given equation has no integer solutions.
