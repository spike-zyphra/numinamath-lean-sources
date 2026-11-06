import Mathlib

open ZMod

/- The sequences $\mathrm{a}_{0}, \mathrm{a}_{1}, \mathrm{a}_{2}, \ldots$ and $\mathrm{b}_{0}, \mathrm{~b}_{1}, \mathrm{~b}_{2}, \ldots$ are defined by $\mathrm{a}_{0}=1, \mathrm{~b}_{0}=4, \mathrm{a}_{\mathrm{n}+1}=\mathrm{a}_{\mathrm{n}}{ }^{2001}+\mathrm{b}_{\mathrm{n}}$, $b_{n+1}=b_{n}^{2001}+a_{n}$. Show that no member of either sequence is divisible by 2003. -/
theorem number_theory_605247 (a b : ℕ → ℕ)
    (ha0 : a 0 = 1) (hb0 : b 0 = 4)
    (han : ∀ n, a (n + 1) = a n ^ 2001 + b n)
    (hbn : ∀ n, b (n + 1) = b n ^ 2001 + a n) :
    ¬ ∃ n, 2003 ∣ a n ∨ 2003 ∣ b n := by
    let hprime : Fact (Nat.Prime 2003) := { out := by native_decide }
    have a_eq (n : ℕ) (ha : (a n : ZMod 2003) ≠ 0) : (a (n + 1) : ZMod 2003) = ((a n) : ZMod 2003)⁻¹ + b n:= by
      rw [(by ring : ((a n : ZMod 2003))⁻¹ = 1 * ((a n : ZMod 2003))⁻¹),
        show ( 1 * ((a n : ZMod 2003))⁻¹ = ↑(a n) ^ (2003 - 1) * ((a n : ZMod 2003))⁻¹) by rw [← ZMod.pow_card_sub_one_eq_one ha],
        han, Nat.cast_add, Nat.cast_pow]
      nth_rewrite 3 [(by ring : (a n : ZMod 2003) = (a n : ZMod 2003)^1)]
      rw [← pow_sub₀ (a n : ZMod 2003) ha (by linarith)]
    have b_eq (n : ℕ) (hb : (b n : ZMod 2003) ≠ 0) : b (n + 1) = ((b n) : ZMod 2003)⁻¹ + a n := by
      rw [(by ring : ((b n : ZMod 2003))⁻¹ = 1 * ((b n : ZMod 2003))⁻¹),
        show ( 1 * ((b n : ZMod 2003))⁻¹ = ↑(b n) ^ (2003 - 1) * ((b n : ZMod 2003))⁻¹) by rw [← ZMod.pow_card_sub_one_eq_one hb],
        hbn, Nat.cast_add, Nat.cast_pow]
      nth_rewrite 3 [(by ring : (b n : ZMod 2003) = (b n : ZMod 2003)^1)]
      rw [← pow_sub₀ (b n : ZMod 2003) hb (by linarith)]
    -- We define the sequence $c_n$ defined to be the product $a_n * b_n$
    let c : ℕ → ℕ := fun n => a n * b n
    have hc (n : ℕ) (hc : (c n : ZMod 2003) ≠ 0) : c (n + 1) = (c n + 1)^2 / (c n : ZMod 2003) := by
      have hc' := hc
      dsimp [c] at hc'
      rw [← ne_eq, Nat.cast_mul, mul_ne_zero_iff] at hc'
      obtain ⟨a_ne_zero, b_ne_zero⟩ := hc'
      calc
      c (n + 1) = (c n : ZMod 2003) + (c n : ZMod 2003)⁻¹ + 2 := by
        simp [c]
        rw [a_eq n a_ne_zero, b_eq n b_ne_zero]
        field_simp
        ring
      _ = (c n + 1)^2 / (c n : ZMod 2003) := by
        field_simp [hc]
        ring
    let inst : Field (ZMod 2003) := ZMod.instField 2003
    -- Showing that the sequences $a_n$ and $b_n$ are never divisible by $2003$ is equivalent
    -- to showing that the of products $c_n := a_n * b_n$ is never equal to zero modulo $2003$
    suffices ∀ n,  ¬ c n  = (0 : ZMod 2003) by
      push_neg
      intro n
      specialize this n
      dsimp [c] at this
      rw [← ne_eq, Nat.cast_mul, mul_ne_zero_iff] at this
      obtain ⟨not_dvd_a, not_dvd_b⟩ := this
      -- Given $a_n$ and $b_n$ are not zero modulo $2003$, they are not divisible by $2003$.
      split_ands
      · intro dvd_a
        rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at dvd_a
        -- a contradiction
        exact not_dvd_a dvd_a
      · intro dvd_b
        rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at dvd_b
        -- a contradiction
        exact not_dvd_b dvd_b
    intro n
    induction n using Nat.strong_induction_on
    case h k hkc =>
      intro c_eq_zero
      by_cases hk : 2 ≤ k
      -- We show that if $c_k = 0$ then $c_{k-1} = -1$ and thus $c_{k-2}^2 + 3 * c_{k-2} + 1 = 0 \mod 2003$. But this contradicts the fact that $x^2 + 3x + 1$ has no solutions in the field $\mathbb{Z}/2003\mathbb{Z}$.
      · have hc₁ := hc (k - 1) ((ne_eq _ _).symm ▸ hkc (k - 1) (by omega))
        have one_le_k : 1 ≤ k := by linarith
        simp [Nat.sub_add_cancel one_le_k, c_eq_zero] at hc₁
        field_simp [hkc (k -1) (by omega)] at hc₁
        symm at hc₁
        rw [sq_eq_zero_iff] at hc₁
        rw [add_eq_zero_iff_eq_neg] at hc₁
        have hc₂ := hc (k - 2) ((ne_eq _ _).symm ▸ hkc (k - 2) (by omega))
        nth_rewrite 1 [(by norm_num : 2 = 1 + 1), (by omega : k - 2 + 1 = k - 1), hc₁] at hc₂
        field_simp [hkc (k - 2) (by omega)] at hc₂
        -- We show that  $x^2 + 3x + 1$ has no solutions in the field $\mathbb{Z}/2003\mathbb{Z}$ by observing that the statement 
        -- $x^2 + 3x + 1 = 0$ is equivalent to saying that $502$ is a quadratic residue in $(\mathbb{Z}/2003\mathbb{Z})^\times$.
        suffices ∀ x : ZMod 2003, 0 ≠ (x^2 + 3 * x + 1) by
          specialize this (c (k - 2))
          symm at hc₂
          rw [← add_eq_zero_iff_eq_neg] at hc₂
          ring_nf at hc₂
          symm at this
          ring_nf at this
          exact this hc₂
        suffices ¬ IsSquare ((502 : ℤ) : ZMod 2003) by
          intro x hx
          have key : (x - 1000)^2 = 1000^2 - 1 := by
            rw [sub_sq]
            rw [(by norm_num : 1000^2 - (1 : ZMod 2003) = - (-1000^2 + 1))]
            rw [← add_eq_zero_iff_eq_neg]
            ring_nf at hx ⊢
            rw [mul_comm, sub_eq_add_neg, ← neg_mul, (by native_decide : -(2000 : ZMod 2003) = 3), mul_comm]
            exact hx.symm
          rw [(by native_decide : 1000^2 - 1 = (502 : ZMod 2003) )] at key
          simp [IsSquare] at this
          specialize this (x - 1000)
          rw [← sq] at this
          exact this key.symm
        -- We show that $502$ is not a quadratic residue by computing the Legendre symbol $(502/2003)$ and showing that it is $-1$.
        rw [← ZMod.nonsquare_iff_jacobiSym_eq_neg_one, ← jacobiSym.legendreSym.to_jacobiSym,
          (by norm_num : (502 : ℤ) = 2 * 251), legendreSym.mul, legendreSym.at_two (by norm_num)]
        let two_hundred_and_fifty_one_prime : Fact (Nat.Prime 251) := by native_decide
        have mod_four : 251 % 4 = 3 := by norm_num
        have mod_four' : 2003 % 4 = 3 := by norm_num
        -- Given $251 = 3 \mod 4$ and $2003 = 3 \mod 4$, we use quadratic reciprocity
        rw [(by norm_num : (251 : ℤ) = ((251 : ℕ) : ℤ)),
          legendreSym.quadratic_reciprocity_three_mod_four mod_four mod_four']
        simp only [Nat.cast_ofNat, χ₈_apply, Int.reduceNeg, mul_neg, neg_mul, one_mul, neg_neg]
        -- reduce modulo 251
        simp only [legendreSym.mod, Nat.cast_ofNat, Int.reduceMod, Int.reduceNeg]
        simp only [Nat.cast_ofNat, Int.reduceMod, Int.reduceNeg]
        rw [(by norm_num : (246 : ℤ) = 2 * 3 * 41), legendreSym.mul, legendreSym.mul]
        simp only [ne_eq, Nat.reduceEqDiff, not_false_eq_true, legendreSym.at_two, Nat.cast_ofNat,
          χ₈_apply, Int.reduceNeg, neg_mul, one_mul, neg_inj]
        have mod_four'' : 3 % 4 = 3 := by native_decide
        -- Given $251 = 3 \mod 4$ and $3 = 3 \mod 4$, we use quadratic reciprocity
        rw [(by norm_num : (3 : ℤ) = ((3 : ℕ) : ℤ)),
          legendreSym.quadratic_reciprocity_three_mod_four mod_four'' mod_four]
        -- reduce modulo 3
        simp only [Nat.cast_ofNat, legendreSym.mod, Int.reduceMod, neg_mul]
        simp only [Nat.cast_ofNat, Int.reduceMod]
        simp [legendreSym.at_two]
        let forty_one_prime : Fact (Nat.Prime 41) := by native_decide
        have mod_four''' : 41 % 4 = 1 := by norm_num
        rw [
            (by norm_num : (41 : ℤ) = ((41 : ℕ) : ℤ)),
            legendreSym.quadratic_reciprocity_one_mod_four mod_four''' (by norm_num)]
        -- reduce modulo 41
        simp only [Nat.cast_ofNat, legendreSym.mod, Int.reduceMod]
        simp only [Nat.cast_ofNat, Int.reduceMod]
        have mod_four'''' : 5 % 4 = 1 := by norm_num
        let five_prime : Fact (Nat.Prime 5) := by native_decide
        rw [(by norm_num : (5 : ℤ) = ((5 : ℕ): ℤ)),
          legendreSym.quadratic_reciprocity_one_mod_four mod_four'''' (by norm_num)]
        -- reduce modulo 5
        simp only [Nat.cast_ofNat, legendreSym.mod, Int.reduceMod]
        -- Legendre symbol at 1 is 1
        simp only [Nat.cast_ofNat, Int.reduceMod, legendreSym.at_one]
      · simp at hk
        interval_cases k
        · simp [hk, c, ha0, hb0] at c_eq_zero
          have c_ne_zero : (4 : ZMod 2003) ≠ 0 := by native_decide
          exact c_ne_zero c_eq_zero
        · simp only [han, ha0, one_pow, hb0, Nat.reduceAdd, hbn, Nat.cast_mul, Nat.cast_ofNat,
          Nat.cast_add, Nat.cast_pow, Nat.cast_one, mul_eq_zero, inst, c] at c_eq_zero
          rcases c_eq_zero with (hl | hr)
          · have contr : (5 : ZMod 2003) ≠ 0 := by native_decide
            exact contr hl
          · -- successively reduce modulo 2003 suitably large powers of 4
            have contr : (4 ^ 2001 : ZMod 2003) + (1 : ZMod 2003) ≠ 0 := by native_decide
            exact contr hr
