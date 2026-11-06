import Mathlib


/- Prove that for any odd integer $n \geq 3$,
the expression $(n+1)^{n^{n-1}} + (n-1)^{n^{n+1}}$ is divisible by $n^n$. -/
theorem number_theory_613243 {n : ℕ} (hn : Odd n ∧ 3 ≤ n) :
    n ^ n ∣ (n + 1) ^ (n ^ (n - 1)) + (n - 1) ^ (n ^ (n + 1)) := by

  -- clearly, both numbers ≠ 0
  -- to show divide relation,
  -- it suffices to show left prime factorization ≤ right.
  rw [← Nat.factorization_prime_le_iff_dvd (by simp) (by simp)]
  intro p pp
  simp only [Nat.factorization_def _ pp]

  -- n is odd, so suffices to consider p is odd case.
  by_cases hp: Even p
  · have: p = 2 := (Nat.Prime.even_iff pp).mp hp
    replace: padicValNat p (n^n) = 0 := by
      have oddn: Odd (n^n) := Odd.pow hn.left
      simp only [this, padicValNat.eq_zero_iff, OfNat.ofNat_ne_one,
      pow_eq_zero_iff', ne_eq, and_not_self,
      Nat.two_dvd_ne_zero, false_or]
      exact Nat.odd_iff.mp oddn
    simp [this]
  rw [Nat.not_even_iff_odd] at hp

  -- suffices to consider p divide n case.
  by_cases pdvd: ¬ p ∣ n
  · have: ¬ p ∣ n^n := by
      by_contra!
      absurd pdvd
      exact pp.dvd_of_dvd_pow this
    simp [padicValNat.eq_zero_of_not_dvd this]
  push_neg at pdvd

  -- rewrite (n-1)^(n^(n+1))
  have h1: (n-1)^(n^(n+1)) = ((n-1)^(n^2))^(n^(n-1)) := by
    simp only [← Nat.pow_mul]
    congr 1
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [h1]

  -- and to use LTE, we need prove p divide (n+1) + (n-1)^(n^2)
  have h2: n+1 + (n-1)^(n^2) ≡ 0 [MOD p] := by
    rw [← Int.natCast_modEq_iff]
    have: 1 ≤ n := by linarith only [hn.right]
    push_cast
    rw [Nat.cast_sub this]
    -- p divide n, so n+1 mod p is 1, n-1 mod p is -1.
    replace pdvd: n ≡ 0 [ZMOD p] := by
      zify at pdvd
      exact Dvd.dvd.modEq_zero_int pdvd
    have h2: n+1 ≡ 0 + 1 [ZMOD p] := pdvd.add rfl
    have h3: n-1 ≡ 0 - 1 [ZMOD p] := pdvd.sub rfl
    simp only [zero_add, zero_sub, Int.reduceNeg,
    Nat.cast_one] at h2 h3 ⊢
    replace h3: (n-1:ℤ)^(n^2) ≡ (-1)^(n^2) [ZMOD p] := h3.pow (n^2)
    have oddn: Odd (n^2) := Odd.pow hn.left
    rw [oddn.neg_one_pow] at h3
    replace := h2.add h3
    exact this.trans rfl
  replace h2: p ∣ n+1 + (n-1)^(n^2) := by
    exact Nat.dvd_of_mod_eq_zero h2
  have h3: ¬ p ∣ n+1 := by
    by_contra!
    replace: p ∣ 1 := (Nat.dvd_add_iff_right pdvd).mpr this
    simp only [Nat.dvd_one] at this
    norm_num [this] at pp

  -- use LTE
  have: Fact (Nat.Prime p) := by
    exact { out := pp }
  rw [padicValNat.pow_add_pow hp h2 h3 (Odd.pow hn.left)]

  -- left is n v_p(n), right is v_p(..) + (n-1) v_p(n)
  rw [padicValNat.pow n (by omega),
  padicValNat.pow (n-1) (by omega)]
  -- suffices to show v_p(..) ≥ v_p(n)
  suffices padicValNat p (n+1 + (n-1)^(n^2)) ≥ padicValNat p n by
    have h4: n = (n-1) + 1 := by omega
    nth_rw 1 [h4, add_one_mul]
    linarith only [this]

  -- and it follows from n divide ...
  have hdvd: n ∣ (n+1) + (n-1)^(n^2) := by
    rw [add_assoc]
    refine Nat.dvd_add dvd_rfl ?_
    zify
    rw [← Int.modEq_zero_iff_dvd]
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    have h4: (n-1) ≡ -1 [ZMOD n] := by
      have: (-1:ℤ) = 0 - 1 := rfl
      rw [this]
      apply Int.ModEq.sub ?_ rfl
      refine Dvd.dvd.modEq_zero_int dvd_rfl
    replace h4: (n-1)^(n^2) ≡ (-1)^(n^2) [ZMOD n] := h4.pow _
    rw [Odd.neg_one_pow hn.left.pow] at h4
    replace: 1 + (n-1)^(n^2) ≡ 1 + (-1) [ZMOD n] := by
      apply Int.ModEq.add rfl h4
    apply this.trans rfl
  rcases hdvd with ⟨k, hk⟩
  have knz: k ≠ 0 := by
    rintro rfl
    simp at hk
  rw [hk, padicValNat.mul (by omega) knz]
  simp