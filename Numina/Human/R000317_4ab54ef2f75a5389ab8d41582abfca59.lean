import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find all triples of prime numbers  $(p, q, r)$  such that  $p^q + p^r$  is a perfect square.-/
theorem number_theory_8905 {p q r : ℕ} (hpp : p.Prime) (hqp : q.Prime) (hrp : r.Prime) :
    IsSquare (p ^ q + p ^ r) ↔
    (p = 2 ∧ q = 5 ∧ r = 2) ∨
    (p = 2 ∧ q = 2 ∧ r = 5) ∨
    (p = 2 ∧ q = 3 ∧ r = 3) ∨
    (p = 3 ∧ q = 3 ∧ r = 2) ∨
    (p = 3 ∧ q = 2 ∧ r = 3) ∨
    (p = 2 ∧ Odd q ∧ Odd r ∧ q = r) := by
  -- To find all triples of prime numbers \((p, q, r)\) such that \(p^q + p^r\) is a perfect square, we start by assuming \(q \geq r\).
  wlog hrq : r ≤ q
  . have iff_of_le := this hpp hrp hqp (by linarith)
    have (h1 h2 h3 h4 h5 h6 h1' h2' h3' h4' h5' h6' : Prop) (H1 : h1 ↔ h2') (H2 : h2 ↔ h1')
        (H3 : h3 ↔ h3') (H4 : h4 ↔ h5') (H5 : h5 ↔ h4') (H6 : h6 ↔ h6') :
        (h1 ∨ h2 ∨ h3 ∨ h4 ∨ h5 ∨ h6) ↔ (h1' ∨ h2' ∨ h3' ∨ h4' ∨ h5' ∨ h6') := by
      rw [H1, H2, H3, H4, H5, H6]
      rw [← or_assoc, or_comm (a := h2'), or_assoc]
      repeat apply or_congr (Iff.refl _)
      rw [← or_assoc, or_comm (a := h5'), or_assoc]
    rw [Nat.add_comm, iff_of_le]
    apply this <;> apply and_congr (Iff.refl _) <;> rw [and_comm]
    rw [and_assoc]
    apply and_congr (Iff.refl _)
    rw [and_comm, eq_comm]
  constructor
  -- Verify solutions
  swap
  . rintro (h | h | h | h | h | h)
    -- Verify that (2,5,2) is solution.
    . rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
      use 6
    -- Verify that (2,2,5) is solution.
    . rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
      use 6
    -- Verify that (2,3,3) is solution.
    . rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
      use 4
    -- Verify that (3,3,2) is solution.
    . rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
      use 6
    . rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
      use 6
    -- Verify that (2,2n+1,2n+1) is solution.
    . rcases h with ⟨rfl, hq, hr, rfl⟩
      rcases hq with ⟨k, rfl⟩
      use 2 ^ (k + 1)
      ring
  . intro hpqr
    rcases le_or_lt r 2 with hr | hr
    --   1. **Assume \(r = 2\)**:
    --  \[ p^q + p^2 = x^2 \]
    replace hr : r = 2 := Nat.le_antisymm hr (Nat.Prime.two_le hrp)
    -- This gives us the equation:
    -- \[ p^q + p^r = p^r (p^{q-r} + 1) = x^2 \]
    rcases hpqr with ⟨k, hk⟩
    have : p ∣ k * k := by
      rw [← hk]
      refine Dvd.dvd.add ?_ ?_
      all_goals apply Dvd.dvd.pow (Nat.dvd_refl _) (by omega)
    have : p ∣ k := by
      rw [Nat.Prime.dvd_mul hpp] at this
      exact this.elim id id
    rcases this with ⟨y, hy⟩
    have : p^2 * (p^(q - 2) + 1) = p^2*y^2 := by
      rw [← mul_pow, ← hy, mul_add, ← pow_add, show 2+(q-2)=q by omega, mul_one]
      nth_rw 1 [← hr, pow_two]
      exact hk
    --  Dividing both sides by \(p^2\):
    --  \[ p^{q-2} + 1 = y^2 \]
    --  where \(y = \frac{x}{p}\). This implies:
    --  \[ p^{q-2} = (y-1)(y+1) \]
    have := Nat.mul_left_cancel (by have := Nat.Prime.two_le hpp; nlinarith) this
    have hyge2 : 2 ≤ y := by
      suffices y ≠ 0 ∧ y ≠ 1 by omega
      refine ⟨fun hy => ?_, fun hy => ?_⟩
      . rw [hy, zero_pow (by norm_num)] at this; omega
      apply_fun (· - 1) at this
      rw [hy, one_pow, Nat.add_sub_cancel, show 1-1=0 from rfl] at this
      have : p^(q-2) ≠ 0 := pow_ne_zero (q - 2) (by linarith [Nat.Prime.two_le hpp])
      contradiction
    apply_fun (· - 1) at this
    have hy_sq_sub_one : y^2-1=(y-1)*(y+1) := by
      zify
      rw [Nat.cast_sub, Nat.cast_pow, Nat.cast_sub]
      ring
      linarith
      nlinarith
    rw [Nat.add_sub_cancel, hy_sq_sub_one] at this
    rcases le_or_lt y 2 with hy2 | hy2
    --   2. **Case 1: \(y - 1 = 1\)**:
    --  \[ y = 2 \]
    replace hy2 : y = 2 := Nat.le_antisymm hy2 hyge2
    --  \[ p^{q-2} = 2 + 1 = 3 \]
    rw [hy2] at this
    norm_num at this
    --  This implies \(p = 3\) and \(q - 2 = 1\), so \(q = 3\). Therefore, one solution is:
    --  \[ (p, q, r) = (3, 3, 2) \]
    rcases le_or_lt q 2 with hq2 | hq2
    replace hq2 : q = 2 := Nat.le_antisymm hq2 (Nat.Prime.two_le hqp)
    rw [hq2] at this
    norm_num at this
    rw [show q-2=q-3+1 by omega, pow_succ] at this
    have hp3 : p = 3 := by
      rw [← Nat.prime_dvd_prime_iff_eq hpp (by norm_num)]
      use p^(q-3)
      rw [mul_comm, this]
    rw [hp3] at this
    have hq3 : q = 3 := by
      norm_num at this
      rw [← pow_zero 3] at this
      have := Nat.pow_right_injective (show 2 ≤ 3 by norm_num) this
      omega
    right; right; right; left
    split_ands <;> assumption
    --   3. **Case 2: \(y - 1 = p^a\) and \(y + 1 = p^b\)**:
    --  Solving \(p^b - p^a = 2\) for prime \(p\):
    have hy_sub1_dvd : y - 1 ∣ p^(q-2) := by use y + 1
    have hy_add1_dvd : y + 1 ∣ p^(q-2) := by use y - 1; rw [this]; ac_rfl
    obtain ⟨a, ha, hay⟩ := (Nat.dvd_prime_pow hpp).mp hy_sub1_dvd
    obtain ⟨b, hb, hby⟩ := (Nat.dvd_prime_pow hpp).mp hy_add1_dvd
    --  \[ p^b - p^a = 2 \]
    have hpb_eq_pa_add2 : p^b = p^a + 2 := by rw [← hay, ← hby]; omega
    --  - If \(p = 2\), then:
    have hp2 : p = 2 := by
      have hapos : 0 < a := by
        rw [Nat.pos_iff_ne_zero]
        intro ha0
        rw [ha0, pow_zero] at hay
        rw [show y = 2 by omega] at hy2
        norm_num at hy2
      have hbpos : 0 < b := by
        rw [Nat.pos_iff_ne_zero]
        intro hb0
        rw [hb0, pow_zero] at hby
        rw [show y = 0 by omega] at hy2
        norm_num at hy2
      apply_fun (· % p) at hpb_eq_pa_add2
      rw [show b = b - 1 + 1 by omega, show a = a - 1 + 1 by omega, pow_succ, pow_succ,
        Nat.mul_mod, Nat.add_mod, Nat.mul_mod _ p, Nat.mod_self] at hpb_eq_pa_add2
      norm_num at hpb_eq_pa_add2
      rw [← Nat.prime_dvd_prime_iff_eq hpp (by norm_num), Nat.dvd_iff_mod_eq_zero, hpb_eq_pa_add2]
    --    \[ 2^b - 2^a = 2 \]
    rw [hp2] at hpb_eq_pa_add2
    have h2a_le_2b : 2^a ≤ 2^b := by omega
    rw [Nat.pow_le_pow_iff_right (by norm_num)] at h2a_le_2b
    have h2b_sub_2a : 2^b - 2^a = 2 := by omega
    replace h2b_sub_2a : 2^a*(2^(b-a)-1) = 2 := by
      zify at h2b_sub_2a ⊢
      rw [Nat.cast_sub, Nat.cast_pow, mul_sub, show ((2 : ℕ) : ℤ) = (2 : ℤ) from rfl,
        ← pow_add, show a+(b-a)=b by omega]
      rw [Nat.cast_sub] at h2b_sub_2a
      convert h2b_sub_2a using 1
      push_cast
      ring
      rwa [Nat.pow_le_pow_iff_right (by norm_num)]
      change 0 < _
      exact Nat.pow_pos (by norm_num)
    --    \[ 2^a (2^{b-a} - 1) = 2 \]
    --    This implies \(a = 1\) and \(b = 2\), so:
    have ha1 : a = 1 := by
      have : 2^a ≤ 2^1 := by
        apply Nat.le_of_dvd (by norm_num)
        use 2^(b-a)-1
        rw [h2b_sub_2a, pow_one]
      rw [Nat.pow_le_pow_iff_right (by norm_num)] at this
      interval_cases a
      . rw [pow_zero] at hay
        rw [show y = 2 by omega] at hy2
        norm_num at hy2
      . rfl
    rw [ha1] at h2b_sub_2a
    norm_num at h2b_sub_2a
    have h2b : 2^(b-1) = 2^1 := by omega
    have hb2 := Nat.pow_right_injective (show 2 ≤ 2 by norm_num) h2b
    replace hb2 : b = 2 := by omega
    rw [hay, hby, hp2, ← pow_add, ha1, hb2] at this
    have hq_sub2 := Nat.pow_right_injective (show 2 ≤ 2 by norm_num) this
    --    \[ q - 2 = a + b = 1 + 2 = 3 \]
    --    \[ q = 5 \]
    have hq5 : q = 5 := by omega
    --    Therefore, another solution is:
    --    \[ (p, q, r) = (2, 5, 2) \]
    left
    split_ands <;> assumption
    -- 4. **General Case: \(q = r = 2n + 1\)**:
    rcases hpqr with ⟨k, hk⟩
    have : p ∣ k * k := by
      rw [← hk]
      refine Dvd.dvd.add ?_ ?_
      all_goals apply Dvd.dvd.pow (Nat.dvd_refl _) (by omega)
    have : p ∣ k := by
      rw [Nat.Prime.dvd_mul hpp] at this
      exact this.elim id id
    rcases this with ⟨y, hy⟩
    have hpr_mul_pqr : p^r*(p^(q-r)+1)=p^q+p^r := by
      rw [mul_add, ← pow_add, show r+(q-r)=q by omega, mul_one]
    have : Fact p.Prime := ⟨hpp⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : 2 ≤ p := Nat.Prime.two_le hpp
    have : k ≠ 0 := fun h => by
      have : 0 < p ^ q := by apply Nat.pow_pos; linarith
      have : 0 < p ^ r := by apply Nat.pow_pos; linarith
      have : 0 < p ^ q + p ^ r := by linarith
      rw [hk, h] at this
      norm_num at this
    have : p ^ r ≠ 0 := by
      rw [← Nat.pos_iff_ne_zero]
      apply Nat.pow_pos
      linarith
    by_cases hq_eq_r : q = r
    --  If \(q = r = 2n + 1\), then:
    --  \[ p^q + p^r = p^{2n+1} + p^{2n+1} = 2p^{2n+1} \]
    . have hoddr : Odd r := by apply Nat.Prime.odd_of_ne_two hrp; exact hr.ne'
      have hoddq : Odd q := by rwa [← hq_eq_r] at hoddr
      --  For \(2p^{2n+1}\) to be a perfect square, \(p\) must be 2:
      --  \[ 2 \cdot 2^{2n+1} = 2^{2n+2} \]
      have hp2 : p = 2 := by
        apply_fun (padicValNat p ·) at hk
        by_contra hpne2
        rw [hq_eq_r, ← two_mul, padicValNat.mul (by norm_num) (by assumption),
          padicValNat.pow _ (by linarith), padicValNat.self (by linarith),
          padicValNat.mul (by assumption) (by assumption), padicValNat_primes hpne2, zero_add, mul_one] at hk
        have : ¬Odd r := by
          rw [Nat.not_odd_iff_even]
          use padicValNat p k
        contradiction
      --  which is indeed a perfect square. Therefore, another family of solutions is:
    --  \[ (p, q, r) = (2, 2n+1, 2n+1) \]
      right; right; right; right; right
      split_ands <;> assumption
    have hp_q_sub_r_eq_zero : padicValNat p (p^(q-r)+1) = 0 := by
      rw [padicValNat.eq_zero_iff]
      right; right
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, show q - r = q - r - 1 + 1 by omega, pow_succ,
        Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt]
      norm_num
      exact Nat.Prime.two_le hpp
    qify at hp_q_sub_r_eq_zero
    rw [← hpr_mul_pqr] at hk
    apply_fun (padicValNat p ·) at hk
    qify at hk
    rw [padicValRat.mul (by assumption_mod_cast) (by norm_cast), Int.cast_add, hp_q_sub_r_eq_zero,
      padicValRat.pow (by norm_cast; linarith), padicValRat.mul (by assumption_mod_cast) (by assumption_mod_cast),
      padicValRat.self (by linarith)] at hk
    norm_cast at hk
    have : Even r := by use (padicValNat p k); rw [← hk, add_zero, mul_one]
    have : ¬Even r := by
      rw [Nat.not_even_iff_odd]
      apply Nat.Prime.odd_of_ne_two hrp
      omega
    contradiction
