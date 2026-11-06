import Mathlib


/- Let $m$ be a positive integer. Let $N_m$ be the integer defined by the sum $N_m = 1 \cdot (10^3)^{m-1} + 2 \cdot (10^3)^{m-2} + \dots + (m-1) \cdot 10^3 + m$. (For example, if $m=3$, $N_3=1002003$. If $m=9$, then $N_9=1002003004005006007008009$.)
Let $d$ be a positive integer that is a divisor of $1001$. Compute the remainder when $N_m$ is divided by $d$. Show that this remainder is equal to the value $R$, where $R$ is the remainder of $\lceil m/2 \rceil$ when divided by $d$. -/
theorem number_theory_640769 (N : ℕ → ℕ) (d : ℕ) (hd : 0 < d)
  (hN : ∀ m, 0 < m → N m = ∑ i ∈ Finset.Icc 1 m, i * (10^3)^(m-i))
  (hdvd : d ∣ 1001) :
  ∀(m:ℕ), 0 < m → N m ≡ ⌈(m/2:ℚ)⌉₊ [MOD d] := by

  -- first, consider N m mod 1000.
  have h1 (m:ℕ) (hm: 0 < m):
    N (m+1) = 1000 * (N m) + m+1 := by
    induction' m,hm using Nat.le_induction with m hm ih
    · simp [hN, Finset.sum_Icc_succ_top]
    · rw [hN (m+1+1) (by simp), Finset.sum_Icc_succ_top (by simp)]
      have: ∑ i ∈ Finset.Icc 1 (m+1), i*(10^3)^(m+1+1-i) =
        10^3 * N (m+1) := by
        rw [hN (m+1) (by simp), Finset.mul_sum]
        apply Finset.sum_congr rfl ?_
        intro i hi
        rw [mul_comm (10^3) _, mul_assoc]
        congr 1
        rw [← pow_succ]
        congr 1
        simp only [Finset.mem_Icc] at hi
        omega
      rw [this, ih]
      simp only [Nat.reducePow, tsub_self, pow_zero, mul_one]
      ring

  -- therefore it mod 1001 is m+1 - (N m)
  have h2 (m:ℕ) (hm: 0 < m):
    N (m+1) ≡ (m+1) - N m [ZMOD 1001] := by
    rw [h1 m hm, add_assoc]
    push_cast
    have hh1: 1000 * (N m) ≡ (-1) * (N m) [ZMOD 1001] := by
      apply Int.ModEq.mul ?_ rfl
      rfl
    have hh2: m+1 ≡ m+1 [ZMOD 1001] := rfl
    refine (hh1.add hh2).trans ?_
    ring_nf
    rfl

  -- we guess it is ceil m/2. let's verify:
  have h3 (m:ℕ) (hm: 0 < m): N m ≡ ⌈(m/2:ℚ)⌉₊ [ZMOD 1001] := by
    induction' m,hm using Nat.le_induction with m hm ih
    · simp only [Nat.succ_eq_add_one, zero_add, Nat.cast_one]
      have: ⌈(1/2:ℚ)⌉₊ = 1 := by
        rw [Nat.ceil_eq_iff (by norm_num)]
        norm_num
      simp only [zero_lt_one, hN, Finset.Icc_self, Nat.reducePow,
      Finset.sum_singleton, tsub_self, pow_zero, mul_one,
      Nat.cast_one, this, Int.ModEq.refl]
    · specialize h2 m hm
      refine h2.trans ?_
      have: m+1 ≡ m+1 [ZMOD 1001] := rfl
      replace := this.sub ih
      refine this.trans ?_
      congr 1
      rcases (Nat.even_or_odd' m) with ⟨k, hk⟩
      rcases hk with keq | keq
      · rw [keq]
        push_cast
        suffices ⌈(2*k+1:ℚ)/2⌉₊ = k+1 by
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          mul_div_cancel_left₀, Nat.ceil_natCast, this]
          push_cast
          ring
        rw [Nat.ceil_eq_iff (by simp)]
        push_cast
        constructor <;> linarith only
      · rw [keq]
        push_cast
        have hh1: ⌈(2*k+1:ℚ)/2⌉₊ = k+1 := by
          rw [Nat.ceil_eq_iff (by simp)]
          push_cast
          constructor <;> linarith only
        have hh2: ⌈(2*k+1+1:ℚ)/2⌉₊ = k+1 := by
          have: (2*k+1+1:ℚ)/2 = ↑(k+1:ℕ) := by
            push_cast
            ring
          rw [this]
          rfl
        rw [hh1, hh2]
        push_cast
        ring
  replace h3 (m:ℕ) (hm: 0 < m): N m ≡ ⌈(m/2:ℚ)⌉₊ [MOD 1001] := by
    specialize h3 m hm
    exact Int.natCast_modEq_iff.mp h3

  -- so answer is ceil (m/2).
  have h41: 1001 = d * (1001/d) := by
    exact Eq.symm (Nat.mul_div_cancel' hdvd)
  intro m hm
  rw [h41] at h3
  specialize h3 m hm
  exact Nat.ModEq.of_mul_right (1001 / d) h3