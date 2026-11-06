import Mathlib


/-
For positive integers  $n,a,b$ , if  $n=a^2 +b^2$ , and  $a$  and  $b$  are coprime, then the number pair  $(a,b)$  is called a *square split* of  $n$  (the order of  $a, b$  does not count). Prove that for any positive  $k$ , there are only two square splits of the integer  $13^k$ .
-/
theorem number_theory_8477
    (is_square_split : ℕ → ℕ → ℕ → Prop)
    (h_issquaresplit : ∀ n a b, is_square_split n a b = (a > 0 ∧ b > 0 ∧ a > b ∧ a.Coprime b ∧ n = a ^ 2 + b ^ 2))
    (k : ℕ) (hk : k > 0)
    (a b c d : ℕ)
    (hssab : is_square_split (13 ^ k) a b)
    (hsscd : is_square_split (13 ^ k) c d) :
    a = c ∧ b = d := by

  -- auxiliary lemma of AM-GM inequality
  have l_amgm (a b : ℝ) : a * b < (a ^ 2 + b ^ 2) / 2 ∨ (a = b ∧ a * b = (a ^ 2 + b ^ 2) / 2) := by
    rcases eq_or_ne a b with h | h
    . right
      simp_all [h, pow_two]
    left
    have t1 : 0 < a ^ 2 + b ^ 2 - 2 * a * b := by
      rw [show a ^ 2 + b ^ 2 - 2 * a * b = (a - b) ^ 2 by ring]
      apply lt_of_le_of_ne (sq_nonneg (a - b)) (pow_ne_zero 2 (sub_ne_zero_of_ne h)).symm
    apply half_pos at t1
    rw [show (a ^ 2 + b ^ 2 - 2 * a * b) / 2 = (a ^ 2 + b ^ 2) / 2 - a * b by field_simp; ring] at t1
    have : 0 + a * b < ((a ^ 2 + b ^ 2) / 2 - a * b) + a * b := by
      exact (add_lt_add_iff_right (a * b)).mpr t1
    rw [sub_add_cancel, zero_add] at this
    exact this

  rw [h_issquaresplit] at hssab hsscd
  obtain ⟨hapos, _, hagtb, habcop, hab⟩ := hssab
  obtain ⟨hcpos, _, hcgtd, hcdcop, hcd⟩ := hsscd
  set n := 13 ^ k

  -- $a^2\equiv -b^2 \pmod{13^k}$
  have r1 : a ^ 2 ≡ - b ^ 2 [ZMOD n] := by
    have : a ^ 2 + b ^ 2 ≡ 0 [ZMOD n] := by
      zify at hab
      rw [← hab]
      exact Int.emod_self
    rw [← Int.add_sub_cancel ((a:ℤ) ^ 2) (b ^ 2), ← Int.zero_sub ((b:ℤ) ^ 2)]
    exact Int.ModEq.sub this rfl

  -- $c^2 \equiv -d^2 \pmod{13^k}$
  have r2 : c ^ 2 ≡ - d ^ 2 [ZMOD n] := by
    have : c ^ 2 + d ^ 2 ≡ 0 [ZMOD n] := by
      zify at hcd
      rw [← hcd]
      exact Int.emod_self
    rw [← Int.add_sub_cancel ((c:ℤ) ^ 2) (d ^ 2), ← Int.zero_sub ((d:ℤ) ^ 2)]
    exact Int.ModEq.sub this rfl

  -- $a^2c^2 \equiv b^2d^2 \pmod{13^k}$
  have r3 : a ^ 2 * c ^ 2 ≡ b ^ 2 * d ^ 2 [ZMOD n] := by
    rw [show (b:ℤ) ^ 2 * d ^ 2 = (- b ^ 2) * (- d ^ 2) by ring]
    exact Int.ModEq.mul r1 r2

  -- $13^k \mid (ac-bd)(ac+bd)$
  have r4 : n ∣ (a * c - b * d) * (a * c + b * d) := by
    have : (a * c - b * d) * (a * c + b * d) = a ^ 2 * c ^ 2 - b ^ 2 * d ^ 2 := by
      have : a * c > b * d := Nat.mul_lt_mul_of_lt_of_lt hagtb hcgtd
      rw [← Nat.mul_pow, ← Nat.mul_pow]
      zify
      rw [Nat.cast_sub, Nat.cast_sub, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_mul, Nat.cast_mul]
      ring
      exact Nat.le_of_succ_le (Nat.pow_lt_pow_left this (show 2 ≠ 0 by norm_num))
      exact Nat.le_of_succ_le this
    rw [this]
    zify
    rw [Nat.cast_sub, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow]
    have t := Int.ModEq.dvd (Int.ModEq.symm r3)
    simp only [n, Nat.cast_pow] at t
    exact t
    have : b ^ 2 * d ^ 2 = (b * d) ^ 2 := by
      exact Eq.symm (Nat.mul_pow b d 2)
    rw [← Nat.mul_pow, ← Nat.mul_pow]
    exact Nat.le_of_succ_le (Nat.pow_lt_pow_left (Nat.mul_lt_mul_of_lt_of_lt hagtb hcgtd) (show 2 ≠ 0 by norm_num))

  -- If  $13 \mid ac-bd$  and  $13 \mid ac+bd$  then  $13\mid 2ac$  - contradiction.
  have r5 : ¬ 13 ∣ (a * c - b * d) ∨ ¬ 13 ∣ (a * c + b * d) := by
    by_contra! h
    obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ := h
    have t1 : a * c * 2 = 13 * (p1 + p2) := by
      have : a * c - b * d + a * c + b * d = 13 * p1 + 13 * p2 := by linarith
      rw [mul_add, ← this]
      zify
      rw [Nat.cast_sub, Nat.cast_mul, Nat.cast_mul]
      ring
      apply mul_le_mul'
      all_goals linarith
    have t2 : 13 ∣ a * c * 2 := by
      exact Dvd.intro (p1 + p2) (id (Eq.symm t1))
    have t3 : 13 ∣ a * c := by
      exact Nat.Coprime.dvd_of_dvd_mul_right (show Nat.Coprime 13 2 by norm_num) t2
    have t4: 13 ∣ a ∨ 13 ∣ c := by
      refine (Nat.Prime.dvd_mul (by norm_num)).mp t3
    rcases t4 with hadvd | hcdvd
    . show False
      -- if 13 ∣ a , then 13 ∣ b as 13 ∣ a ^ 2 + b ^ 2, then contradicts to 'a is coprime with b'.
      have hbdvd : 13 ∣ b := by
        have : 13 ∣ b ^ 2 := by
          have hdvd1 : 13 ∣ n := dvd_pow_self 13 (by linarith)
          have hdvd2 : 13 ∣ a ^ 2 := dvd_pow hadvd (by linarith)
          rw [show b ^ 2 = n - a ^ 2 by omega]
          exact Nat.dvd_sub' hdvd1 hdvd2
        apply Nat.Prime.dvd_of_dvd_pow (show Nat.Prime 13 by norm_num) this
      rw [Nat.coprime_iff_gcd_eq_one] at habcop
      have : 13 ∣ a.gcd b := by
        exact Nat.dvd_gcd hadvd hbdvd
      rw [habcop] at this
      contradiction
    . show False
      -- if 13 ∣ c , then 13 ∣ d as 13 ∣ c ^ 2 + d ^ 2, then contradicts to 'c is coprime with d'.
      have hddvd : 13 ∣ d := by
        have : 13 ∣ d ^ 2 := by
          have hdvd1 : 13 ∣ n := dvd_pow_self 13 (by linarith)
          have hdvd2 : 13 ∣ c ^ 2 := dvd_pow hcdvd (by linarith)
          rw [show d ^ 2 = n - c ^ 2 by omega]
          exact Nat.dvd_sub' hdvd1 hdvd2
        apply Nat.Prime.dvd_of_dvd_pow (show Nat.Prime 13 by norm_num) this
      rw [Nat.coprime_iff_gcd_eq_one] at hcdcop
      have : 13 ∣ c.gcd d := Nat.dvd_gcd hcdvd hddvd
      rw [hcdcop] at this
      contradiction

  -- So,  $13^k \mid ac+bd$  or  $13^k \mid ac-bd$
  have r6 : n ∣ (a * c - b * d) ∨ n ∣ (a * c + b * d) := by
    rcases r5 with h | h
    . have : n.Coprime (a * c - b * d) := by
        simp only [n]
        apply Nat.Coprime.pow_left k
        exact (Nat.Prime.coprime_iff_not_dvd (show Nat.Prime 13 by norm_num)).mpr h
      right
      exact Nat.Coprime.dvd_of_dvd_mul_left this r4
    . have : n.Coprime (a * c + b * d) := by
        simp only [n]
        apply Nat.Coprime.pow_left k
        exact (Nat.Prime.coprime_iff_not_dvd (show Nat.Prime 13 by norm_num)).mpr h
      left
      exact Nat.Coprime.dvd_of_dvd_mul_right this r4

  -- $ac+bd < \frac{a^2+c^2}{2}+\frac{b^2+d^2}{2}=\frac{a^2+b^2+c^2+d^2}{2}=13^k$
  have ineq1 : a * c + b * d < n ∨ (a = c ∧ b = d ∧ a * c + b * d = n) := by
    have ac_amgm := l_amgm a c
    have bd_amgm := l_amgm b d
    have t1 : ((a:ℝ) ^ 2 + c ^ 2) / 2 + (b ^ 2 + d ^ 2) / 2 = n := by
      rify at hab
      rify at hcd
      rw [show (n:ℝ) = n * 2 / 2 by field_simp, mul_two]
      conv => rhs; enter [1, 1]; rw [hab]
      conv => rhs; enter [1, 2]; rw [hcd]
      ring

    rify; rw [← t1]
    rcases ac_amgm with hac | ⟨_, hac⟩
    . left;
      rcases bd_amgm with h | ⟨_, h⟩
      . exact add_lt_add hac h
      . exact add_lt_add_of_lt_of_le hac (le_of_eq h)

    rcases bd_amgm with hbd | ⟨_, hbd⟩
    . left; exact add_lt_add_of_le_of_lt (le_of_eq hac) hbd
    right
    simp_all

  have ineq2 : n ≤ a * c + b * d := by
    rcases r6 with h | h
    . apply Nat.le_trans _ (show a * c - b * d ≤ a * c + b * d by omega)
      -- n ≤ a * c - b * d
      obtain ⟨t, htn⟩ := h
      have hne : a * c - b * d ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr (Nat.mul_lt_mul_of_lt_of_lt hagtb hcgtd)
      rcases Nat.eq_zero_or_pos t with ht | ht
      . simp_all
      have : a * c - b * d ≥ n * 1 := by
        rw [htn]
        exact Nat.mul_le_mul_left n ht
      linarith
    . obtain ⟨t, htn⟩ := h
      have hne : a * c + b * d ≠ 0 := Nat.ne_of_gt (Nat.add_pos_left (Nat.mul_pos hapos hcpos) (b * d))
      rcases Nat.eq_zero_or_pos t with ht | ht
      . simp_all
      have : a * c + b * d ≥ n * 1 := by
        rw [htn]
        exact Nat.mul_le_mul_left n ht
      linarith

  -- so a = c and b = d, there's only one possible solution
  rcases ineq1 with h | ⟨h1, h2, _⟩
  . linarith
  exact ⟨h1, h2⟩
