import Mathlib


/- 4. Determine all pairs of positive integers $(a, n)$ with $a \geq n \geq 2$ for which the number $(a+1)^{n}+a-1$ is a power of 2. -/
theorem number_theory_137992 (a n : ℕ) (ha : 2 ≤ n) (hn : n ≤ a)
    (h : ∃ k, (a + 1)^n + a - 1 = 2^k) :
    (a = 4 ∧ n = 3) := by

  -- use binomial theorem, expand (a+1)^n
  have heq := add_pow a 1 n
  -- single out first three terms from expansion of (a+1)^n
  replace heq: (a+1)^n = (∑ i ∈ Finset.Ico 3 (n+1),
    a^i * 1^(n-i) * n.choose i) +
    (n.choose 2)*a^2 + n*a + 1 := by
    rw [heq, Finset.range_eq_Ico]
    zify
    have h1: 2 < n+1 := by omega
    have h2: 1 < n+1 := by omega
    have h3: 0 < n+1 := by omega
    simp only [← Finset.sum_Ico_sub_bot, h1, h2, h3]
    simp only [Nat.Ico_zero_eq_range, one_pow, mul_one, pow_zero,
    tsub_zero, Nat.choose_zero_right, Nat.cast_one, pow_one, Nat.choose_one_right]
    ring
  -- thus (a+1)^n + a - 1 = ...a^3 + ..a^2 + (n+1)a
  replace heq: (a+1)^n + a - 1 = (∑ i ∈ Finset.Ico 3 (n+1),
    a^i * 1^(n-i) * n.choose i) + (n.choose 2)*a^2 + (n+1)*a := by
    rw [heq]
    simp only [one_pow, mul_one, Nat.succ_add_sub_one]
    ring

  -- it's a 2-power, a divide this, so a also 2-power.
  obtain ⟨b,hab⟩: ∃ b:ℕ, a = 2^b := by
    have: a ∣ (a+1)^n + a - 1 := by
      rw [heq]
      have h1: a ∣ (∑ i ∈ Finset.Ico 3 (n+1),
        a^i * 1^(n-i) * n.choose i) := by
        apply Finset.dvd_sum (fun i hi => ?_)
        apply Dvd.dvd.mul_right
        simp only [one_pow, mul_one]
        simp only [Finset.mem_Ico] at hi
        refine dvd_pow_self a (by omega)
      have h2: a ∣ (n.choose 2) * a^2 := by
        apply Dvd.dvd.mul_left
        exact Dvd.intro_left (a.pow 1) rfl
      apply Dvd.dvd.add (h1.add h2) ?_
      exact Nat.dvd_mul_left a (n + 1)
    rcases h with ⟨i,hi⟩
    rw [hi, Nat.dvd_prime_pow (by norm_num)] at this
    tauto

  -- let (a+1)^n+a-1 be 2^c, we claim c > 2b
  obtain ⟨c,hc⟩ := h
  have hbc: c > 2*b := by
    have h1: (a+1)^n+a-1 ≥ (a+1)^2+a-1 := by
      rw [Nat.add_sub_assoc (by omega), Nat.add_sub_assoc (by omega)]
      simp only [ge_iff_le, add_le_add_iff_right]
      apply (Nat.pow_le_pow_iff_right (by omega)).mpr ha
    have h2: (a+1)^2 + a - 1 > a^2 := by
      simp only [pow_two, Nat.add_one_mul, Nat.mul_add_one]
      rw [Nat.add_sub_assoc (by omega)]
      simp [add_assoc]
    have h3: 2^c > 2^(2*b) := by
      rw [mul_comm 2 b, Nat.pow_mul, ← hab, ← hc]
      apply lt_of_lt_of_le h2 h1
    apply (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3

  -- therefore a^2 divide ..a^3 + ..a^2 + (n+1)a, it follows that a divide n+1.
  have hdvd: a^2 ∣ (n+1)*a := by
    have h1: a^2 ∣ (a+1)^n+a-1 := by
      rw [hc, hab, ← Nat.pow_mul, mul_comm b 2]
      exact Nat.pow_dvd_pow 2 hbc.le
    have h2: a^2 ∣ ∑ i ∈ Finset.Ico 3 (n+1),
      a^i * 1^(n-i) * n.choose i := by
      apply Finset.dvd_sum (fun i hi => ?_)
      apply Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
      simp only [Finset.mem_Ico] at hi
      refine Nat.pow_dvd_pow a (by omega)
    rw [heq] at h1
    have h3 := h2.add (Nat.dvd_mul_left (a^2) (n.choose 2))
    exact (Nat.dvd_add_iff_right h3).mpr h1
  rw [pow_two] at hdvd
  replace hdvd: a ∣ (n+1) :=
    Nat.dvd_of_mul_dvd_mul_right (by omega) hdvd

  -- since 2 ≤ n ≤ a, for a divide n+1, it forces n+1 = a
  have hna: n+1 = a := by
    rcases hdvd with ⟨m,hm⟩
    have h1: m < 2 := by
      by_contra!
      replace: n+1 ≥ 2*n := by
        rw [hm]
        replace: a*m ≥ a*2 := Nat.mul_le_mul_left a this
        apply le_trans ?_ this
        rw [mul_comm 2 n]
        exact Nat.mul_le_mul_right 2 hn
      linarith only [this, ha]
    have h2: 0 < m := by
      by_contra!
      replace: m = 0 := Nat.eq_zero_of_le_zero this
      simp [this] at hm
    have: m = 1 := by omega
    rw [hm, this, mul_one]

  -- b > 1, otherwise n = 1, contradiction.
  have hb: b ≥ 2 := by
    by_contra!
    replace: b ≤ 1 := by omega
    rw [hab] at hna
    replace: n+1 ≤ 2 := by
      rw [hna]
      nth_rw 2 [← pow_one 2]
      refine Nat.pow_le_pow_right (by norm_num) this
    linarith only [ha, this]

  -- then we claim c > 3b
  replace hbc: c > 3*b := by
    -- then n+1 ≥ 4, n ≥ 3
    have nge: n ≥ 3 := by
      have: a ≥ 2^2 := by
        rw [hab]
        exact Nat.pow_le_pow_right (by norm_num) hb
      rw [← hna] at this
      linarith only [this]
    -- (a+1)^n + a - 1 > (a+1)^n > a^3
    have h1: (a+1)^n + a - 1 > (a+1)^n := by
      rw [Nat.add_sub_assoc (by omega)]
      simp only [gt_iff_lt, lt_add_iff_pos_right, tsub_pos_iff_lt]
      omega
    have h2: (a+1)^n > a^n := by
      exact Nat.pow_lt_pow_left (by simp) (by omega)
    have h3: a^n ≥ a^3 := by
      exact Nat.pow_le_pow_right (by omega) nge
    have h4: 2^c > 2^(3*b) := by
      rw [← hc, mul_comm 3 b, Nat.pow_mul, ← hab]
      apply lt_of_le_of_lt h3 (h2.trans h1)
    apply (Nat.pow_lt_pow_iff_right (by norm_num)).mp h4

  -- therefore a^3 divide ..a^2 + (n+1)a
  replace hdvd: a^3 ∣ (n.choose 2 + 1) * a^2 := by
    have: a^3 ∣ 2^c := by
      rw [hab, ← Nat.pow_mul, mul_comm b 3]
      exact Nat.pow_dvd_pow 2 hbc.le
    rw [← hc, heq, hna, ← pow_two,
    add_assoc, ← add_one_mul _ (a^2)] at this
    refine (Nat.dvd_add_iff_right ?_).mpr this
    apply Finset.dvd_sum (fun i hi => ?_)
    simp only [Finset.mem_Ico] at hi
    apply Dvd.dvd.mul_right
    simp only [one_pow, mul_one, Nat.pow_dvd_pow a hi.left]
  replace hdvd: a ∣ n.choose 2 + 1 := by
    have: a^3 = a * a^2 := by ring
    rw [this] at hdvd
    apply Nat.dvd_of_mul_dvd_mul_right ?_ hdvd
    apply Nat.pow_pos (by omega)


  -- simplify n.choose 2 + 1
  have: n.choose 2 + (1:ℤ) = 2^(2*b-1) - 2^b - 2^(b-1) + 2 := by
    rw [Nat.choose_two_right]
    push_cast
    rw [Nat.cast_sub (by omega)]
    zify at hna
    replace hna: n = (a:ℤ) - 1 := by linarith only [hna]
    rw [hna, hab]
    push_cast
    have h1: (2^b-1:ℤ)*(2^b-1-1)/2 = (2^b-1) * (2^(b-1)-1) := by
      qify
      have: (2:ℤ) ∣ 2^b-1-1 := by
        simp only [sub_sub, Int.reduceAdd, dvd_sub_self_right]
        refine dvd_pow_self 2 (by omega)
      rw [Int.cast_div (this.mul_left _) (by norm_num)]
      field_simp
      ring_nf
      have: 1 ≤ b := by omega
      simp only [← pow_succ, mul_assoc, Nat.sub_add_cancel this]
      simp only [pow_succ]
      ring
    have h2: 2*b-1 = b + (b-1) := by omega
    rw [h1, h2]
    ring
  rw [hab] at hdvd
  zify at hdvd
  rw [this] at hdvd

  -- cannot be the case b > 2, otherwise 2^b divide 2-2^(b-1)
  have hb': b < 3 := by
    by_contra! hb
    replace: (2:ℤ)^(2*b-1) - 2^b - 2^(b-1) + 2
      = 2^b * (2^(b-1) - 1) + (2 - 2^(b-1)) := by
      have: 2*b-1 = b + (b-1) := by omega
      rw [this]
      ring
    rw [this] at hdvd
    replace: (2:ℤ)^b ∣ 2 - 2^(b-1) := by
      refine (Int.dvd_iff_dvd_of_dvd_add hdvd).mp ?_
      exact Int.dvd_mul_right (2 ^ b) (2 ^ (b - 1) - 1)
    -- but that's impossible.
    replace: (2:ℤ)^b ∣ 2^(b-1) - 2 := by
      have hh: (2:ℤ)^(b-1) - 2 = - (2 - 2^(b-1)) := by ring
      rw [hh]
      exact Int.dvd_neg.mpr this
    have h1: (2:ℤ)^1 < 2^(b-1) := by
      apply (pow_lt_pow_iff_right₀ (by norm_num)).mpr (by omega)
    have h2: (2:ℤ)^b > 2^(b-1) := by
      apply (pow_lt_pow_iff_right₀ (by norm_num)).mpr (by omega)
    replace := Int.le_of_dvd (by linarith only [h1]) this
    linarith only [h2, this]

  -- therefore we have b = 2
  have beq: b = 2 := by omega

  -- so a = 4, n = 3
  rw [beq] at hab
  constructor <;> linarith only [hab, hna]