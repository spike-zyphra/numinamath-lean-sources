import Mathlib

open Polynomial

/-let f(x) = x ^ 3 + 3 * x - 1 have roots a, b, c. Given that
1 / (a ^ 3 + b ^ 3) + 1 / (b ^ 3 + c ^ 3) + 1 / (c ^ 3 + a ^ 3)
can be written as m/n, where m,n are positive integers and gcd(m,n)=1, find 100m+n
-/
theorem algebra_610388 {a b c: ℂ} {m n: ℕ} {f: ℂ[X]} (hf: f = X ^ 3 + 3 * X - 1) (f_roots: f.roots = [a,b,c])
(h: 1 / (a ^ 3 + b ^ 3) + 1 / (b ^ 3 + c ^ 3) + 1 / (c ^ 3 + a ^ 3) = (m: ℂ) / n) (hmn: gcd m n = 1) (hn: n ≠ 0):
100 * m + n = 3989 := by

  -- we firstly prove 3d vieta's theorem, and give the sum of a, ab, abc --
  have f_eq: f = (X - C a) * (X - C b) * (X - C c) := by --factorize f --
    have h_monic : f.Monic := by
      have eq: f = X ^ 3 + (3 * X - 1) := by
        rw [hf]
        ring
      rw [eq]
      apply monic_X_pow_add
      simp
      have le: (3 * X + C (-1: ℂ)).degree ≤ 1 := by
        apply Polynomial.degree_linear_le
      have eq: 3 * X - 1 = 3 * X + C (-1: ℂ) := by
        simp
        ring
      rw [eq]
      calc
        (3 * X + C (-1: ℂ)).degree ≤ (1: WithBot ℕ) := by exact le
                                  _ < 3 := by norm_num
    have h_splits : Splits (algebraMap ℂ ℂ) f := by
      apply IsAlgClosed.splits_codomain  -- use the fundamental theorem of algebra --
    rw [Polynomial.eq_prod_roots_of_monic_of_splits_id h_monic h_splits]
    rw [f_roots]
    simp
    ring
  simp [hf] at f_eq
  have p: X ^ 3 + 3 * X - 1 - (X - C a) * (X - C b) * (X - C c) = 0 := by
    rw [f_eq]
    ring
  have p1: X ^ 3 + 3 * X - 1 - (X - C a) * (X - C b) * (X - C c)
   = C (a + b + c) * X ^ 2 + C (3 - (a * b + b * c + c * a)) * X + C (a * b * c - 1) := by
    rw [show C (a + b + c) = C a + C b + C c by simp]
    have o: C (3 - (a * b + b * c + c * a)) = 3 - (C a * C b + C b * C c + C c * C a) := by
      simp
      norm_cast
    rw [show C (a * b * c - 1) = C a * C b * C c - 1 by simp]
    rw [o]
    ring_nf
  rw [p1] at p
  clear p1 f_eq
  set g:= C (a + b + c) * X ^ 2 + C (3 - (a * b + b * c + c * a)) * X + C (a * b * c - 1) with hg
  clear_value g
  have eq_sum_a: a + b + c = 0 := by        -- compute a + b + c --
    by_contra! no
    rw [← Polynomial.leadingCoeff_eq_zero] at p
    have o: g.leadingCoeff = a + b + c := by
      rw [hg]
      apply Polynomial.leadingCoeff_quadratic
      exact no
    rw [←o] at no
    tauto
  rw [eq_sum_a] at hg
  rw [show C 0 * X ^ 2 + C (3 - (a * b + b * c + c * a)) * X + C (a * b * c - 1)
  = C (3 - (a * b + b * c + c * a)) * X + C (a * b * c - 1) by simp] at hg
  have eq_sum_ab: a * b + b * c + c * a = 3 := by   -- compute a * b + b * c + c * a --
    by_contra! no
    rw [← Polynomial.leadingCoeff_eq_zero] at p
    have o: g.leadingCoeff = 3 - (a * b + b * c + c * a) := by
      rw [hg]
      apply Polynomial.leadingCoeff_linear
      by_contra! i
      absurd no
      rw [show (3: ℂ) = 3 - 0 by norm_num]
      rw [← i]
      ring
    rw [p] at o
    absurd no
    rw [show (3: ℂ) = 3 - 0 by norm_num]
    rw [o]
    ring
  rw [eq_sum_ab] at hg
  rw [show C (3 - 3) * X + C (a * b * c - 1) = C (a * b * c - 1) by simp] at hg
  rw [hg] at p
  have eq_sum_abc: a * b * c = 1 := by  -- compute a * b * c --
    have i: g.coeff 0 = 0 := by
      rw [hg]
      rw [p]
      simp
    have j: g.coeff 0 = a * b * c - 1 := by
      rw [hg]
      apply Polynomial.coeff_C_zero
    rw [j] at i
    rw [show (1: ℂ) = 1 + 0 by norm_num]
    rw [← i]
    ring

-- Then we compute a ^ 3, b ^ 3, c ^ 3 --
  have eqa: f.eval a = 0 := by
    have o: a ∈ f.roots := by
      simp [f_roots]
    simp at o
    rcases o with ⟨o1, o2⟩
    exact o2
  have eqb: f.eval b = 0 := by
    have o: b ∈ f.roots := by
      simp [f_roots]
    simp at o
    rcases o with ⟨o1, o2⟩
    exact o2
  have eqc: f.eval c = 0 := by
    have o: c ∈ f.roots := by
      simp [f_roots]
    simp at o
    rcases o with ⟨o1, o2⟩
    exact o2
  simp [hf] at eqa eqb eqc
  replace eqa: a ^ 3 = -3 * a + 1 := by
    rw [show a ^ 3 = a ^ 3 - 0 by ring]
    rw [← eqa]
    ring
  replace eqb: b ^ 3 = -3 * b + 1 := by
    rw [show b ^ 3 = b ^ 3 - 0 by ring]
    rw [← eqb]
    ring
  replace eqc: c ^ 3 = -3 * c + 1 := by
    rw [show c ^ 3 = c ^ 3 - 0 by ring]
    rw [← eqc]
    ring

    -- now substitute a ^ 3, b ^ 3, c ^ 3 in the sum --
  simp [eqa, eqb, eqc] at h
  have eqsumc: -(3 * a) + 1 + (-(3 * b) + 1) = 2 - 3 * (a + b + c) + 3 * c := by ring
  have eqsuma: -(3 * b) + 1 + (-(3 * c) + 1) = 2 - 3 * (a + b + c) + 3 * a := by ring
  have eqsumb: -(3 * c) + 1 + (-(3 * a) + 1) = 2 - 3 * (a + b + c) + 3 * b := by ring
  have ane: 2 + 3 * a ≠ 0 := by
    by_contra! no
    replace no: a = -2 / 3 := by
      replace no: 3 * a = -2 := by
        rw [show 3 * a = 3 * a - 0 by ring]
        rw [← no]
        ring
      rw [show a = 3 * a / 3 by ring]
      rw [no]
    simp [no] at eqa
    absurd eqa
    norm_num
  have bne: 2 + 3 * b ≠ 0 := by
    by_contra! no
    replace no: b = -2 / 3 := by
      replace no: 3 * b = -2 := by
        rw [show 3 * b = 3 * b - 0 by ring]
        rw [← no]
        ring
      rw [show b = 3 * b / 3 by ring]
      rw [no]
    simp [no] at eqb
    absurd eqb
    norm_num
  have cne: 2 + 3 * c ≠ 0 := by
    by_contra! no
    replace no: c = -2 / 3 := by
      replace no: 3 * c = -2 := by
        rw [show 3 * c = 3 * c - 0 by ring]
        rw [← no]
        ring
      rw [show c = 3 * c / 3 by ring]
      rw [no]
    simp [no] at eqc
    absurd eqc
    norm_num
  simp [eq_sum_a] at eqsumc eqsuma eqsumb
  simp [eqsuma, eqsumb,eqsumc] at h

  -- now we simply the sum using equations derived from Vieta's theorem --
  have bigne: 8 + 27 * a * b * c + 12 * (a + b + c) + 18 * (a * b + b * c + c * a) ≠ 0 := by
      rw [show 27 * a * b * c = 27 * (a * b * c) by ring]
      simp [eq_sum_abc, eq_sum_a, eq_sum_ab]
      norm_num
  have simp1: (2 + 3 * c)⁻¹ + (2 + 3 * a)⁻¹ + (2 + 3 * b)⁻¹
  = (12 + 12 * (a + b + c) + 9 * (a * b + b * c + c * a)) / (8 + 27 * a * b * c + 12 * (a + b + c) + 18 * (a * b + b * c + c * a)) := by
    field_simp
    ring
  rw [simp1] at h
  clear simp1
  simp [eq_sum_a, eq_sum_ab, eq_sum_abc] at h
  rw [show 27 * a * b * c = 27 * (a * b * c) by ring] at h
  simp [eq_sum_abc] at h
  rw [show ((12: ℂ) + 9 * 3) / (8 + 27 + 18 * 3) = 39 / 89 by norm_num] at h
  have eqmn: (39: ℂ) * n = 89 * m := by
    calc
      (39: ℂ) * n = 39 / 89 * 89 * n := by norm_num
                 _= m / n * 89 * n := by rw [h]
                 _= m * 89 := by field_simp [hn]
                 _= 89 * m := by ring
  norm_cast at eqmn
  clear * - eqmn hmn hn

  -- finally, we use eqmn and hmn to derive m and n --
  have dvd1: 39 ∣ m := by
    have o: 39 ∣ 89 * m := by omega
    apply Nat.Coprime.dvd_of_dvd_mul_left at o
    exact o
    norm_num
  apply Nat.le_of_dvd at dvd1
  have dvd2: m ∣ 39 := by
    have o: m ∣ 39 * n := by rw [eqmn]; apply Nat.dvd_mul_left
    apply Nat.Coprime.dvd_of_dvd_mul_right at o
    exact o
    rw [Nat.coprime_iff_gcd_eq_one]
    exact hmn
  apply Nat.le_of_dvd at dvd2
  have m_val: m = 39 := by omega
  simp [m_val] at eqmn
  replace eqmn: n = 89 := by omega
  omega
  omega
  omega