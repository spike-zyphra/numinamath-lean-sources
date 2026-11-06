import Mathlib

/- Find all couples of non-zero integers  $(x,y)$  such that,  $x^2+y^2$  is a common divisor of  $x^5+y$  and  $y^5+x$ .-/
theorem number_theory_8864 :
    {(x, y) : ℤ × ℤ | x ≠ 0 ∧ y ≠ 0 ∧ (x^2 + y^2) ∣ (x^5 + y) ∧ (x^2 + y^2) ∣ (y^5 + x)} =
    {(-1, -1), (-1, 1), (1, -1), (1, 1)} := by
  ext z
  simp [-ne_eq]
  set x := z.1
  set y := z.2
  rw [show z = (x, y) from rfl, show (1 : ℤ × ℤ) = (1, 1) from rfl]
  constructor
  swap
  -- Verify that (x,y)=(-1,-1),(-1,1),(1,-1),(1,1) are solutions.
  . rintro (h | h | h | h)
    all_goals
      rw [Prod.ext_iff] at h
      rcases h with ⟨hx, hy⟩
      change x = _ at hx
      change y = _ at hy
      rw [hx, hy]
      norm_num
  rintro ⟨hx, hy, hxy1, hxy2⟩
  -- Let d = gcd(x,y). We prove that $d | y / d$.
  have gcd_dvd (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy1 : x^2+y^2 ∣ x^5+y) (_ : x^2+y^2 ∣ y^5+x) :
      ↑(x.gcd y) ∣ y / x.gcd y := by
    obtain ⟨a, ha⟩ : ↑(x.gcd y) ∣ x := Int.gcd_dvd_left
    obtain ⟨b, hb⟩ : ↑(x.gcd y) ∣ y := Int.gcd_dvd_right
    set d := x.gcd y
    have hd : (d : ℤ) ≠ 0 := gcd_ne_zero_of_right hy
    have : (d : ℤ) ^ 2 ∣ x ^ 2 + y ^ 2 := by
      apply Dvd.dvd.add
      . rw [Int.pow_dvd_pow_iff (by norm_num)]
        exact Int.gcd_dvd_left
      . rw [Int.pow_dvd_pow_iff (by norm_num)]
        exact Int.gcd_dvd_right
    have := Int.dvd_trans this hxy1
    rw [ha, hb, show (d : ℤ) ^ 2 = d * d by ring,
      show _ + _ * b = (d : ℤ) * (d ^ 4 * a ^ 5 + b) by ring] at this
    rcases this with ⟨u, hu⟩
    have : (d : ℤ) ∣ d ^ 4 * a ^ 5 + b := by
      use u
      rw [← mul_left_inj' hd]
      linear_combination hu
    --  $x^5+y=d(a^5d^4+b)\implies d^2\mid d(a^5d^4+b)\implies d\mid b$
    have := Dvd.dvd.sub this (Dvd.dvd.mul_left (Int.dvd_refl d) (d ^ 3 * a ^ 5))
    ring_nf at this
    rw [hb]
    convert this
    field_simp
  -- It's obvious that gcd(x,y) is positive since x,y are nonzero.
  have gcd_xy_pos : 0 < x.gcd y := by
    rw [Nat.pos_iff_ne_zero]
    zify
    exact gcd_ne_zero_of_right hy
  -- Combine $d | y / d$ and $d | x / d$, we have $d | gcd(x/d,y/d)$.
  have gcd_xy_dvd : (x.gcd y : ℤ) ∣ Int.gcd (x / x.gcd y) (y / y.gcd x) := by
    apply Int.dvd_gcd
    . rw [Int.gcd_comm]
      exact gcd_dvd y x hy hx (by rwa [add_comm]) (by rwa [add_comm])
    . nth_rw 2 [Int.gcd_comm]
      exact gcd_dvd x y hx hy hxy1 hxy2
  -- Notice that $gcd(x/d,y/d)=1$.
  have : (Int.gcd (x / x.gcd y) (y / x.gcd y) : ℤ) = 1 := by
    obtain ⟨a, ha⟩ : ↑(x.gcd y) ∣ x := Int.gcd_dvd_left
    obtain ⟨b, hb⟩ : ↑(x.gcd y) ∣ y := Int.gcd_dvd_right
    set d := x.gcd y
    have hd : (d : ℤ) ≠ 0 := gcd_ne_zero_of_right hy
    rw [ha, hb]
    field_simp
    rw [Int.gcd, ← Nat.coprime_iff_gcd_eq_one]
    have {x y z : ℤ} (h : x = y * z) (hy : y ≠ 0) : z.natAbs = x.natAbs / y.natAbs := by
      zify
      rw [h, abs_mul]
      field_simp
    rw [this ha (by positivity), this hb (by positivity)]
    exact Nat.coprime_div_gcd_div_gcd gcd_xy_pos
  rw [Int.gcd_comm y, this] at gcd_xy_dvd
  -- We have $d=1$ which means that x,y are coprime.
  have xy_coprime : x.gcd y = 1 := by
    zify
    exact Int.eq_one_of_dvd_one (by positivity) gcd_xy_dvd
  -- $x^2+y^2\mid (x^5+y)(x^5-y)=(x^2)^5-y^2\implies (-y^2)^5-y^2\equiv (x^2)^5-y^2\equiv 0\pmod{x^2+y^2}$ .
  -- $x^2+y^2\mid y^{10}-y^2\implies x^2+y^2\mid y^8-1$  since  $\gcd(x^2+y^2,y^2)=1$ .
  -- So,  $x^2+y^2\mid y^8-1-y^3(y^5+x)=-(xy^3+1)$ .
  have sq_add_sq_dvd (x y : ℤ) (hxy1 : x^2+y^2 ∣ x^5+y) (hxy2 : x^2+y^2 ∣ y^5+x)
      (h : Int.gcd (x ^ 2 + y ^ 2) (x ^ 2) = 1) :
      x ^ 2 + y ^ 2 ∣ 1 - x ^ 3 * y := by
    have := Dvd.dvd.mul_right hxy1 (x ^ 5 - y)
    ring_nf at this
    rw [← Int.modEq_zero_iff_dvd] at this
    have := this.add (show x ^ 2 + y ^ 2 ≡ 0 [ZMOD x ^ 2 + y ^ 2] from Int.emod_self)
    ring_nf at this
    symm at this
    rw [Int.modEq_iff_dvd, sub_zero, show x ^ 2 + x ^ 10 = (1 + x ^ 8) * x ^ 2 by ring] at this
    -- x ^ 2 + y ^ 2 | 1 + x ^ 8
    have := Int.dvd_of_dvd_mul_left_of_gcd_one this h
    have := this.sub (hxy1.mul_right (x ^ 3))
    ring_nf at this
    exact this
  -- Since  $\gcd(x^2+y^2,x)=\gcd(x^2+y^2,y)=1$ ,  $x^2+y^2\mid x^2-y^2$ .
  have sq_add_sq_dvd_sq_sub_sq : x ^ 2 + y ^ 2 ∣ x ^ 2 - y ^ 2 := by
    have h {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Int.gcd (a + b) a = Int.gcd a b := by
      rw [Int.gcd, Int.gcd, show (a+b).natAbs = a.natAbs + b.natAbs by zify; repeat rw [abs_of_nonneg (by positivity)],
        add_comm, Nat.gcd_comm (a.natAbs)]
      exact Nat.gcd_add_self_left _ _
    have h1 := sq_add_sq_dvd x y hxy1 hxy2 (by
      rw [h (by positivity) (by positivity)]
      rw [Int.gcd, ← Nat.coprime_iff_gcd_eq_one] at xy_coprime
      have := Nat.Coprime.pow 2 2 xy_coprime
      rw [Nat.coprime_iff_gcd_eq_one] at this
      rw [Int.gcd]
      convert this
      . zify
        exact Eq.symm (pow_abs x 2)
      . zify
        exact Eq.symm (pow_abs y 2))
    have h2 := sq_add_sq_dvd y x (by rwa [add_comm]) (by rwa [add_comm]) (by
      rw [h (by positivity) (by positivity)]
      rw [Int.gcd, ← Nat.coprime_iff_gcd_eq_one] at xy_coprime
      have := Nat.Coprime.pow 2 2 xy_coprime
      rw [Nat.coprime_iff_gcd_eq_one] at this
      rw [Int.gcd_comm, Int.gcd]
      convert this
      . zify
        exact Eq.symm (pow_abs x 2)
      . zify
        exact Eq.symm (pow_abs y 2))
    rw [add_comm] at h2
    have := h1.sub h2
    ring_nf at this
    rw [show x*y^3-x^3*y = (y^2-x^2)*(x*y) by ring] at this
    have := Int.dvd_of_dvd_mul_left_of_gcd_one this (by
      by_contra h
      push_neg at h
      have : (x ^ 2 + y ^ 2).gcd (x * y) ≠ 0 := by
        zify
        apply gcd_ne_zero_of_right
        positivity
      have : 2 ≤ (x ^ 2 + y ^ 2).gcd (x * y) := by omega
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h
      zify at hpdvd
      have : ↑((x ^ 2 + y ^ 2).gcd (x * y)) ∣ x * y := Int.gcd_dvd_right
      have := Int.dvd_trans hpdvd this
      have := Int.Prime.dvd_mul' hp this
      rcases this with hpx | hpy
      . have : ↑((x ^ 2 + y ^ 2).gcd (x * y)) ∣ x ^ 2 + y ^ 2 := Int.gcd_dvd_left
        have := Int.dvd_trans hpdvd this
        have := this.sub (hpx.pow (show 2 ≠ 0 by norm_num))
        ring_nf at this
        have := Int.Prime.dvd_pow' hp this
        have : (p : ℤ) ∣ x.gcd y := by
          exact Int.dvd_gcd hpx this
        rw [xy_coprime] at this
        norm_num at this
        have := Int.eq_one_of_dvd_one (by positivity) this
        norm_cast at this
        rw [this] at hp
        norm_num at hp
      have : ↑((x ^ 2 + y ^ 2).gcd (x * y)) ∣ x ^ 2 + y ^ 2 := Int.gcd_dvd_left
      have := Int.dvd_trans hpdvd this
      have := this.sub (hpy.pow (show 2 ≠ 0 by norm_num))
      ring_nf at this
      have := Int.Prime.dvd_pow' hp this
      have : (p : ℤ) ∣ x.gcd y := by
        exact Int.dvd_gcd this hpy
      rw [xy_coprime] at this
      norm_num at this
      have := Int.eq_one_of_dvd_one (by positivity) this
      norm_cast at this
      rw [this] at hp
      norm_num at hp)
    rw [show y^2-x^2=-(x^2-y^2) by ring, Int.dvd_neg] at this
    exact this
  rcases eq_or_ne (x ^ 2) (y ^ 2) with xeqy | xney
  swap
  -- If  $x^2-y^2\neq 0$  then  $|x^2-y^2|\geq |x^2+y^2|\implies \max(x^2,y^2)\geq x^2+y^2>\max(x^2,y^2)$  which is absurd.
  . exfalso
    have max_lt_of_ne (_ : x^2 ≠ y^2) : max (x^2) (y^2) < x^2 + y^2 := by
      rcases lt_trichotomy (x^2) (y^2) with hxy | hxy | hxy
      . rw [max_eq_right hxy.le]
        have : 0 < x ^ 2 := by
          rw [lt_iff_le_and_ne]
          exact ⟨sq_nonneg _, by positivity⟩
        linarith
      . contradiction
      . rw [max_eq_left hxy.le]
        have : 0 < y ^2 := by
          rw [lt_iff_le_and_ne]
          exact ⟨sq_nonneg _, by positivity⟩
        linarith
    have lt_max_of_ne (_ : x^2 ≠ y^2) : |x^2 - y^2| < max (x^2) (y^2) := by
      rcases lt_trichotomy (x^2) (y^2) with hxy | hxy | hxy
      . rw [abs_of_neg (by linarith), max_eq_right (by linarith)]
        have : 0 < x ^ 2 := by
          rw [lt_iff_le_and_ne]
          exact ⟨sq_nonneg _, by positivity⟩
        linarith
      . contradiction
      . rw [abs_of_pos (by linarith), max_eq_left (by linarith)]
        have : 0 < y ^ 2 := by
          rw [lt_iff_le_and_ne]
          exact ⟨sq_nonneg _, by positivity⟩
        linarith
    have abs_sq_sub_sq_pos : 0 < |x ^ 2 - y ^ 2| := by
      suffices |x ^ 2 - y ^ 2| ≠ 0 by
        rw [lt_iff_le_and_ne]
        exact ⟨abs_nonneg _, this.symm⟩
      simp only [ne_eq, abs_eq_zero]
      intro h
      have : x ^ 2 = y ^ 2 := by linear_combination h
      contradiction
    specialize max_lt_of_ne xney
    specialize lt_max_of_ne xney
    have := lt_trans lt_max_of_ne max_lt_of_ne
    rw [← dvd_abs] at sq_add_sq_dvd_sq_sub_sq
    have := Int.le_of_dvd abs_sq_sub_sq_pos sq_add_sq_dvd_sq_sub_sq
    linarith
  -- Thus,  $x^2=y^2\implies x=\pm y$ . But since  $\gcd(x,y)=1$ ,  $x,y\in\{-1,1\}$ .
  rw [sq_eq_sq_iff_eq_or_eq_neg] at xeqy
  rcases xeqy with h | h
  . rw [h] at xy_coprime
    rw [Int.gcd_self] at xy_coprime
    zify at xy_coprime
    rw [abs_eq (by norm_num)] at xy_coprime
    rcases xy_coprime with hy1 | hy1
    all_goals
      rw [hy1] at h
      rw [hy1, h]
      norm_num
  . rw [h] at xy_coprime
    rw [Int.neg_gcd, Int.gcd_self] at xy_coprime
    zify at xy_coprime
    rw [abs_eq (by norm_num)] at xy_coprime
    rcases xy_coprime with hy1 | hy1
    all_goals
      rw [hy1] at h
      rw [hy1, h]
      norm_num
