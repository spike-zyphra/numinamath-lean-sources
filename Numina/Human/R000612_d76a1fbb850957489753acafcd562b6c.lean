import Mathlib

/- Compute $$\sum_{k=1}^{1000} k(\lceil \log_{\sqrt{2}}{k}\rceil- \lfloor\log_{\sqrt{2}}{k} \rfloor).$$ -/
theorem algebra_13276: ∑ k in Finset.range 1000, (k+1)*(⌈Real.logb √2 (k+1)⌉ - ⌊Real.logb √2 (k+1)⌋) = 499477 := by
  -- some auxilary definitions.
  let f(x:ℝ): ℤ :=
    if x = ⌊x⌋ then 0
    else 1
  have f_def: f = fun (x:ℝ) => (if x = ⌊x⌋ then 0 else 1) := rfl
  -- notice that when x is integer, ⌈x⌉ = ⌊x⌋, else ⌈x⌉-⌊x⌋=1
  have hf: f = fun (x:ℝ) => (⌈x⌉ - ⌊x⌋) := by
    rw [f_def]
    funext x
    by_cases hx: x = ⌊x⌋
    rw [if_pos hx, hx]; simp
    rw [if_neg hx]
    have h1: ⌈x⌉ = ⌊x⌋ + 1 ∨ ⌈x⌉ = ⌊x⌋ := by
      have ht1: ⌈x⌉ ≤ ⌊x⌋ + 1 := Int.ceil_le_floor_add_one x
      have ht2: ⌈x⌉ ≥ ⌊x⌋ := Int.floor_le_ceil x
      -- notice that for integer a,b; if a ≤ b+1 and a ≥ b, then a = b or a = b+1. because integer has gap, cannot take "middle" value.
      omega
    rcases h1 with h1l | h1r
    omega
    rw [Int.ceil_eq_iff] at h1r
    have hx': x = ⌊x⌋ := by
      have ht1 := h1r.right
      have ht2: x ≥ ⌊x⌋ := Int.floor_le x
      apply eq_of_le_of_le ht1 ht2
    contradiction
  let g(k:ℤ): ℝ := Real.logb √2 k
  have g_def: g = fun (k:ℤ) => Real.logb √2 k := rfl
  -- rewrite the expression in terms of f and g
  have h1: ∑ k in Finset.range 1000, (k+1)*(⌈Real.logb √2 (k+1)⌉ - ⌊Real.logb √2 (k+1)⌋) = ∑ k in Finset.range 1000, (k+1) * (f (g (k+1))) := by
    rw [g_def,hf]; simp
  rw [h1, f_def]; simp
  -- therefore the original expression can be separated in two parts.
  have h2 (n:ℕ)(hn: 0 < n): (∑ x ∈ Finset.range n, if g (x + 1) = ⌊g (x + 1)⌋ then 0 else (x + 1 : ℤ)) = ∑ x ∈ Finset.range n, (x+1:ℤ) - ∑ x ∈ Finset.range n, if g (x+1) = ⌊g (x+1)⌋ then (x+1:ℤ) else 0 := by
    induction' n with d hd
    omega
    by_cases hhd: d = 0
    rw [hhd]
    have: g 1 = 0 := by
        rw [g_def]; simp
    have ht: g 1 = ⌊g 1⌋ := by
      rw [this]; simp
    simp
    rw [if_pos ht, if_pos ht]; simp
    have posd: 0 < d := by
      push_neg at hhd
      -- d is natural number and we have d ≠ 0, so 0 < d.
      omega
    rw [Finset.sum_range_succ]
    have ht1: ∑ x ∈ Finset.range (d + 1), (x + 1:ℤ) - (∑ x ∈ Finset.range (d + 1), if g (x + 1) = ⌊g (x + 1)⌋ then (x + 1:ℤ) else 0) = ∑ x ∈ Finset.range d, (x+1:ℤ) - (∑ x ∈ Finset.range d, if g (x+1) = ⌊g (x+1)⌋ then (x+1:ℤ) else 0) + (d+1:ℤ) - (if g (d+1) = ⌊g (d+1)⌋ then (d+1:ℤ) else 0) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      ring
    rw [ht1, hd posd]
    by_cases gcon: g (d+1) = ⌊g (d+1)⌋
    rw [if_pos gcon, if_pos gcon]; simp
    rw [if_neg gcon, if_neg gcon]; simp
  have: 0 < 1000 := by norm_num
  rw [h2 1000 this]
  -- now, it suffices to find the value of two sums.
  have sum1eq': ∑ x ∈ Finset.range 1000, (x+1:ℤ) = (1000*1001)/2 := by
    -- we know that 1+2+..+n = n(n+1)/2
    have hsum (n:ℕ): ∑ x ∈ Finset.range n, (x+1:ℤ) = n*(n+1)/2 := by
      induction' n with d hd
      simp
      rw [Finset.sum_range_succ, hd]
      by_cases hdvd: 2 ∣ (d+1:ℤ)
      have ht1: (d+1:ℤ) = (d+1)/2 * 2 := by omega
      nth_rw 2 [ht1]
      have ht2: d*(d+1:ℤ)/2 = (d+1)/2 * d := by
        rw [mul_comm ((d+1:ℤ)/2)]
        apply Int.mul_ediv_assoc d hdvd
      have ht3: (d+1:ℤ)+1 = d+2 := by ring
      simp
      have ht4: (d+1:ℤ)*(d+2)/2 = (d+2)*((d+1:ℤ)/2) := by
        rw [mul_comm]
        apply Int.mul_ediv_assoc (d+2) hdvd
      rw [ht2, ht3, ht4]; ring
      have hdvd': 2 ∣ d := by
        -- for any integer d, d % 2 is integer less than 2, and can only be 0 or 1.
        have: d % 2 = 0 ∨ d % 2 = 1 := by omega
        rcases this with hl | hr
        apply Nat.dvd_of_mod_eq_zero hl
        have: (d+1) % 2 = 0 := by
          apply Nat.succ_mod_two_eq_zero_iff.mpr hr
        have tt1: 2 ∣ (d+1) := Nat.dvd_of_mod_eq_zero this
        have tt2: 2 ∣ (d+1:ℤ) := Int.natAbs_dvd_natAbs.mp tt1
        exfalso; apply hdvd tt2
      have dvdz: 2 ∣ (d:ℤ) := by
        exact Int.ofNat_dvd_right.mpr hdvd'
      simp
      have ht1:  (d+1:ℤ) * (d+1+1) / 2 = (d+1)*((d+2)/2) := by
        have tt1: (d+1+1:ℤ) = d+2 := by ring
        have tt2: 2 ∣ (d+2:ℤ) := by
          have: 2 ∣ (2:ℤ) := Int.dvd_of_emod_eq_zero rfl
          apply (Int.dvd_add_right dvdz).mpr this
        rw [tt1, Int.mul_ediv_assoc (d+1:ℤ) tt2]
      rw [mul_comm (d:ℤ), Int.mul_ediv_assoc (d+1:ℤ) dvdz]
      nth_rw 2 [← mul_one (d+1:ℤ)]
      rw [← Int.mul_add, ht1]
      simp; omega
    apply hsum 1000
  -- finish calculation of sum part1, move on sum part2.
  -- notice that when k is an integer power of √2, g(x+1) is integer. and when k is integer, it's equivalent to say k is of the form 2^n
  -- so we only need to consider those 2^n, other terms are all zero.
  -- before going on, some lemmas are needed.
  -- for g(k) to be integer, k must be integer power of √2. and we can prove, when k is between 2^n and 2^(n+1), g(k) cannot be integer.
  have one_lt_rt2: 1 < √2 := by
    have: 1^2 < (2:ℝ) := by norm_num
    exact Real.lt_sqrt_of_sq_lt this
  have gvalue (n:ℕ): g (2^n) = 2*n := by
    rw [g_def]; simp
    have pos2: 0 < (2:ℝ) := by norm_num
    have: Real.logb √2 2 = 2 := by
      have: 2 = √2^2 := by norm_num
      nth_rw 2 [this]
      rw [Real.logb_pow]
      have: Real.logb √2 √2 = 1 := by
        apply Real.logb_self_eq_one one_lt_rt2
      simp [this]
    rw [Real.logb_pow, this]
    ring
  have gmono (n1 n2: ℕ): 0 < n1 → 0 < n2 → n1 < n2 → g n1 < g n2 := by
    intro n1pos n2pos nlt
    rw [g_def]; simp
    have n2pos': (0:ℝ) < n2 := Nat.cast_pos'.mpr n2pos
    have n1pos': (0:ℝ) < n1 := Nat.cast_pos'.mpr n1pos
    have nlt': (n1:ℝ) < n2 := Nat.cast_lt.mpr nlt
    apply (Real.logb_lt_logb_iff one_lt_rt2 n1pos' n2pos').mpr nlt'
  have gifpos (n:ℕ): g (2^n) = ⌊g (2^n)⌋ := by
    rw [gvalue n]
    have: n*2 = ⌊((n*2):ℝ)⌋ := by
      let n2 := n*2
      have n2_def: n2 = n*2 := rfl
      have: ⌊(n2:ℝ)⌋ = n2 := Int.floor_natCast n2
      rw [n2_def] at this; simp at this; rw [this]
    rw [mul_comm, ← this]; simp
  have nirrn(n:ℕ): ¬ Irrational (2^n) := by
    induction' n with e he
    simp
    rw [pow_succ']
    have h1: ¬ Irrational 2 := by simp
    by_contra! hc
    have h2: Irrational 2 ∨ Irrational (2^e) := by
      apply Irrational.mul_cases hc
    rcases h2 with h3 | h3
    apply h1 h3
    apply he h3
  -- when k is at the "gap", g(k) cannot be integer.
  have gne(k n:ℕ): (2^n < k ∧ k < 2^(n+1)) → ¬ (g k) = ⌊g k⌋ := by
    intro ⟨kgt,klt⟩
    by_cases nz: n = 0
    rw [nz] at kgt klt; simp at kgt klt
    omega
    push_neg at nz
    have ht1 (a b:ℕ): (a:ℝ) < b → a < b := by
      intro hlt
      by_contra! hc
      by_cases ht: b = a
      rw [ht] at hlt
      simp at hlt
      have tt1: b < a := by
        apply Nat.lt_of_le_of_ne hc ht
      have tt2: 0 < a-b := by
        exact Nat.zero_lt_sub_of_lt tt1
      let diff := a-b
      have diff_def: diff = a-b := rfl
      rw [← diff_def] at tt2
      have tt3: 0 < (diff:ℝ) := by
        exact Nat.cast_pos'.mpr tt2
      have tt4: diff = (a:ℝ)-b := by
        rw [diff_def]
        apply Nat.cast_sub hc
      rw [tt4] at tt3
      linarith [tt3, hlt]
    have ht2: ¬ ∃ a:ℕ, a = g k := by
      have pos2n:0 < 2^n := Nat.two_pow_pos n
      have pos2n1: 0 < 2^(n+1) := Nat.two_pow_pos (n+1)
      have posk: 0 < k := by
        linarith [pos2n,kgt]
      have g1lt: g (2^n) < g k := by
        have := gmono (2^n) k pos2n posk kgt
        simp at this; exact this
      have g2lt: g k < g (2^(n+1)) := by
        have := gmono k (2^(n+1)) posk pos2n1 klt
        simp at this; exact this
      by_contra! hc
      rcases hc with ⟨a,ha⟩
      rw [gvalue, ← ha] at g1lt; rw [gvalue, ← ha] at g2lt
      have ale: a ≤ 2*n + 1 := by
        have alt: a < 2*n+1 +1 := by
          have: (a:ℝ) < ((2*n+1 + 1):ℝ) := by
            simp at g2lt; linarith [g2lt]
          apply ht1
          simp; exact this
        exact Nat.le_of_lt_succ alt
      have age: a ≥ 2*n+1 := by
        have agt: a > 2*n := by
          have: 2*n < a := by
            apply ht1
            simp; exact g1lt
          exact this
        exact agt
      have aeq: a = 2*n+1 := le_antisymm ale age
      rw [aeq] at ha; simp at ha
      rw [← gvalue, g_def] at ha; simp at ha
      have: Real.logb √2 √2 = 1 := Real.logb_self_eq_one one_lt_rt2
      rw [← this, ← Real.logb_mul] at ha
      have ginj := Real.logb_injOn_pos one_lt_rt2
      rw [Set.InjOn] at ginj; simp at ginj
      have con1: 2^n * √2 = k := by
        have tt1: 0 < 2^n * √2 := by
          have hh1: 0 < √2 := by norm_num
          have hh2: 0 < (2:ℝ)^n := by
            have: 0 < (2:ℝ) := by norm_num
            apply pow_pos this n
          apply mul_pos hh2 hh1
        have tt2: 0 < (k:ℝ) := by
          apply Nat.cast_pos'.mpr posk
        apply ginj tt1 tt2 ha
      have con2: √2 = k / 2^n := by
        rw [← con1]; simp
      have irr2 := irrational_sqrt_two
      rw [con2] at irr2
      simp at irr2
      have con3 := irr2.right
      simp at con3
      apply nirrn n con3
      simp
      simp
    by_contra! hc
    have ht3: ∃a:ℕ,a = g k := by
      use ⌊g k⌋.toNat
      rw [hc]
      simp
      have tt1: 0 ≤ ⌊g k⌋ := by
        have: 0 ≤ g k := by
          rw [g_def]; simp
          have kge1: (k:ℝ) ≥ 1 := by
            have hhh1: k > 1 := by omega
            have hhh2: (k:ℝ) > 1 := Nat.one_lt_cast.mpr hhh1
            apply le_of_lt hhh2
          apply Real.logb_nonneg one_lt_rt2 kge1
        apply Int.floor_nonneg.mpr this
      have tt2: ⌊g k⌋.toNat = ⌊g k⌋ := Int.toNat_of_nonneg tt1
      apply congrArg Int.cast tt2
    apply ht2 ht3
  have hhn (n:ℕ): n ≠ 0 → 2^n < 2^n + 1 ∧ 2^n + 1 < 2^(n+1) := by
    intro nez
    have hleft: 2^n < 2^n + 1 := by omega
    have hright: 2^n + 1 < 2^(n+1) := by
      have ht1: 2^(n+1) = 2^n + 2^n := by omega
      have ht2: 2^n > 1 := by
        induction' n with d hd
        norm_num at nez
        have tt1: 2^(d+1) = 2^d + 2^d := by omega
        have tt2: 2^d ≥ 1 := Nat.one_le_two_pow
        rw [tt1]
        linarith [tt2]
      rw [ht1]
      linarith [ht2]
    exact ⟨hleft,hright⟩
  -- if k is between 2^n and 2^(n+1), then those terms from 2^n to k are all zero, therefore sum from 0 to k is equal to sum from 0 to 2^n.
  have h3(k n: ℕ): n ≠ 0 → (2^n < k ∧ k < 2^(n+1)) → ∑ x ∈ Finset.range k, (if g (x + 1:ℤ) = ⌊g (x + 1:ℤ)⌋ then (x + 1:ℤ) else 0) =
    ∑ x ∈ Finset.range (2^n), (if g (x + 1:ℤ) = ⌊g (x + 1:ℤ)⌋ then (x + 1:ℤ) else 0) := by
    induction' k with d hd
    intro nez ⟨hleft,hrgiht⟩; norm_num at hleft
    intro nez ⟨hgt,hlt⟩
    have hge: d ≥ 2^n := Nat.le_of_lt_succ hgt
    by_cases dd: d = 2^n
    -- d = 2n, term d+1 is zero.
    rw [dd, Finset.sum_range_succ]
    simp
    intro h
    have nh: ¬ g (d+1) = ⌊g (d+1)⌋ := by
      apply gne (d+1) n
      rw [dd]; apply hhn n nez
    rw [dd] at nh; simp at nh
    exfalso; apply nh h
    -- d ≠ 2n, we use induction hypothesis.
    have dgt: 2^n < d := by
      apply Nat.lt_of_le_of_ne
      apply hge
      push_neg at dd; symm at dd; push_neg; apply dd
    have dlt: d < 2^(n+1) := by linarith [hlt]
    rw [Finset.sum_range_succ, hd nez ⟨dgt,dlt⟩]
    simp
    intro h
    have nh: ¬ g (d+1) = ⌊g (d+1)⌋ := gne (d+1) n ⟨hgt,hlt⟩
    exfalso; apply nh h
  -- use h3, we prove that the whole sum is exactly the sum of those nonzero terms.
  have h4(k n: ℕ):  ∑ x ∈ Finset.range (2^n), (if g (x + 1:ℤ) = ⌊g (x + 1:ℤ)⌋ then (x + 1:ℤ) else 0) = ∑ x ∈ Finset.range (n+1), 2^x := by
    have gifpos1: g 1 = ⌊g 1⌋ := by
      rw [g_def]; simp
    have gifpos2: g 2 = ⌊g 2⌋ := by
      have: (2:ℤ) = 2^1 := by norm_num
      rw [this, gifpos 1]
      simp
    induction' n with d hd
    simp; apply gifpos1
    by_cases dz: d=0
    rw [dz]; simp
    rw [Finset.sum_range_succ]; simp
    rw [if_pos gifpos1, if_pos gifpos2]; simp
    push_neg at dz
    let v := 2^(d+1)-1
    have v_def: v = 2^(d+1)-1 := rfl
    have v_def': v = 2^d + 2^d - 1 := by
      rw [v_def]; omega
    have eqv: (v+1:ℤ) = 2^(d+1) := by
      rw [v_def]; simp
    have: 2^(d+1) = v+1 := by
      rw [v_def]
      have: 1 ≤ 2^(d+1) := Nat.one_le_two_pow
      simp [this]
    rw [this, Finset.sum_range_succ]
    have ht1: 2^d < v := by
      rw [v_def']
      have: 1 < 2^d := Nat.one_lt_two_pow_iff.mpr dz
      rw [Nat.add_sub_assoc (le_of_lt this)]
      have: 0 < 2^d-1 := Nat.zero_lt_sub_of_lt this
      apply Nat.lt_add_of_pos_right this
    have ht2: v < 2^(d+1) := by
      rw [v_def]
      have: 2^(d+1) ≠ 0 := by norm_num
      apply Nat.sub_one_lt this
    rw [h3 v d dz ⟨ht1,ht2⟩, hd]
    have: ∑ x ∈ Finset.range (d+1+1),(2:ℤ)^x = ∑ x ∈ Finset.range (d+1),2^x + 2^(d+1) := by
      rw [Finset.sum_range_succ]
    rw [this]; simp
    rw [eqv, if_pos (gifpos (d+1))]
  -- now we can deal the part2 sum.
  have sum2eq': ∑ x ∈ Finset.range 1000, (if g (x + 1:ℤ) = ⌊g (x + 1:ℤ)⌋ then (x + 1:ℤ) else 0) = ∑ j ∈ Finset.range 10, 2^j := by
    -- notice that 2^4=16, 16x16=256=2^8. therefore 2^9=512, 2^10=1024. and 1000 is between 2^9 and 2^10.
    have ht1: 9 ≠ 0 := by norm_num
    have ht2: 2^9 < 1000 := by
      have: 2^9 = 512 := by norm_num
      rw [this]; norm_num
    have ht3: 1000 < 2^10 := by
      have: 2^10 = 1024 := by norm_num
      rw [this]; norm_num
    rw [h3 1000 9 ht1 ⟨ht2,ht3⟩, h4 9]
  rw [sum1eq', sum2eq']
  -- some calculation. part1 is 1000x1001/2, and it is 500x1001=500500
  have sum1eq: (1000:ℤ) * 1001 / 2 = 500500 := by norm_num
  -- part2 is 2^0+2^1+...+2^9. use geometric sequence sum, or we directly calculate its value, result is 2^10-1=1023.
  have sum2eq: ∑ j ∈ Finset.range 10, (2:ℤ)^j = 1023 := by
    have: 10 = 1+1+1+1+1+1+1+1+1+1 := by simp
    rw [this]
    repeat' rewrite [Finset.sum_range_succ]
    simp
  rw [sum1eq,sum2eq]
  -- 500500-1023 = 499477
  simp
