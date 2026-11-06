import Mathlib

/-
Prove that if a and b are positive integers with a odd and b even,
and if a^n + b^n is an odd prime, then n must be a power of 2.
-/
theorem PrimePowerOfTwoExponent (a b n: ℕ) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (hb' : Even b) (hn' : Odd (a ^ n + b ^ n) ∧ Nat.Prime (a ^ n + b ^ n)) :
    ∃ k : ℕ, n = 2 ^ k := by
  -- Extract the hypothesis: a^n + b^n is an odd prime p
  obtain ⟨hp1, hp2⟩ := hn'
  set p := a^n + b^n with hp
  by_contra hnot

  -- Factor n as n = 2^k * m where m is odd
  have exists_k_m : ∃ k m, n = 2 ^ k * m ∧ Odd m := by
    have h2 : 2 ≠ 1 := by decide
    have hnpos:n≠0:=by omega
    rcases Nat.exists_eq_pow_mul_and_not_dvd hnpos 2 h2 with ⟨k, m, hm', hm⟩
    use k, m
    have t:Odd m:=by refine Nat.odd_iff.mpr ?_;omega
    split_ands
    exact hm
    exact t
  rcases exists_k_m with ⟨k, m, n_eq, m_odd⟩
  have hkpos:k≥0:=by omega

  -- If m=1 then n is a power of 2, contradicting our assumption
  by_cases hm1 : m = 1
  · apply hnot
    use k
    rw [n_eq, hm1, mul_one]

  -- Now m > 1 and odd
  have m_gt1 : 1 < m := by
    by_contra not
    push_neg at not
    interval_cases m
    all_goals omega

  -- Define x = a^{2^k}, y = b^{2^k}
  set x := a ^ (2 ^ k) with hx_def
  set y := b ^ (2 ^ k) with hy_def

  -- Express p as x^m + y^m
  have hp_eq : p = x^m + y^m := by
    rw [hp, n_eq, pow_mul, pow_mul, hx_def, hy_def]

  -- In ℤ, prove x+y divides x^m + y^m using factorization
  have h_dvd_int : (x + y : ℤ) ∣ (x^m + y^m : ℤ) := by
    have h_factor : (x : ℤ)^m + (y : ℤ)^m = (x + y) *
        (Finset.sum (Finset.range m) (fun i => (-(1:ℤ))^i * x^(m - 1 - i) * y^i)) := by
      -- Rewrite x^m + y^m as x^m - (-y)^m
      rw [← sub_neg_eq_add]

      -- Key step: prove -y^m = (-y)^m
      have neg_pow_y : -((y^m):ℤ) = (((-y):ℤ)^m:ℤ) := by
        ring_nf
        have :(-1)^m=-1:=by exact Odd.neg_one_pow m_odd
        rw [this]
        omega
      rw [neg_pow_y]

      -- Apply geometric series formula
      have h_geom := geom_sum₂_mul (x:ℤ) (-y:ℤ) m
      rw [← h_geom]


      -- Simplify: x - (-y) = x + y
      rw [sub_eq_add_neg]       -- x - (-y) → x + -(-y)
      rw [neg_neg]              -- -(-y) → y
      rw [add_comm]
      rw [mul_add]
      rw [add_mul]

      congr 1
      rw [← Finset.sum_range_reflect (fun i => (-1:ℤ)^i * (x:ℤ)^(m-1-i) * (y:ℤ)^i) m]
      have t':(∑ i ∈ Finset.range m, (x:ℤ) ^ i * ((-y):ℤ) ^ (m - 1 - i)) * (y:ℤ)=(∑ i ∈ Finset.range m, (x:ℤ) ^ i * (-1) ^ (m - 1 - i)*y^(m-1-i)) * ↑y:=by
        ring_nf
        simp
        constructor
        have :((-y):ℤ) ^ (m - 1 - x)=(-1) ^ (m - 1 - x) * y ^ (m - 1 - x):=by
          ring
        rw [← Finset.sum_congr]
        exact rfl
        ring_nf
        simp
      rw [t']
      rw [Finset.sum_congr]
      exact
        Int.mul_comm
          (∑ j ∈ Finset.range m, (-1) ^ (m - 1 - j) * ↑x ^ (m - 1 - (m - 1 - j)) * ↑y ^ (m - 1 - j))
          ↑y
      exact rfl
      intro j hj
      have hj_le : j ≤ m - 1 := Nat.le_pred_of_lt (Finset.mem_range.1 hj)
      rw [Nat.sub_sub_self hj_le]
      ring

      rw [← Finset.sum_range_reflect (fun i => (-1:ℤ)^i * (x:ℤ)^(m-1-i) * (y:ℤ)^i) m]
      have t':(∑ i ∈ Finset.range m, (x:ℤ) ^ i * ((-y):ℤ) ^ (m - 1 - i)) * (x:ℤ)=(∑ i ∈ Finset.range m, (x:ℤ) ^ i * (-1) ^ (m - 1 - i)*y^(m-1-i)) * ↑x:=by
        ring_nf
        simp
        constructor
        have :((-y):ℤ) ^ (m - 1 - x)=(-1) ^ (m - 1 - x) * y ^ (m - 1 - x):=by
          ring
        rw [← Finset.sum_congr]
        exact rfl
        ring_nf
        simp
      rw [t']
      rw [Finset.sum_congr]
      exact
        Int.mul_comm
          (∑ j ∈ Finset.range m, (-1) ^ (m - 1 - j) * ↑x ^ (m - 1 - (m - 1 - j)) * ↑y ^ (m - 1 - j))
          ↑x
      exact rfl
      intro j hj
      have hj_le : j ≤ m - 1 := Nat.le_pred_of_lt (Finset.mem_range.1 hj)
      rw [Nat.sub_sub_self hj_le]
      ring
    rw [h_factor]
    exact dvd_mul_right _ _

  -- Transfer back to ℕ divisibility
  have h_dvd_nat : (x + y) ∣ (x^m + y^m) := by
    exact Odd.nat_add_dvd_pow_add_pow x y m_odd

  -- Prove x + y > 1
  have hxy_gt1 : 1 < x + y := by
    have hb2 : b ≥ 2 := by
      rcases hb' with ⟨b, rfl⟩
      omega
    have hy2 : y ≥ 2 := by
      rw [hy_def]
      have t:2^k≥1:=by exact Nat.one_le_two_pow
      have t': b ^ (2 ^ k)≥b^1:=by exact Nat.pow_le_pow_right hb t
      have t'':b^1≥2:=by simp;exact hb2
      omega
    have hx1 : x ≥ 1 := Nat.one_le_pow _ _ (Nat.one_le_of_lt ha)
    linarith

  -- Prove x + y < x^m + y^m
  have hxy_lt : x + y < x^m + y^m := by
    have hm3 : 3 ≤ m := by
      have : 2 < m := by
        refine Nat.two_lt_of_ne ?_ hm1 ?_
        omega
        have m_odd':m%2=1:=by exact Nat.odd_iff.mp m_odd
        by_contra meq2
        rw [meq2] at m_odd'
        omega
      linarith
    have hy_pos:1<y:=by
        refine Nat.one_lt_pow ?_ ?_
        simp
        refine Nat.one_lt_of_ne_zero_of_even ?_ hb'
        omega
    by_cases hx1 : x = 1
    · rw [hx1, one_pow, add_comm, add_comm (1 : ℕ)]
      simp
      refine lt_self_pow₀ ?_ m_gt1
      exact hy_pos
    · have hx2 : x ≥ 2 := by
        have hxpos:0<x:=by
          rw [hx_def]
          exact Nat.pow_pos ha
        by_contra not
        push_neg at not
        push_neg at hx1
        interval_cases x
        omega
      have hx_lt : x < x^m := by exact lt_self_pow₀ hx2 m_gt1
      have hy_lt : y < y^m := by
        refine lt_self_pow₀ ?_ m_gt1
        exact hy_pos
      exact add_lt_add hx_lt hy_lt

  -- Contradiction: prime p has proper divisor x+y
  rw [← hp_eq] at hxy_lt
  have hp_eq':x+y∣p:=by exact (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod (id (Eq.symm hp_eq))) (x ^ m + y ^ m)) h_dvd_nat).mp h_dvd_nat
  have h_factors : x + y = 1 ∨ x + y = p := by
    exact (Nat.dvd_prime hp2).mp hp_eq'

  cases h_factors
  linarith [hxy_gt1]
  linarith [hxy_lt]

