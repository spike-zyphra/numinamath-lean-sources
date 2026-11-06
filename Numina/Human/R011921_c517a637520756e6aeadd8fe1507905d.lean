import Mathlib


/- Let $a, b, c, d$ be elements of the set $\{1, 2, 3, \ldots, 2014, 2015\}$
such that $a < b < c < d$, $a + b$ is a divisor of $c + d$, and $a + c$ is a divisor of $b + d$.
Determine the greatest possible value of $a$. -/
theorem number_theory_613046:
  IsGreatest {a:ℕ | a ∈ Finset.Icc 1 2015 ∧ (∃ (b c d: ℕ),
    b ∈ Finset.Icc 1 2015 ∧ c ∈ Finset.Icc 1 2015 ∧ d ∈ Finset.Icc 1 2015 ∧
    a < b ∧ b < c ∧ c < d ∧
    a+b ∣ c+d ∧ a+c ∣ b+d)} 464 := by

  rw [IsGreatest, upperBounds]
  simp only [Finset.mem_Icc, exists_and_left, Set.mem_setOf_eq,
    Nat.one_le_ofNat, Nat.reduceLeDiff, and_self,
    true_and, and_imp, forall_exists_index]
  constructor

  · -- when a = 464, find such b,c,d.
    refine ⟨466, ?_, 776, ?_, 2014, ?_⟩
    <;> norm_num

  · -- prove a ≤ 464
    intro a age ale b bge ble c cge cle d dge dle
      hab hbc hcd hdvd1 hdvd2
    -- suppose c+d = m(a+b), b+d = n(a+c)
    rcases hdvd1 with ⟨m, hm⟩
    rcases hdvd2 with ⟨n, hn⟩
    -- obviously, m,n > 1 since d > c > b > a
    have mgt: (a+b) < (a+b) * m := by
      rw [← hm]
      linarith only [hab, hbc, hcd]
    have ngt: a+c < (a+c)*n := by
      rw [← hn]
      linarith only [hab, hcd]
    rw [Nat.lt_mul_iff_one_lt_right (by linarith only [age, bge])] at mgt
    rw [Nat.lt_mul_iff_one_lt_right (by linarith only [age, cge])] at ngt
    -- we claim m > n
    have mgtn: m > n := by
      by_contra!
      have h1: c+d ≤ (a+b)*n := by
        rw [hm]
        exact Nat.mul_le_mul_left (a + b) this
      have h2: (a+b)*n ≤ (a+c)*n := by
        apply Nat.mul_le_mul_right _ ?_
        linarith only [hbc]
      rw [← hn] at h2
      have := h1.trans h2
      linarith only [this, hbc]

    -- take difference of two equations.
    have heq: b - (c:ℤ) = (a+c)*n - (a+b)*m := by
      zify at hm hn
      rw [← hm, ← hn]
      ring
    replace heq: (n+1: ℤ)*c = (m-n)*a + (m+1)*b := by
      linarith only [heq]
    -- divide n+1
    have hc: (c:ℚ) = ((m-n)*a + (m+1)*b) / (n+1) := by
      field_simp
      rw [mul_comm (c:ℚ) _]
      qify at heq; exact heq
    -- express d in terms of c, then substitute this in
    replace hm: d = (a+b)*m - (c:ℤ) := by
      linarith only [hm]
    have hd: (d:ℚ) = ((m+1)*n*a + (m*n-1)*b) / (n+1) := by
      qify at hm
      rw [hm, hc]
      field_simp
      ring
    -- m,n > 1, mn-1 > 0
    have mngt: m*n - (1:ℚ) > 0 := by
      simp only [sub_pos]
      qify at mgt ngt
      exact one_lt_mul mgt.le ngt
    -- b > a, then ... + b > ... + a
    have hd': (d:ℚ) > ((m+1)*n*a + (m*n-1)*a) / (n+1) := by
      rw [hd]
      rw [gt_iff_lt, div_lt_div_iff_of_pos_right
        (Nat.cast_add_one_pos n), add_lt_add_iff_left]
      -- m,n > 1, so mn - 1 > 0
      refine (mul_lt_mul_iff_of_pos_left mngt).mpr ?_
      simp [hab]
    rw [← add_mul] at hd'
    -- then a/d < ...
    have dpos: (0:ℚ) < d := by
        simp only [Nat.cast_pos]
        linarith only [dge]
    have ha: (a:ℚ)/d < (n+1) / ((m+1)*n + (m*n-1)) := by
      rw [gt_iff_lt, div_lt_iff₀ (Nat.cast_add_one_pos n)] at hd'
      rw [mul_comm (d:ℚ) _, ← div_lt_iff₀ dpos] at hd'
      rw [mul_div_assoc, mul_comm _ (a/d:ℚ)] at hd'
      refine (lt_div_iff₀ ?_).mpr hd'
      apply add_pos ?_ mngt
      simp [mul_pos, Nat.cast_add_one_pos, Nat.zero_lt_of_lt ngt]
    replace ha: (a:ℚ)/d < (1 + (2*m+2)/ ( (2*m+1)*n - 1 )) / (2*m+1) := by
      apply lt_of_lt_of_le ha (le_of_eq ?_)
      have h1: (m+1:ℚ)*n + (m*n-1) > 0 := by
        apply add_pos ?_ mngt
        simp [mul_pos, Nat.cast_add_one_pos, Nat.zero_lt_of_lt ngt]
      have h2: 2*m+(1:ℚ) > 0 := by linarith only
      have h3: (2*m+1:ℚ)*n - 1 > 0 := by
        simp only [gt_iff_lt, sub_pos]
        qify at ngt
        refine one_lt_mul ?_ ngt
        rw [gt_iff_lt] at h2
        norm_cast at h2 ⊢
      field_simp [h1.ne', h2.ne', h3.ne']
      ring
    have: (2*m+1:ℚ)*2 - 1 > 0 := by
      simp only [sub_pos]
      apply one_lt_mul ?_ (by norm_num)
      linarith only [mgt]
    -- n > 1, then n ≥ 2
    replace ha: (a:ℚ)/d < (1 + (2*m+2)/ ( (2*m+1)*2 - 1 )) / (2*m+1) := by
      apply lt_of_lt_of_le ha ?_
      refine (div_le_div_iff_of_pos_right ?_).mpr ?_
      · linarith only [mgt]
      · simp only [add_le_add_iff_left]
        refine (div_le_div_iff_of_pos_left ?_ ?_ this).mpr ?_
        · linarith only [mgt]
        · simp only [sub_pos]
          norm_cast
          apply one_lt_mul ?_ ngt
          linarith only [mgt]
        · simp only [tsub_le_iff_right, sub_add_cancel]
          rw [mul_le_mul_iff_of_pos_left (by linarith only [mgt])]
          norm_cast
    replace: ((1:ℚ) + (2*m+2)/ ( (2*m+1)*2 - 1 )) / (2*m+1) =
      3 / (4*m+1) := by
      field_simp [this]
      ring
    -- multiply d to right side, simplify
    rw [div_lt_iff₀ dpos, this] at ha
    -- n ≥ 2, m > n, so m ≥ 3. and we can find upperbound of 3/(4m+1)
    have mge: m ≥ 3 := by
      replace: m > 2 := by
        apply lt_of_le_of_lt ?_ mgtn
        exact ngt
      exact this
    replace: (3:ℚ) / (4*m+1) ≤ 3/13 := by
      refine (div_le_div_iff_of_pos_left
        (by norm_num) ?_ (by norm_num)).mpr ?_
      · linarith only
      · qify at mge
        linarith only [mge]
    -- d ≤ 2015, so a < 3/13 x 2015
    replace ha: (a:ℚ) < 3/13 * 2015 := by
      apply lt_of_lt_of_le ha ?_
      exact mul_le_mul this (by simp [dle]) (by simp) (by norm_num)
    -- 3/13 x 2015 = 465. a < 465, so a ≤ 464
    norm_num at ha
    exact Nat.le_of_lt_succ ha