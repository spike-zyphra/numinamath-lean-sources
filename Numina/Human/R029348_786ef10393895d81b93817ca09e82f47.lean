import Mathlib



/- Let $S$ be the set of all non-negative real numbers. Determine all $c \in \mathbb{R}$ for which there exists a function $f: S \rightarrow \mathbb{R}$ satisfying the inequality
$$f(x + y^2) \geq cf(x) + y$$
for all $x, y \in S$. -/
theorem inequalities_613502 (c : ℝ) :
  (∃ f : ℝ → ℝ, ∀ x y, 0 ≤ x → 0 ≤ y → f (x + y^2) ≥ c * f x + y) ↔ c < 1 := by

  constructor

  · -- such function does not exist if c ≥ 1
    rintro ⟨f,hf⟩
    by_contra! hc
    -- we can always find a positive f(x)
    have ex_posf: ∃ x:ℝ, 0 ≤ x ∧ f x > 0 := by
      use (|c * f 0| + 1)^2
      have h1: 0 < |c * f 0| + 1 := by
        linarith only [abs_nonneg (c * f 0)]
      have h2: |c * f 0| + c * f 0 ≥ 0 := by
        by_cases h: c * f 0 < 0
        · rw [abs_of_neg h]
          simp
        · push_neg at h
          rw [abs_of_nonneg h]
          linarith only [h]
      specialize hf 0 (|c * f 0| + 1) le_rfl h1.le
      rw [zero_add] at hf
      refine ⟨sq_nonneg _, ?_⟩
      apply lt_of_lt_of_le ?_ hf
      linarith only [h2]
    -- obviously, c > 1 is impossible, otherwise f(x) > f(x) for positive f(x)
    replace hc: c = 1 := by
      by_contra!
      replace hc := lt_of_le_of_ne hc this.symm
      rcases ex_posf with ⟨x,xnng,hfx⟩
      specialize hf x 0 xnng le_rfl
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, ge_iff_le] at hf
      absurd hf
      push_neg
      exact (lt_mul_iff_one_lt_left hfx).mpr hc
    simp only [hc, one_mul] at hf
    -- f(1) - f(0) is bounded.
    obtain ⟨N,hN⟩: ∃ (N:ℕ), f 1 - f 0 < N := by
      use (⌊f 1 - f 0⌋ + 1).natAbs
      have h1: f 1 - f 0 < ⌊f 1 - f 0⌋ + 1 := by
        exact Int.lt_floor_add_one (f 1 - f 0)
      have h2: ⌊f 1 - f 0⌋ + 1 ≤ (⌊f 1 - f 0⌋ + 1).natAbs := Int.le_natAbs
      rw [← Int.abs_eq_natAbs] at h2
      apply lt_of_lt_of_le h1 ?_
      rw [Nat.cast_natAbs]
      norm_cast
    have Npos: 0 < N := by
      have: f 1 - f 0 ≥ 1 := by
        specialize hf 0 (1^2) le_rfl (by simp)
        simp only [one_pow, zero_add, ge_iff_le] at hf
        linarith only [hf]
      rify
      linarith only [hN, this]
    -- but by cutting interval 0,1 into N^2 parts, we can prove f(1) - f(0) ≥ N.
    set g: ℕ → ℝ := fun i => f ( (i+1) * (1/N^2) ) - f ( i * (1/N^2)) with g_def
    have gsum {n:ℕ} (hn: n > 0):
      ∑ i ∈ Finset.range n, g i = f ( (n) * (1/N^2)) - f 0 := by
      replace hn: n ≥ 1 := by exact hn
      induction' n,hn using Nat.le_induction with n hn ih
      · simp [g_def]
      · rw [Finset.sum_range_succ, ih]
        simp [g_def]
    replace gsum: f 1 - f 0 = ∑ i ∈ Finset.range (N^2), g i := by
      rw [gsum (Nat.pos_pow_of_pos 2 Npos)]
      congr 2
      push_cast
      simp [Npos.ne']
    -- each g i ≥ 1/N
    have hg (i:ℕ): g i ≥ 1/N := by
      simp only [g_def]
      have: (i+1:ℝ) * (1/N^2) = (i * (1/N^2)) + (1/N)^2 := by
        simp [add_mul]
      rw [this]
      specialize hf (i * (1/N^2)) (1/N) (by positivity) (by positivity)
      linarith only [hf]
    -- so their sum ≥ N^2 1/N, contradiction.
    absurd hN
    push_neg
    have: (N:ℝ) = ∑ i ∈ Finset.range (N^2), (1/N:ℝ) := by
      simp only [one_div, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Nat.cast_pow]
      field_simp [Npos.ne']
      ring
    rw [this, gsum]
    apply Finset.sum_le_sum (fun _ _ => ?_)
    apply hg


  · -- find such function for c < 1
    intro hc
    -- if c ≤ 0, suffices to find f such that f(x+y^2) ≥ y
    -- we may just choose square root function
    by_cases c_sign: c ≤ 0
    · use (fun x => √x)
      intro x y hx hy
      simp only
      have h1: c*√x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg c_sign (by simp)
      have h2: √(x+y^2) ≥ y := by
        apply le_of_sq_le_sq ?_ (by simp)
        rw [Real.sq_sqrt (by positivity)]
        simp [hx]
      linarith only [h1,h2]
    push_neg at c_sign
    -- from latter calculation, we will find f(x) = a √x is possible,
    -- if c^2 - （a^2-1）(1-c^2) < 0
    -- and such a exist given 0 < c < 1.
    obtain ⟨a,ha1, ha2⟩ : ∃ a, c^2 - (a^2-1) * (1-c^2) < 0 ∧ a > 1 := by
      use √(1 + 2*c^2/(1-c^2))
      have h1: c^2 < 1 := by
        apply pow_lt_one₀ c_sign.le hc (by norm_num)
      have h2: 0 < 1-c^2 := by
        linarith only [h1]
      have h3: 0 < c^2 / (1-c^2) := div_pos (pow_pos c_sign 2) h2
      constructor
      · have: 0 ≤ 1 + 2*c^2/(1-c^2) := by
          rw [mul_div_assoc, two_mul]
          linarith only [h3]
        rw [Real.sq_sqrt this]
        simp [h2.ne', two_mul, pow_pos c_sign]
      · refine Real.lt_sqrt_of_sq_lt ?_
        simp [one_pow, lt_add_iff_pos_right, mul_div_assoc, h3]
    use (fun x => a*√x)
    intro x y hx hy
    simp only
    -- square both sides
    apply le_of_sq_le_sq ?_ (by positivity)
    have h1: (a*√(x+y^2))^2 = a^2*x + a^2*y^2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have h2: (c*(a*√x) + y)^2 = a^2*x*c^2 + y^2 + 2*a*c*√x*y := by
      ring_nf
      simp only [Real.sq_sqrt hx]
    rw [h1, h2]
    -- view it as a quadratic form of y
    suffices (a^2-1)*(y*y)+ (-2*a*c*√x)*y + (a^2 - a^2*c^2)*x ≥ 0 by
      linarith only [this]
    have ha3: a^2-1 > 0 := by
      apply sub_pos.mpr
      apply one_lt_pow₀ ha2 (by norm_num)
    -- rearrange
    have h3: (a^2-1)*(y*y)+ (-2*a*c*√x)*y + (a^2 - a^2*c^2)*x =
      (a^2-1)*(y - a*c*√x/(a^2-1))^2 +
      ((a^2 - a^2*c^2)*x - a^2*(c*√x)^2/(a^2-1)) := by
      field_simp [ha3.ne']
      ring
    -- simplify the latter term
    have h4: (a^2 - a^2*c^2)*x - a^2*(c*√x)^2/(a^2-1) =
      (a^2*x / (a^2-1)) * ((1-c^2)*(a^2-1) - c^2) := by
      field_simp [ha3.ne']
      ring_nf
      simp only [Real.sq_sqrt hx]
      ring
    -- by our choice of a, that term ≥ 0.
    have h5: (a^2*x / (a^2-1)) * ((1-c^2)*(a^2-1) - c^2) ≥ 0 := by
      apply mul_nonneg ?_ ?_
      · apply div_nonneg ?_ ha3.le
        apply mul_nonneg (sq_nonneg _) hx
      · linarith only [ha1]
    -- done.
    have h6: (a^2-1) * (y - a*c*√x/(a^2-1))^2 ≥ 0 := by
      apply mul_nonneg ha3.le (sq_nonneg _)
    rw [h3, h4]
    linarith only [h5,h6]