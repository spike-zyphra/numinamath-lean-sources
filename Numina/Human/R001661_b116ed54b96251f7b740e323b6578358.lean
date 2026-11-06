import Mathlib


open Real

/- tan (x+y) = (tan x + tan y) / (1 - tan x tan y) for non-singular point of tan function. -/
lemma l_tan_add_eq_of_cos_ne_zero {x y: ℝ}
  (hx: cos x ≠ 0) (hy: cos y ≠ 0):
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  apply tan_add' ?_
  constructor <;> rintro k rfl
  · absurd hx
    rw [cos_eq_zero_iff]
    use k
  · absurd hy
    rw [cos_eq_zero_iff]
    use k

/- similar as above, rephrase with condition tan x ≠ 0, tan y ≠ 0 -/
lemma l_tan_add_eq_of_tan_ne_zero {x y: ℝ}
  (hx: tan x ≠ 0) (hy: tan y ≠ 0):
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  rw [tan_eq_sin_div_cos, ne_eq, div_eq_zero_iff, not_or] at hx hy
  refine l_tan_add_eq_of_cos_ne_zero ?_ ?_
  <;> tauto

/- expand tan 3(arctan x) -/
lemma l_tan_three_mul_arctan {x: ℝ} (hx: x ≠ 0) (hx': |x| ≠ 1 / √3):
  tan (3*(arctan x)) = (3*x - x^3) / (1 - 3 * x^2) := by
  by_cases hhx: x^2 = 1
  · rw [sq_eq_one_iff] at hhx
    rcases hhx with hhx | hhx
    · have: arctan x = π / 4 := by
        rw [hhx, arctan_one]
      replace: 3 * arctan x = - (π / 4) + π := by
        rw [this]
        ring
      rw [this, tan_add_pi, tan_neg, tan_pi_div_four, hhx]
      ring
    · have: arctan x = - (π / 4) := by
        rw [hhx, arctan_neg, arctan_one]
      replace: 3 * arctan x = (π / 4) - π := by
        rw [this]
        ring
      rw [this, tan_sub_pi, tan_pi_div_four, hhx]
      ring
  · have h1: 3 * (arctan x) = 2 * (arctan x) + arctan x := by ring
    have h2: tan (2 * arctan x) ≠ 0 := by
      simp only [tan_two_mul, tan_arctan, ne_eq, div_eq_zero_iff,
      mul_eq_zero, OfNat.ofNat_ne_zero, hx, or_self, false_or]
      rw [← ne_eq] at hhx ⊢
      exact sub_ne_zero_of_ne hhx.symm
    rw [← tan_arctan x] at hx
    replace hx': 1 - 3*x^2 ≠ 0 := by
      suffices x^2 ≠ 1 / 3 by
        rintro heq
        absurd this
        linarith only [heq]
      rintro heq
      absurd hx'
      rw [← sq_abs] at heq
      have: 1 / 3 = (√(1/3))^2 := by
        rw [sq_sqrt (by norm_num)]
      rw [this, sq_eq_sq₀] at heq
      <;> simp [heq]
    field_simp [hx']
    rw [h1, l_tan_add_eq_of_tan_ne_zero h2 hx]
    simp only [tan_two_mul, tan_arctan]
    have h3: 1 - x^2 ≠ 0 := by
      apply sub_ne_zero_of_ne
      exact fun a => hhx (id (Eq.symm a))
    field_simp [h3]
    have: 1 - x^2 - 2*x*x = 1 - 3*x^2 := by ring
    rw [this]
    field_simp [hx']
    ring


/- if A+B+C = kπ, then tanA + tanB + tanC = tanA tanB tanC  -/
lemma l_tan_add_eq_tan_mul_of {A B C: ℝ}
  (h1: ∃ k:ℤ, A + B + C = k * π)
  (hA: tan A ≠ 0) (hB: tan B ≠ 0) (hC: tan C ≠ 0):
  tan A + tan B + tan C = tan A * tan B * tan C := by
  rcases h1 with ⟨k, hk⟩
  have h1 := l_tan_add_eq_of_tan_ne_zero hA hB
  replace hk: A + B = k*π - C := by
    rw [← hk]
    ring
  rw [hk, tan_int_mul_pi_sub] at h1
  have h2: 1 - tan A * tan B ≠ 0 := by
    rintro heq
    simp only [heq, div_zero, neg_eq_zero] at h1
    simp [h1] at hC
  field_simp [h2] at h1
  linarith only [h1]

/- re-size any number to - π /2, π / 2  -/
lemma tan_resize {x: ℝ} (hx: tan x ≠ 0):
  ∃ k:ℤ, - (π / 2) < k * π + x ∧ k*π + x < π / 2 := by
  have: x = x / π * π := by simp [pi_pos.ne']
  by_cases hk1: x / π ≥ ⌊x / π⌋ + 1/2
  · use (-⌊x / π⌋ - 1)
    constructor
    · suffices (⌊x / π⌋ + 1/2) * π < x by
        push_cast at this ⊢
        linarith only [this]
      rw [← lt_div_iff₀ pi_pos]
      apply lt_of_le_of_ne hk1 ?_
      rintro heq
      replace heq: x = (π / 2) + ⌊x/π⌋ * π := by
        nth_rw 1 [this, ← heq]
        ring
      rw [heq, tan_add_int_mul_pi, tan_pi_div_two] at hx
      norm_num at hx
    · push_cast
      suffices x < (⌊x / π⌋ + 3/2) * π by
        linarith only [this]
      nth_rw 1 [this]
      simp only [pi_pos, mul_lt_mul_right]
      linarith only [Int.lt_floor_add_one (x / π)]
  · push_neg at hk1
    use (- ⌊x / π⌋)
    constructor
    · suffices (⌊x / π⌋ - 1/2) * π < x by
        push_cast
        linarith only [this]
      nth_rw 2 [this]
      simp only [pi_pos, mul_lt_mul_right]
      linarith only [Int.floor_le (x / π)]
    · suffices x < (⌊x/π⌋ + 1/2) * π by
        push_cast
        linarith only [this]
      nth_rw 1 [this]
      simp only [pi_pos, mul_lt_mul_right, hk1]


/- the other direction. if tan A + tan B + tan C = tanA tanB tanC,
we may claim A + B + C = k π  -/
lemma l_add_to_int_mul_pi_of {A B C: ℝ}
  (h1: tan A + tan B + tan C = tan A * tan B * tan C)
  (hA: tan A ≠ 0) (hB: tan B ≠ 0) (hC: tan C ≠ 0):
  ∃ k:ℤ, A + B + C = k * π := by
  replace h1: tan C * (1 - tan A * tan B) = - (tan A + tan B) := by
    linarith only [h1]
  have h2: tan A * tan B ≠ 1 := by
    rintro h2
    simp only [h2, sub_self, mul_zero, neg_add_rev] at h1
    replace h1: tan A = - tan B := by linarith only [h1]
    simp only [h1, neg_mul, ← pow_two] at h2
    linarith only [sq_nonneg (tan B), h2]
  have h3 := l_tan_add_eq_of_tan_ne_zero hA hB
  have h3': tan (A + B) ≠ 0 := by
    rw [h3]
    replace h2: 1 - tan A * tan B ≠ 0:= by
      apply sub_ne_zero_of_ne h2.symm
    have: tan A + tan B ≠ 0 := by
      by_contra!
      simp [this, hC, h2] at h1
    simp [h2, this]
  replace h1: tan C = -(tan A + tan B) / (1 - tan A * tan B) := by
    replace h2: 1 - tan A * tan B ≠ 0 := by
      apply sub_ne_zero_of_ne h2.symm
    exact eq_div_of_mul_eq h2 h1
  replace h1: tan C = - tan (A+B) := by
    rw [h3, h1]
    ring
  have h4: ∃ k1:ℤ, -(π / 2) < k1 * π - C ∧ k1 * π - C < π / 2 := by
    replace hC: tan (-C) ≠ 0 := by
      simp [hC]
    rcases (tan_resize hC) with ⟨k1, hk1⟩
    use k1
    exact hk1
  have h5: ∃ k2:ℤ, -(π / 2) < k2 * π + (A + B) ∧ k2 * π + (A+B) < π / 2 := by
    apply tan_resize h3'
  rcases h4 with ⟨k1, hk1⟩
  rcases h5 with ⟨k2, hk2⟩
  use (k1-k2)
  suffices k1*π - C = k2*π + (A+B) by
    push_cast at this ⊢
    linarith only [this]
  apply tan_inj_of_lt_of_lt_pi_div_two hk1.left hk1.right hk2.left hk2.right ?_
  rw [tan_int_mul_pi_sub, add_comm _ (A+B), tan_add_int_mul_pi, h1, neg_neg]


/- 9. II 3 (CUB 3) Let $x, y, z$ be real numbers each of whose absolute value is different from $1 / \sqrt{3}$ such that $x+y+z=x y z$. Prove that  $$ \frac{3 x-x^{3}}{1-3 x^{2}}+\frac{3 y-y^{3}}{1-3 y^{2}}+\frac{3 z-z^{3}}{1-3 z^{2}}=\frac{3 x-x^{3}}{1-3 x^{2}} \cdot \frac{3 y-y^{3}}{1-3 y^{2}} \cdot \frac{3 z-z^{3}}{1-3 z^{2}} $$ -/
theorem algebra_25035 {x y z : ℝ} (hx : |x| ≠ 1 / √3) (hy : |y| ≠ 1 / √3)
    (hz : |z| ≠ 1 / √3) (h : x + y + z = x * y * z) :
    (3 * x - x ^ 3) / (1 - 3 * x ^ 2) + (3 * y - y ^ 3) / (1 - 3 * y ^ 2) +
    (3 * z - z ^ 3) / (1 - 3 * z ^ 2) =
    (3 * x - x ^ 3) / (1 - 3 * x ^ 2) * (3 * y - y ^ 3) / (1 - 3 * y ^ 2) *
    (3 * z - z ^ 3) / (1 - 3 * z ^ 2) := by

  -- first, we work on one of them eq zero case.
  have case_two_variable {a b: ℝ} (ha: |a| ≠ 1 / √3) (hb: |b| ≠ 1 / √3)
    (heq: a + b = 0):
    (3*a - a^3) / (1 - 3*a^2) + (3*b - b^3) / (1 - 3*b^2) = 0 := by
    have h1: a = -b := by linarith only [heq]
    have h2: a^3 = - b^3 := by
      rw [h1, Odd.neg_pow (Nat.odd_iff.mpr rfl)]
    have h3: a^2 = b^2 := by
      rw [h1, neg_sq]
    rw [h2, h3, h1]
    ring

  -- then x,y,z = 0 case is easy.
  by_cases hhx: x = 0
  · simp only [hhx, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sub_self, sub_zero,
    div_one, zero_add, zero_mul, zero_div]
    apply case_two_variable hy hz ?_
    simpa only [hhx, zero_add, zero_mul] using h
  by_cases hhy: y = 0
  · simp only [hhy, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sub_self,
    sub_zero, div_one, add_zero, zero_mul, zero_div]
    apply case_two_variable hx hz ?_
    simpa only [hhy, add_zero, mul_zero, zero_mul] using h
  by_cases hhz: z = 0
  · simp only [hhz, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sub_self, sub_zero, div_one, add_zero]
    apply case_two_variable hx hy ?_
    simpa only [hhz, add_zero, mul_zero] using h
  rw [← ne_eq] at hhx hhy hhz

  -- focus on x,y,z ≠ 0 case, turn (3x - x^3)/(1-3x^2) to tan (arctan 3x).
  rw [← l_tan_three_mul_arctan hhx hx, mul_div_assoc,
  mul_div_assoc, ← l_tan_three_mul_arctan hhy hy,
  ← l_tan_three_mul_arctan hhz hz]

  -- also, we can work out some arctan x = π / 3 case.
  have case_two_variable' {a b: ℝ} (hh: ∃ k:ℤ, a + b = k*π):
    tan a + tan b = 0 := by
    rcases hh with ⟨k, hk⟩
    replace hk: a = k*π - b := by linarith only [hk]
    simp [hk, tan_int_mul_pi_sub]

  -- suffices arctan x + arctan y + arctan z = k π.
  suffices heq: ∃ k:ℤ, arctan x + arctan y + arctan z = k*π by
    rcases heq with ⟨k, heq⟩
    have h1: 3*arctan x + 3*arctan y + 3*arctan z = (3*k:ℤ) * π := by
      push_cast
      rw [mul_assoc, ← heq]
      ring

    -- some of them eq π /3 case we already solve.
    by_cases hhx': ∃ d:ℤ, 3 * arctan x = d * π
    · rcases hhx' with ⟨d, hd⟩
      simp only [hd, tan_int_mul_pi, zero_add, zero_mul]
      apply case_two_variable'
      use (3*k-d)
      rw [hd] at h1
      push_cast at h1 ⊢
      linarith only [h1]
    by_cases hhy': ∃ d:ℤ, 3 * arctan y = d * π
    · rcases hhy' with ⟨d, hd⟩
      simp only [hd, tan_int_mul_pi, add_zero, mul_zero, zero_mul]
      apply case_two_variable'
      use (3*k-d)
      rw [hd] at h1
      push_cast at h1 ⊢
      linarith only [h1]
    by_cases hhz': ∃ d:ℤ, 3 * arctan z = d * π
    · rcases hhz' with ⟨d, hd⟩
      simp only [hd, tan_int_mul_pi, add_zero, mul_zero, zero_mul]
      apply case_two_variable'
      use (3*k-d)
      rw [hd] at h1
      push_cast at h1 ⊢
      linarith only [h1]

    -- absolute value ≠ 1 / √3, then its arctan ≠ π/6 or - π /6
    have h2 {d:ℤ} {r: ℝ} (hr1: r ≠ 0) (hr2: |r| ≠ 1 / √3):
      3 * arctan r ≠ (2*d+1) * π / 2 := by
      rintro hh
      replace hh: arctan r = (d/3 + 1/6) * π := by
        linarith only [hh]
      have h21 := arctan_mem_Ioo r
      simp only [Set.mem_Ioo] at h21
      have h22: 0 < (d+2)/3 * π := by
        rw [hh] at h21
        linarith only [h21.left]
      simp only [pi_pos, mul_pos_iff_of_pos_right, Nat.ofNat_pos,
      div_pos_iff_of_pos_right] at h22
      have h23: (d-1)/3 * π < 0 := by
        rw [hh] at h21
        linarith only [h21.right]
      replace h23: (d-1:ℝ) < 0 := by
        suffices (d-1:ℝ)/3 < 0 by
          apply neg_of_div_neg_left this (by norm_num)
        exact (neg_iff_pos_of_mul_neg h23).mpr pi_pos
      norm_cast at h22 h23
      obtain (deq | deq): d = 0 ∨ d = -1 := by omega
      · have: r = 1 / √3 := by
          rw [← tan_arctan r, hh, deq]
          simp only [Int.cast_zero, zero_div, zero_add]
          rw [one_div, inv_mul_eq_div, tan_pi_div_six]
        simp [this] at hr2
      · have: r = - (1 / √3) := by
          rw [← tan_arctan r]
          have: arctan r = - (π / 6) := by
            simp only [hh, deq, Int.reduceNeg, Int.cast_neg, Int.cast_one]
            ring
          rw [this, tan_neg, tan_pi_div_six]
        simp [this] at hr2

    -- again, we claim tan(3A) + tan(3B) + tan(3C) = tan3A tan3B tan3C if 3A+3B+3C = kπ.
    push_neg at hhx' hhy' hhz'
    apply l_tan_add_eq_tan_mul_of ⟨3*k, h1⟩ ?_ ?_ ?_
    all_goals
      rw [ne_eq, tan_eq_zero_iff]
      rintro ⟨d, hd⟩
      rcases (Int.even_or_odd' d) with ⟨d', deq⟩
      rcases deq with deq | deq
      <;> rw [deq] at hd <;> push_cast at hd
    · specialize hhx' d'
      rw [← hd] at hhx'
      absurd hhx'
      ring
    · absurd hd; push_neg; symm
      apply h2 hhx hx
    · specialize hhy' d'
      absurd hhy'
      rw [← hd]
      ring
    · absurd hd; push_neg; symm
      apply h2 hhy hy
    · specialize hhz' d'
      absurd hhz'
      rw [← hd]
      ring
    · absurd hd; push_neg; symm
      apply h2 hhz hz


  -- then we claim it follows from x+y+z = xyz
  apply l_add_to_int_mul_pi_of
  <;> simp [hhx, hhy, hhz, h]