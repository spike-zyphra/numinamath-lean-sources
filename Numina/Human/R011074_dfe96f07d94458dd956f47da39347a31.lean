import Mathlib


/- a) Solve the equation $x^{4}-y^{4}=16$ in the set of integers. -/
theorem algebra_120738_1 {x y: ℤ}:
  x^4 - y^4 = 16 ↔ ((x=2 ∨ x=-2) ∧ y=0) := by
  constructor
  · have: x^4 - y^4 = (x^2 - y^2)*(x^2+y^2) := by ring
    rw [this]
    intro heq
    have h1: x^2 + y^2 > 0 := by
      apply lt_of_le_of_ne ?_ ?_
      · linarith only [sq_nonneg x, sq_nonneg y]
      · rintro h
        simp [← h] at heq
    have h2: x^2 - y^2 > 0 := by
      replace: (x^2 - y^2) * (x^2 + y^2) > 0 := by
        norm_num [heq]
      exact (pos_iff_pos_of_mul_pos this).mpr h1
    have h3: x^2 + y^2 ≥ x^2 - y^2 := by
      linarith only [sq_nonneg y]
    replace h3: x^2 + y^2 ≥ 4 := by
      by_contra! hh1
      have hh2: x^2 - y^2 < 4 := by linarith only [h3, hh1]
      replace: (x^2 - y^2) * (x^2 + y^2) < 4 * 4 := by
        refine Int.mul_lt_mul hh2 hh1.le h1 (by norm_num)
      simp [heq] at this
    have hdvd: x^2 + y^2 ∣ 16 := by
      rw [← heq]
      apply Int.dvd_mul_left
    -- 16 = 2^4, 2 is prime.
    -- so its factor can only be 2^i for some i.
    -- therefore x^2 + y^2 = 4,8,16
    replace: ∀n:ℤ, n ≥ 4 → n ≤ 16 → n ∣ 16 →
      n = 4 ∨ n = 8 ∨ n = 16 := by decide
    specialize this (x^2+y^2) h3 (Int.le_of_dvd (by norm_num) hdvd) hdvd
    rcases this with eq4 | eq8 | eq16
    · -- x^2 + y^2 = 4, we solve x^2 - y^2 = 4. x = 2,-2, y = 0
      rw [eq4] at heq
      replace heq: x^2 - y^2 = 4 := by linarith only [heq]
      have yeq: y = 0 := by
        have: y^2 = 0 := by linarith only [eq4, heq]
        exact pow_eq_zero this
      have xeq: x^2 = 2^2 := by
        rw [yeq] at eq4
        linarith only [eq4]
      rw [sq_eq_sq_iff_eq_or_eq_neg] at xeq
      exact ⟨xeq, yeq⟩
    · -- x^2 + y^2 = 8, we solve x^2 - y^2 = 2. impossible.
      rw [eq8] at heq
      replace heq: x^2 - y^2 = 2 := by linarith only [heq]
      have: x^2 = 5 := by linarith only [eq8, heq]
      rw [← abs_sq, abs_pow] at this
      have hh1: 2^2 < |x|^2 := by norm_num [this]
      have hh2: |x|^2 < 3^2 := by norm_num [this]
      rw [pow_lt_pow_iff_left₀ (by norm_num)
      (abs_nonneg _) (by norm_num)] at hh1
      rw [pow_lt_pow_iff_left₀ (abs_nonneg _)
      (by norm_num)  (by norm_num)] at hh2
      omega
    · -- x^2 + y^2 = 16, we solve x^2 - y^2 = 1
      rw [eq16] at heq
      replace heq: x^2 - y^2 = 1 := by linarith only [heq]
      have: 2*x^2 = 17 := by linarith only [eq16, heq]
      -- impossible for 2 divide 17.
      omega
  · rintro ⟨(rfl | rfl), rfl⟩
    <;> norm_num


/- b) Find the largest natural number $n$ for which $\frac{n^{2}-2012}{n+1} \in \mathbb{Z}$. -/
theorem algebra_120738_2:
  IsGreatest {n:ℕ | ∃ (m:ℤ), m = (n^2-2012:ℚ)/(n+1)} 2010 := by
  rw [IsGreatest, upperBounds]
  simp only [Set.mem_setOf_eq, Int.cast_ofNat, forall_exists_index]
  have (n:ℕ): (n^2 - 2012:ℚ)/(n+1) = n - 1 - 2011/(n+1) := by
    have: n+1 > 0 := by simp
    qify at this
    field_simp [this.ne']
    ring
  constructor
  -- for n - 1 - 2011/(n+1) be integer, 2011 / (n+1) must be integer
  -- so largest n is 2010, and 2010 - 1 - 2011/(2010+1) = 2008
  · rw [this 2010]
    use 2008
    norm_num
  · intro n m h
    rw [this n] at h
    have: (n+1:ℤ) ∣ 2011 := by
      use (n-1-m)
      qify
      have: n+1 > 0 := by simp
      field_simp [this.ne'] at h
      linarith only [h]
    replace: (n+1:ℤ) ≤ 2011 := by
      apply Int.le_of_dvd (by norm_num) this
    replace: (n:ℤ) ≤ 2010 := by linarith only [this]
    norm_cast at this


/- c) Find the real numbers $a$ and $b$ if $\max \left\{a^{2}-b+1, b^{2}+a+1\right\} \leq \frac{3}{4}$. -/
theorem algebra_120738_3 {a b: ℝ}:
  max (a^2-b+1) (b^2+a+1) ≤ 3/4 ↔ a = -1/2 ∧ b = 1/2 := by
  constructor <;> intro h
  · have: a^2-b+1 + (b^2+a+1) ≤ 3/4 + 3/4 := by
      apply add_le_add <;> apply le_trans ?_ h
      <;> simp only [le_sup_left, le_sup_right]
    replace: (a+1/2)^2 + (b-1/2)^2 ≤ 0 := by linarith only [this]
    replace: (a+1/2)^2 + (b-1/2)^2 = 0 := by
      apply le_antisymm this ?_
      linarith only [sq_nonneg (a+1/2), sq_nonneg (b-1/2)]
    simp only [pow_two, mul_self_add_mul_self_eq_zero] at this
    constructor <;> linarith only [this]
  · rw [h.left, h.right]
    norm_num