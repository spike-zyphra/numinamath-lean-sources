import Mathlib


/- Let $f(x)$ and $g(x)$ be given by

$$
f(x)=\frac{1}{x}+\frac{1}{x-2}+\frac{1}{x-4}+\cdots+\frac{1}{x-2018}
$$

and

$$
g(x)=\frac{1}{x-1}+\frac{1}{x-3}+\frac{1}{x-5}+\cdots+\frac{1}{x-2017} .
$$

Prove that

$$
|f(x)-g(x)|>2
$$

for any non-integer real number $x$ satisfying $0 < x < 2018$. -/
theorem algebra_605885 {f g : ℝ → ℝ}
    (hf : ∀ x, f x = ∑ i ∈ Finset.range 1010, 1 / (x - 2 * i))
    (hg : ∀ x, g x = ∑ i ∈ Finset.range 1009, 1 / (x - 2 * i - 1)) :
    ∀ (x:ℝ), 0 < x ∧ x < 2018 → (∀z:ℤ, x ≠ z) → |f x - g x| > 2 := by

  rintro x ⟨xlb,xub⟩ x_not_int


  -- for 1 < y < 2, we can prove 1/(y(y-1)) + 1 / (y-2)(y-3)  > 2.
  have ineq {y:ℝ} (hy: 1 < y ∧ y < 2):
    1 / (y*(y-1)) + 1 / ((y-2)*(y-3)) > 2 := by
    have ynz: y ≠ 0 := by
      symm; apply ne_of_lt
      linarith only [hy.left]
    have y1nz: y-1 ≠ 0 := by
      rintro heq
      have: y = 1 := by linarith only [heq]
      simp [this] at hy
    have y2nz: y-2 ≠ 0 := by
      rintro heq
      have: y = 2 := by linarith only [heq]
      simp [this] at hy
    have y3nz: y-3 ≠ 0 := by
      apply ne_of_lt
      linarith only [hy.right]
    -- notice that 1 / (y(y-1)) = 1/(y-1) - 1/y
    -- put 1/(y-1),1/(y-2) together, the other two terms together.
    have h1: 1/ (y*(y-1)) + 1 / ((y-2)*(y-3)) =
      1/((y-1)*(2-y)) + 3/(y*(y-3)) := by
      have: 2-y ≠ 0 := by
        refine sub_ne_zero_of_ne ?_
        exact (sub_ne_zero.mp y2nz).symm
      field_simp [ynz, y1nz, y2nz, y3nz, this]
      ring
    rw [h1]
    -- for 1 < y < 2, 1/((y-1)(2-y) ≥ 4
    -- use HM-GM, or write it in quadratic form.
    have h2: 1 / ((y-1)*(2-y)) ≥ 4 := by
      have: (4:ℝ) = 1/(1/4) := by norm_num
      rw [this]
      apply one_div_le_one_div_of_le ?_ ?_
      · apply mul_pos
        <;> linarith only [hy]
      · linarith only [sq_nonneg (y - 3/2)]
    -- and 3 / (y(y-3)) ≥ -3/2
    -- write in quadratic form, and notice 1 < y < 2.
    have h3: 3 / (y*(y-3)) ≥ -3/2 := by
      have: y*(y-3) < 0 := by
        apply mul_neg_of_pos_of_neg
        <;> linarith only [hy]
      refine (le_div_iff_of_neg' this).mpr ?_
      suffices (y-3/2)^2 ≤ (1/2)^2 by
        linarith only [this]
      rw [sq_le_sq, abs_le, abs_of_nonneg (by norm_num)]
      constructor <;> linarith only [hy]
    -- done
    linarith only [h2, h3]

  -- for 0 < y < 1, 1/y + 1/((y-2)(y-1)) > 2
  have ineq' {y:ℝ} (hy: 0 < y ∧ y < 1):
    1/y + 1 / ((y-2)*(y-1)) > 2 := by
    have: 1/y + 1 / ((y-2)*(y-1)) = 1/(y*(1-y)) - 1/(2-y) := by
      have y2nz: y-2 ≠ 0 := by
        apply ne_of_lt
        linarith only [hy]
      have y1nz: y-1 ≠ 0 := by
        apply ne_of_lt
        linarith only [hy]
      have ynz: y ≠ 0 := hy.left.ne'
      have y2nz': 2-y ≠ 0 := by
        symm; apply ne_of_lt
        linarith only [hy]
      have y1nz': 1-y ≠ 0 := by
        symm; apply ne_of_lt
        linarith only [hy]
      field_simp [y2nz, y1nz, ynz, y1nz', y2nz']
      ring
    rw [this]
    -- by HM-GM or write in quadratic form, 1/(y(1-y)) ≥ 4.
    have h1: 1 / (y*(1-y)) ≥ 4 := by
      have: (4:ℝ) = 1/(1/4) := by norm_num
      rw [this]
      apply one_div_le_one_div_of_le ?_ ?_
      · apply mul_pos
        <;> linarith only [hy]
      · nlinarith only [sq_nonneg (y-1/2)]
    -- 2-y ≥ 1, since y < 1.
    have h2: 1/(2-y) ≤ 1 := by
      apply (div_le_one₀ ?_).mpr ?_
      <;> linarith only [hy]
    linarith only [h1,h2]

  -- we consider an index i near x.
  obtain ⟨i0, hi0⟩: ∃ (i:ℕ), 2*i < x ∧ x < 2*(i+1) := by
    rcases (Nat.even_or_odd' ⌊x⌋₊) with ⟨i, (hi | hi)⟩
    · use i
      rify at hi
      constructor
      · rw [← hi]
        apply lt_of_le_of_ne ?_ ?_
        · apply Nat.floor_le xlb.le
        · apply (x_not_int _).symm
      · have: x < 2*i+1 := by
          rw [← hi]
          exact Nat.lt_floor_add_one x
        apply this.trans (by linarith only)
    · use i
      rify at hi
      constructor
      · have: 2*i+1 < x := by
          rw [← hi]
          apply lt_of_le_of_ne ?_ ?_
          · apply Nat.floor_le xlb.le
          · apply (x_not_int _).symm
        apply lt_trans (by simp) this
      · apply lt_of_lt_of_le (Nat.lt_floor_add_one x) ?_
        rw [hi]
        apply le_of_eq (by ring)

  -- x must be between 2i0 and 2(i0+1) for some i0.
  -- cases on relation of x to 2i0+1
  by_cases hx: x < 2*i0 + 1
  · set ff: ℝ → ℝ := fun y => ∑ i ∈ Finset.range 1009,
      1 / (y - 2*(1+i)) with ff_def
    have hff: f x = 1/x + ff x := by
      simp only [ff_def, hf x]
      have: 1010 = 1 + 1009 := by norm_num
      rw [this, Finset.sum_range_add]
      simp
    have hfg1: ff x - g x = ∑ i ∈ Finset.range 1009, 1 / ((x-2-2*i)*(x-2*i-1)) := by
      simp only [ff_def, hg x]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl (fun i hi => ?_)
      simp only [mul_add, mul_one, ← sub_sub]
      have h1: x-2-2*i ≠ 0 := by
        specialize x_not_int (2*i+2)
        rw [sub_sub, add_comm 2 _]
        push_cast at x_not_int
        exact sub_ne_zero_of_ne x_not_int
      have h2: x-2*i-1 ≠ 0 := by
        rw [sub_sub]
        specialize x_not_int (2*i+1)
        push_cast at x_not_int
        apply sub_ne_zero_of_ne x_not_int
      field_simp [h1, h2]
      ring
    -- each term ≥ 0
    have hfg_nng: ∀i ∈ Finset.range 1009,
      0 ≤ 1 / ((x-2-2*i)*(x-2*i-1)) := by
      intro i hi
      rw [one_div_nonneg]
      apply le_of_lt
      by_cases i0eq: i0 = 0
      · simp only [i0eq, CharP.cast_eq_zero, mul_zero,
        zero_add, mul_one] at hi0 hx
        apply mul_pos_of_neg_of_neg ?_ ?_
        <;> linarith only [hx]
      replace i0eq: 1 ≤ i0 := Nat.one_le_iff_ne_zero.mpr i0eq
      by_cases hhi: i ≤ i0-1
      · rify at hhi
        simp only [Nat.cast_sub i0eq, Nat.cast_one] at hhi
        apply mul_pos ?_ ?_
        <;> linarith only [hi0.left, hhi]
      · replace hhi: i ≥ i0 := by omega
        rify at hhi
        apply mul_pos_of_neg_of_neg ?_ ?_
        · linarith only [hi0.right, hhi]
        · linarith only [hx, hhi]
    -- then terms inside absolute value ≥ 0, and we can remove it.
    have hfg2: |f x - g x| = f x - g x := by
      apply abs_of_nonneg ?_
      rw [hff, add_sub_assoc]
      apply add_nonneg (by simp [xlb.le]) ?_
      rw [hfg1]
      apply Finset.sum_nonneg hfg_nng
    -- if i0 = 0, consider 1/x - 1/(x-1) + 1/(x-2)
    -- we prove it > 2, and other term ≥ 0.
    by_cases i0eq: i0 = 0
    · rw [hfg2, hff, add_sub_assoc, hfg1]
      simp only [i0eq, CharP.cast_eq_zero, mul_zero,
      zero_add, mul_one] at hx hi0
      have: i0 ∈ Finset.range 1009 := by
        simp [Finset.mem_range, i0eq]
      rw [← Finset.insert_erase this, Finset.sum_insert (by simp), ← add_assoc]
      have h1: 1 / x + 1 / ((x - 2 - 2 * i0) * (x - 2 * i0 - 1)) > 2 := by
        simp only [i0eq, CharP.cast_eq_zero, mul_zero, sub_zero]
        apply ineq' ⟨hi0.left,hx⟩
      have h2: 0 ≤  ∑ i ∈ (Finset.range 1009).erase i0,
        1 / ((x-2-2*i)*(x-2*i-1)) := by
        apply Finset.sum_nonneg (fun i hi => ?_)
        apply hfg_nng i
        clear * - hi
        simp_all only [Finset.mem_erase, ne_eq, Finset.mem_range]
      linarith only [h1,h2]
    -- else, consider i0 and i0-1 term.
    -- use inequality 1/(x(x-1)) + 1/((x-2)(x-3)) > 2, and other terms ≥ 0.
    · replace i0eq: 1 ≤ i0 := by omega
      -- if i0 ≠ 0, choose term i0-1, i0 out.
      have h1: i0 ∈ Finset.range 1009 := by
        simp only [Finset.mem_range]
        rify
        linarith only [xub, hi0]
      have h2: i0-1 ∈ (Finset.range 1009).erase i0 := by
        simp only [Finset.mem_erase, ne_eq, Finset.mem_range]
        refine ⟨(by omega), ?_⟩
        rify
        rw [Nat.cast_sub i0eq]
        linarith only [xub, hi0]
      suffices ff x - g x > 2 by
        rw [hfg2, hff]
        have h: 0 < 1/x := by simp [xlb]
        linarith only [this, h]
      rw [hfg1, ← Finset.insert_erase h1, Finset.sum_insert (by simp),
      ← Finset.insert_erase h2, Finset.sum_insert (by simp), ← add_assoc]
      rw [Nat.cast_sub i0eq]
      push_cast
      have h3: 1 / ((x - 2 - 2 * i0) * (x - 2 * i0 - 1)) +
        1 / ((x - 2 - 2 * (i0 - 1)) * (x - 2 * (i0 - 1) - 1)) > 2 := by
        have: 1 / ((x - 2 - 2 * i0) * (x - 2 * i0 - 1)) +
          1 / ((x - 2 - 2 * (i0 - 1)) * (x - 2 * (i0 - 1) - 1)) =
          1 / ( (x-2*i0+1) * (x-2*i0+1-1) ) +
          1 / ( (x-2*i0+1-2) * (x-2*i0+1-3)) := by ring
        rw [this]
        apply ineq
        constructor <;> linarith only [hi0, hx]
      have h4: 0 ≤ ∑ i ∈ ((Finset.range 1009).erase i0).erase (i0 - 1),
        1 / ((x - 2 - 2 * i) * (x - 2 * i - 1)) := by
        apply Finset.sum_nonneg (fun i hi => ?_)
        apply hfg_nng i
        clear * - hi
        simp_all only [Finset.mem_erase, ne_eq, Finset.mem_range]
      linarith only [h3, h4]


  -- for the other case, we argue in a similar way.
  -- single out terms near x, and prove that > 2, with other terms ≥ 0.
  · replace hx: 2*i0+1 < x := by
      apply lt_of_le_of_ne ?_ ?_
      · apply le_of_not_lt hx
      · specialize x_not_int (2*i0+1)
        push_cast at x_not_int
        exact x_not_int.symm
    set gg: ℝ → ℝ := fun y => ∑ i ∈ Finset.range 1010,
      1 / (y - 2*i - 1) with gg_def
    have hgg: g x = - 1 / (x - 2019) + gg x := by
      simp only [gg_def, hg x]
      rw [Finset.sum_range_succ _ 1009]
      push_cast
      ring
    have hfg1: gg x - f x =
      ∑ i ∈ Finset.range 1010, 1 / ((x-2*i)*(x-2*i-1)) := by
      simp only [gg_def, hf x]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl (fun i hi => ?_)
      have h1: x - 2*i - 1 ≠ 0 := by
        rw [sub_sub]
        specialize x_not_int (2*i+1)
        push_cast at x_not_int
        apply sub_ne_zero_of_ne x_not_int
      have h2: x - 2*i ≠ 0 := by
        specialize x_not_int (2*i)
        push_cast at x_not_int
        apply sub_ne_zero_of_ne x_not_int
      field_simp [h1, h2]
      ring
    have hfg_nng: ∀ i ∈ Finset.range 1010,
      0 ≤ 1 / ((x-2*i)*(x-2*i-1)) := by
      intro i hi
      rw [one_div_nonneg]
      apply le_of_lt ?_
      by_cases hhi: i ≤ i0
      · rify at hhi
        apply mul_pos
        <;> linarith only [hhi, hx]
      · replace hhi: i ≥ i0+1 := by omega
        rify at hhi
        apply mul_pos_of_neg_of_neg
        <;> linarith only [hi0.right,hhi]
    -- in this case, fx - gx < 0.
    -- and after take absolute value, we get gx - fx.
    have hfg2: |f x - g x| = -  1 / (x-2019) + (gg x - f x) := by
      rw [abs_sub_comm, hgg, add_sub_assoc]
      apply abs_of_nonneg
      apply add_nonneg ?_ ?_
      · simp only [neg_div, one_div, Left.nonneg_neg_iff,
        inv_nonpos, tsub_le_iff_right, zero_add]
        linarith only [xub]
      · rw [hfg1]
        apply Finset.sum_nonneg hfg_nng
    replace hfg2: |f x - g x| > gg x - f x := by
      simp only [hfg2, neg_div, one_div, gt_iff_lt, lt_add_iff_pos_left,
      Left.neg_pos_iff, inv_neg'', sub_neg]
      linarith only [xub]
    -- take i0,i0+1 term out.
    have h1: i0 ∈ Finset.range 1010 := by
      simp only [Finset.mem_range]
      rify
      linarith only [xub, hi0]
    have h2: i0+1 ∈ (Finset.range 1010).erase i0 := by
      simp only [Finset.mem_erase, ne_eq, add_right_eq_self,
      one_ne_zero, not_false_eq_true, Finset.mem_range, true_and]
      rify
      linarith only [xub, hi0]
    apply lt_trans ?_ hfg2
    rw [hfg1, ← Finset.insert_erase h1, Finset.sum_insert (by simp),
    ← Finset.insert_erase h2, Finset.sum_insert (by simp), ← add_assoc]
    push_cast
    have h3: 2 < 1 / ((x-2*i0)*(x-2*i0-1)) +
      1 / ((x-2*(i0+1)) * (x-2*(i0+1)-1)) := by
      have hh1: x-2*(i0+1) = x-2*i0-2 := by ring
      have hh2: x-2*(i0+1)-1 = x-2*i0-3 := by ring
      rw [hh2, hh1]
      apply ineq
      constructor <;> linarith only [hi0, hx]
    have h4: 0 ≤ ∑ i ∈ ((Finset.range 1010).erase i0).erase (i0+1),
      1 / ((x-2*i)*(x-2*i-1)) := by
      apply Finset.sum_nonneg (fun i hi => ?_)
      apply hfg_nng i
      clear * - hi
      simp_all only [Finset.mem_erase, ne_eq, Finset.mem_range]
    linarith only [h3, h4]