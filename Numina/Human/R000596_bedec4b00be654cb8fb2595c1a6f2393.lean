import Mathlib

/- The real numbers $a,$ $b,$ $c,$ and $d$ satisfy
\[a^2 + b^2 + c^2 + 1 = d + \sqrt{a + b + c - d}.\]Find $d.$-/
theorem algebra_13092 {a b c d : ℝ} (h : a^2 + b^2 + c^2 + 1 = d + Real.sqrt (a + b + c - d)) (hnonneg : 0 ≤ a + b + c - d) :
    d = 5 / 4 := by
  -- Let $x = \sqrt{a + b + c - d}.$
  set x : ℝ := Real.sqrt (a + b + c - d)
  -- Then $x^2 = a + b + c - d,$
  have hxsq : x ^ 2 = a + b + c - d := Real.sq_sqrt hnonneg
  -- so $d = a + b + c - x^2,$
  have hd : d = a + b + c - x ^ 2 := by linear_combination hxsq
  rw [hd] at h
  -- and we can write
  -- \[a^2 + b^2 + c^2 + 1 = a + b + c - x^2 + x.\]
  replace h : a ^ 2 - a + b ^ 2 - b + c ^ 2 - c + x ^ 2 - x + 1 = 0 := by linear_combination h
  -- Then
  -- \[a^2 - a + b^2 - b + c^2 - c + x^2 - x + 1 = 0.\]
  -- Completing the square in $a,$ $b,$ $c,$ and $x,$ we get
  -- \[\left( a - \frac{1}{2} \right)^2 + \left( b - \frac{1}{2} \right)^2 + \left( c - \frac{1}{2} \right)^2 + \left( x - \frac{1}{2} \right)^2 = 0.\]
  replace h : (a - 1 / 2) ^ 2 + (b - 1 / 2) ^ 2 + (c - 1 / 2) ^ 2 + (x - 1 / 2) ^ 2 = 0 := by linear_combination h
  -- We need the following data and proposition to use lemma `Finset.sum_eq_zero_iff_of_nonneg`.
  let f : ℕ → ℝ := fun n => match n with
    | 0 => (a - 1 / 2) ^ 2
    | 1 => (b - 1 / 2) ^ 2
    | 2 => (c - 1 / 2) ^ 2
    | 3 => (x - 1 / 2) ^ 2
    | _ => 0 -- junk value
  let s : Finset ℕ := Finset.range 4
  have hfnonneg : ∀ i ∈ s, 0 ≤ f i := by
    intro i hi
    simp [s] at hi
    interval_cases i
    all_goals simp [f]; positivity
  have hfsum_eq_zero : ∑ i ∈ s, f i = 0 := by
    simp [s, Finset.sum_range_succ, f]
    convert h using 1
    congr
    all_goals norm_num
  rw [Finset.sum_eq_zero_iff_of_nonneg hfnonneg] at hfsum_eq_zero
  -- Hence, $a = b = c = x = \frac{1}{2},$
  have ha : a = 1 / 2 := by
    specialize hfsum_eq_zero 0 (by simp [s])
    simp [f] at hfsum_eq_zero
    linear_combination hfsum_eq_zero
  have hb : b = 1 / 2 := by
    specialize hfsum_eq_zero 1 (by simp [s])
    simp [f] at hfsum_eq_zero
    linear_combination hfsum_eq_zero
  have hc : c = 1 / 2 := by
    specialize hfsum_eq_zero 2 (by simp [s])
    simp [f] at hfsum_eq_zero
    linear_combination hfsum_eq_zero
  have hx : x = 1 / 2 := by
    specialize hfsum_eq_zero 3 (by simp [s])
    simp [f] at hfsum_eq_zero
    linear_combination hfsum_eq_zero
  -- so
  -- \[d = a + b + c - x^2 = \frac{1}{2} + \frac{1}{2} + \frac{1}{2} - \frac{1}{4} = \boxed{\frac{5}{4}}.\]
  norm_num [hd, ha, hb, hc, hx]
