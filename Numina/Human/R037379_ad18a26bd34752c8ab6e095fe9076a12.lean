import Mathlib

-- Let $\left[ x \right]$ denote the greatest integer not exceeding $x$, then $\sum\limits_{k=0}^{2012}{\left[ \frac{2012+{{2}^{k}}}{{{2}^{k+1}}} \right]}=$ ___          ___ .
theorem algebra_626184 : ∑ k ∈ Finset.Icc 0 2012, ⌊((2012 + 2 ^ k) / 2 ^ (k + 1) : ℝ)⌋ = 2012 := by
  -- From the identity $\left[ x+\frac{1}{2} \right]=\left[ 2x \right]-\left[ x \right]$,
  have floor_add_half_eq (x : ℝ) : ⌊x + 1 / 2⌋ = ⌊2 * x⌋ - ⌊x⌋ := by
    let n := ⌊x⌋
    let r := Int.fract x
    have : x = n + r := by
      exact Eq.symm (Int.floor_add_fract x)
    rw [this]
    have : r ≥ 0 := by
      exact Int.fract_nonneg x
    have : r < 1 := by
      exact Int.fract_lt_one x
    have : ⌊n + r + 1 / 2⌋ = n + ⌊r + 1 / 2⌋ := by
      rw [show n + r + 1 / 2 = n + (r + 1 / 2) by ring]
      simp --exact Int.floor_int_add n (r + 1 / 2)
    rw [this]
    have : ⌊2 * (n + r)⌋ - ⌊n + r⌋ = n + ⌊2 * r⌋ - ⌊r⌋ := by
      rw [show 2 * (n + r) = (2 * n : ℤ) + 2 * r by push_cast; ring]
      set _2_n := 2 * n
      simp
      --unfold _2_n
      ring
    rw [this]
    suffices ⌊r + 1 / 2⌋ = ⌊2 * r⌋ - ⌊r⌋ by linarith
    -- This hold for both cases.
    have : ⌊r⌋ = 0 := by
      have : r ∈ Set.Ico 0 1 := by
        simp
        constructor <;>
        linarith
      exact Int.floor_eq_zero_iff.mpr this
    rw [this]
    by_cases r < 1 / 2
    . have : ⌊r + 1 / 2⌋ = 0 := by
        have : r + 1 / 2 ∈ Set.Ico 0 1 := by
          simp
          constructor <;>
          linarith
        exact Int.floor_eq_zero_iff.mpr this
      rw [this]
      have : ⌊2 * r⌋ = 0 := by
        have : 2 * r ∈ Set.Ico 0 1 := by
          simp
          constructor <;>
          linarith
        exact Int.floor_eq_zero_iff.mpr this
      rw [this]
      simp
    . have : r ≥ 1 / 2 := by linarith
      have : ⌊r + 1 / 2⌋ = 1 := by
        refine Int.floor_eq_iff.mpr ?_
        constructor <;>
        linarith
      rw [this]
      have : ⌊2 * r⌋ = 1 := by
        refine Int.floor_eq_iff.mpr ?_
        norm_num
        constructor <;>
        linarith
      rw [this]
      simp
  /-
  we have

  $\sum\limits_{k=0}^{2012}{\left[ \frac{2012+{{2}^{k}}}{{{2}^{k+1}}} \right]}=\sum\limits_{k=0}^{2012}{\left( \left[ \frac{2012}{{{2}^{k}}} \right]-\left[ \frac{2012}{{{2}^{k+1}}} \right] \right)}=2012$．
   -/
  have : (fun k => ⌊((2012 + 2 ^ k) / 2 ^ (k + 1) : ℝ)⌋) =
      (fun k => ⌊(2012 / 2 ^ k : ℝ)⌋ - ⌊(2012 / 2 ^ (k + 1) : ℝ)⌋) := by
    ext k
    have : ((2012 + 2 ^ k) / 2 ^ (k + 1) : ℝ) = (2012 / 2 ^ (k + 1) + 1 / 2 : ℝ) := by
      field_simp
      ring
    rw [this]
    rw [floor_add_half_eq]
    congr 2
    ring
  rw [this]
  have : ∑ k ∈ Finset.Icc 0 2012, (⌊(2012 / 2 ^ k : ℝ)⌋ - ⌊(2012 / 2 ^ (k + 1) : ℝ)⌋) =
      ∑ k ∈ Finset.Icc 0 2012, ⌊(2012 / 2 ^ k : ℝ)⌋ - ∑ k ∈ Finset.Icc 0 2012, ⌊(2012 / 2 ^ (k + 1) : ℝ)⌋ := by
    exact Finset.sum_sub_distrib
  rw [this]
  --set n := 2012
  generalize _2012_eq_n : 2012 = n
  rw [show (2012 : ℝ) = n by norm_cast]
  rw [show (2012 : ℤ) = n by norm_cast]
  have : ∑ k ∈ Finset.Icc 0 n, ⌊(n / 2 ^ (k + 1) : ℝ)⌋ = ∑ k ∈ Finset.Icc 1 (n + 1), ⌊(n / 2 ^ k : ℝ)⌋ := by
    apply Finset.sum_nbij' (. + 1) (. - 1)
    . simp
    . simp
    . simp
    . intros k k_in
      simp at k_in
      omega
    . simp
  rw [this]
  set f := fun (k : ℕ) => ⌊(n / 2 ^ k : ℝ)⌋
  have : (Finset.Icc 0 n).sum f - (Finset.Icc 1 (n + 1)).sum f = f 0 - f (n + 1) := by
    set s := Finset.Icc 0 n
    set t := Finset.Icc 1 (n + 1)
    have : s.sum f - t.sum f = (s \ t).sum f - (t \ s).sum f := by
      exact Eq.symm Finset.sum_sdiff_sub_sum_sdiff
    rw [this]
    --norm_num [s, t]
    have : s \ t = {0} := by
      unfold s t
      ext k
      simp
      omega
    rw [this]
    have : t \ s = {n + 1} := by
      unfold s t
      ext k
      simp
      omega
    rw [this]
    simp [f]
  rw [this]
  simp [f, ←_2012_eq_n]
  constructor <;>
  . norm_num
