import Mathlib

/- There is a positive real number x not equal to either 1/20 or 1/2 such that
log_(20x)(22x) = log_(2x)(202x)
The value log_(20x)(22x) can be written as log_10(m/n) where m and n are relatively prime positive integers. Find m+n
-/
theorem algebra_98634 (x : ℝ) (m n : ℕ) (hx : x > 0) (hne : x ≠ 1 / 20 ∧ x ≠ 1 / 2)
(h : Real.logb (20 * x) (22 * x) = Real.logb (2 * x) (202 * x))
(hm: m > 0) (hn: n > 0) (hmn: m.Coprime n) (hmnx: Real.logb (20 * x) (22 * x) = Real.logb 10 ((m:ℝ) / n))
: m + n = 112 := by
  obtain ⟨hne₁, hne₂⟩ := hne
  -- define a to be log_(20x)(22x), from that deduce (20x)^a = 22x and (2x)^a = 202x
  set a := Real.logb (20 * x) (22 * x) with h'
  have ha₁ : (20 * x) ^ a = 22 * x := by
    refine (Real.logb_eq_iff_rpow_eq ?_ ?_ ?_).mp h'
    any_goals linarith
    intro hne₂'
    have : x = (1:ℝ) / 20 := by linarith
    contradiction
  have ha₂ : (2 * x) ^ a = 202 * x := by
    refine (Real.logb_eq_iff_rpow_eq ?_ ?_ ?_).mp h.symm
    any_goals linarith
    intro hne₁'
    have : x = (1:ℝ) / 2 := by linarith
    contradiction
  -- divide last two facts to get 10^a = 11/101
  have ha₃ : (10:ℝ) ^ a = 11 / 101 := by
    calc
      (10:ℝ)^a = (10:ℝ)^a * (2 * x)^a / (2 * x)^a := by field_simp
      _ = (10 * (2 * x))^a / (2 * x)^a := by
        congr
        refine Eq.symm (Real.mul_rpow ?_ ?_)
        norm_num
        linarith
      _ = (20*x)^a / (2*x)^a := by ring_nf
      _ = (22 * x) / (202 * x) := by rw[ha₁, ha₂]
      _ = 11 / 101 := by
        field_simp
        ring
  -- 10^a = m/n by hypothesis, so m * 101 = n * 11
  have ha₄ : (10:ℝ) ^ a = m / n := by
    refine (Real.logb_eq_iff_rpow_eq ?_ ?_ ?_).mp hmnx.symm
    any_goals norm_num
    apply div_pos
    all_goals norm_cast
  have hmn₁ : m * 101 = n * 11 := by
    rw [ha₃] at ha₄
    field_simp at ha₄
    norm_cast at ha₄
    linarith
  -- due to the fact that m, n are corprime and 101, 11 are coprime, we get m = 11 and n = 101, then result is just plugging in
  have hmn₂ : m = 11 ∧ n = 101 := by
    zify
    apply Rat.div_int_inj
    any_goals norm_cast
    refine (NNRat.divNat_inj ?_ ?_).mpr ?_
    all_goals linarith
  rw [hmn₂.left, hmn₂.right]