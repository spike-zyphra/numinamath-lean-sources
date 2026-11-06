import Mathlib

/- Is there an integer $n$ such that $\sqrt{n-1}+\sqrt{n+1}$ is a rational number?-/
theorem number_theory_63481 (n : ℕ) (hn : n ≥ 1) : Irrational (Real.sqrt (n - 1) + Real.sqrt (n + 1)) := by



  -- Assume on the contrary that √(n - 1) + √(n + 1) is rational.
  by_contra!
  -- We first establish n is not 1
  have h_n_ne_1 : n ≠ 1 := by    
    contrapose! this
    subst this
    norm_num
    exact irrational_sqrt_two
  simp [Irrational] at this
  -- If this is rational, then so as √(n² - 1), by squaring both sides.
  obtain ⟨r, hr⟩ := this
  replace hr := congr_arg (· ^ 2) hr
  simp [add_sq] at hr
  iterate 2 rw [Real.sq_sqrt (by norm_cast; omega)] at hr
  rw [mul_assoc, <-Real.sqrt_mul (by norm_cast; omega)] at hr
  rw [mul_comm (n - 1 : ℝ), <-sq_sub_sq] at hr
  simp at hr
  have h' : ¬Irrational (Real.sqrt (n ^ 2 - 1 : ℤ)) := by
    simp [Irrational]
    use (r ^ 2 - 2 * n) / 2
    push_cast at hr ⊢
    linarith only [hr]
  have : (n ^ 2 - 1 : ℤ) = (n ^ 2 - 1 : ℕ) := by
    norm_cast
    rw [Int.subNatNat_eq_coe, Int.ofNat_sub]
    nlinarith
  -- But this would imply that n² - 1 is a perfect square.
  rw [this] at h'
  simp [irrational_sqrt_natCast_iff, IsSquare] at h'
  -- Now r'² = n² - 1.
  obtain ⟨r', hr'⟩ := h'
  rw [<-pow_two] at hr'
  -- Show that r' < n.
  have hnr : r' ^ 2 < n ^ 2 := by
    linarith
  rw [Nat.pow_lt_pow_iff_left (by norm_num)] at hnr
  -- Show that r' ≤ n - 1.
  replace hnr : r' ≤ n - 1 := by omega
  -- Now r'² ≤ (n - 1)².
  rw [<-Nat.pow_le_pow_iff_left (show 2 ≠ 0 by norm_num), <-hr'] at hnr
  zify at hnr
  rw [Int.ofNat_sub (by nlinarith), Int.ofNat_sub (by omega)] at hnr
  push_cast at hnr
  have : n = 1 := by nlinarith
  exact h_n_ne_1 this

  