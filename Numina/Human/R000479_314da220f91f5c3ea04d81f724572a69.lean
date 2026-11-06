import Mathlib

open Real


/- For some positive integers $a$ and $b$, the product $\log_a(a+1) \cdot \log_{a+1} (a+2) \dotsm \log_{b-2} (b-1)  \cdot\log_{b-1} b$ contains exactly $870$ terms, and its value is $2.$ Compute $a+b.$ -/
theorem algebra_11133 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a < b) (ha' : 1 < a)
    (hsz : (Finset.Ico a b).card = 870)
    (h : ∏ i ∈ Finset.Ico a b, logb i (i + 1) = 2) :
    a + b = 930 := by

  -- auxiliary lemma of production
  have l_1 (f : ℕ → ℝ) (a b : ℕ) (h : a < b) (hfp : ∀ i ∈ Finset.Ico a b, f i > 0) :
      ∏ i ∈ Finset.Ico a b, f (i + 1) / f i = f b / f a := by
    have : ∀ d ≤ b - a, ∏ i ∈ Finset.Ico a (a + d), f (i + 1) / f i = f (a + d) / f a := by
      intro d
      induction d with
      | zero =>
        simp
        rw [div_self]
        apply ne_of_gt
        exact hfp a (by exact Finset.left_mem_Ico.mpr h)
      | succ d ih =>
        intro hd
        rw [← add_assoc, Finset.prod_Ico_succ_top, ih (by linarith)]
        rw [← mul_div_assoc, div_eq_mul_inv, mul_comm, ← mul_assoc, ← mul_div_assoc, inv_mul_cancel₀]
        . field_simp
        . apply ne_of_gt
          convert hfp (a + d) ?_
          simp only [Finset.mem_Ico, le_add_iff_nonneg_right, zero_le, true_and]
          have : d + 1 + a ≤ b - a + a := by linarith
          rw [Nat.sub_add_cancel (by linarith)] at this
          linarith
        linarith
    convert this (b - a) ?_
    any_goals rw [Nat.add_sub_cancel' (Nat.le_of_succ_le h)]
    linarith


  -- By the change-of-base formula, the expression is equivalent to $\frac{\log (a+1)}{\log a} \cdot \frac{\log (a+2)}{\log (a+1)} \dotsm \frac{\log (b-1)}{\log (b-2)} \cdot \frac{\log b}{\log (b-1)}.$Almost all the terms cancel, leaving just $\frac{\log b}{\log a},$ which equals $\log_a b$ by the change-of-base formula again. Therefore, $\log_a b = 2,$ so $b = a^2.$
  have r1 : b = a ^ 2 := by
    have : ∏ i ∈ Finset.Ico a b, logb i (i + 1) = log b / log a := by
      dsimp [logb]
      convert l_1 (fun x => log x) a b (by linarith) ?_
      . norm_cast
      . intro x hx
        simp only [Finset.mem_Ico] at hx
        obtain ⟨hx1, hx2⟩ := hx
        simp only [gt_iff_lt]
        refine (log_pos_iff ?_.hx).mpr ?_
        all_goals norm_cast; linarith
    rw [h] at this
    apply_fun fun x => x * log a at this
    rw [div_mul_cancel₀, mul_log_eq_log_iff] at this
    norm_cast at this
    any_goals norm_cast
    . exact this.symm
    . by_contra! h_contra
      apply log_eq_zero.mp at h_contra
      norm_cast at h_contra
      simp only [or_false] at h_contra
      rcases h_contra
      all_goals linarith

  -- We are given that the expression contains $870$ logarithms, so $(b-1) - a + 1 = 870,$ or $b-a=870.$
  have r2 : b - a = 870 := by convert hsz; simp only [Nat.card_Ico]


  -- Substituting $b=a^2$ gives $a^2-a=870,$ or $a^2-a-870=0,$ which factors as $(a-30)(a+29)=0.$
  apply_fun fun x => a + x at r2
  rw [Nat.add_sub_cancel' (by linarith)] at r2
  rw [r1] at r2
  zify at r2
  have : ((a : ℤ) - 30) * (a + 29) = 0 := by ring_nf; linarith

  -- Since $a$ must be positive, we have $a=30,$ and $a=30,$ and so $b=a^2=900.$
  have : (a : ℤ) = 30 ∨ (a : ℤ) = -29 := by
    rcases mul_eq_zero.mp this
    . left; linarith
    . right; linarith
  norm_cast at this
  rw [or_false] at this
  simp only [this, Nat.reducePow] at r1

  -- Thus, $a+b=30+900=\boxed{930}.$
  linarith
