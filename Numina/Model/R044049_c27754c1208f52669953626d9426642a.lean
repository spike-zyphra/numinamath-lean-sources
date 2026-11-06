import Mathlib

theorem algebra_98614 : { (r, s) : ℤ × ℤ | r ∈ Set.Ioc 0 100 ∧ s ∈ Set.Ioc 0 100 ∧
    Complex.I * ((√3 + Complex.I) / 2) ^ r = ((-1 + Complex.I * √3) / 2) ^ s }.ncard = 834 := by
  have eqw : Complex.exp (Complex.I * (Real.pi / 6)) = (√3 + Complex.I) / 2 := by
    apply Complex.ext
    . rw [Complex.exp_re]; simp
    . rw [Complex.exp_im]; simp

  have eqz : Complex.exp (Complex.I * (2 * Real.pi / 3)) = (-1 + Complex.I * √3) / 2 := by
    rw [show (2 * Real.pi / 3 : ℂ) = Real.pi - Real.pi / 3 by ring]
    apply Complex.ext
    . rw [Complex.exp_re]; simp; ring
    . rw [Complex.exp_im]; simp

  have eqi : Complex.exp (Complex.I * (Real.pi / 2)) = Complex.I := by
    apply Complex.ext
    . rw [Complex.exp_re]; simp
    . rw [Complex.exp_im]; simp

  have {s r : ℤ} : Complex.I * ((√3 + Complex.I) / 2) ^ r = ((-1 + Complex.I * √3) / 2) ^ s ↔ ∃ k : ℤ, 3 + r = 4 * (s + 3 * k) := by
    rw [← eqw, ← eqz]
    nth_rw 1 [← eqi]
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    rw [Complex.exp_eq_exp_iff_exists_int]
    apply exists_congr
    intro a
    move_mul [Complex.I]
    rw [← add_mul, ← add_mul, mul_left_inj' Complex.I_ne_zero]
    norm_cast
    rw [← mul_left_inj' (show (6 : ℝ) ≠ 0 by norm_num)]
    ring_nf
    move_mul [Real.pi]
    rw [← add_mul, ← add_mul, mul_left_inj' Real.pi_ne_zero]
    norm_cast
    ring_nf
  simp_rw [this]

  have hprop {r t : ℤ} (h : 3 + r = 4 * t) : r ∈ Set.Ioc 0 100 ↔ t ∈ Finset.Ico 1 26 := by
    simp
    have : 0 < r ↔ 1 ≤ t := by
      rw [← mul_le_mul_left (show 0 < (4 : ℤ) by norm_num), ← h, ← Int.add_one_le_iff, ← tsub_le_iff_left]
      simp
    rw [this]
    have : r ≤ 100 ↔ t < 26 := by
      rw [← mul_lt_mul_left (show 0 < (4 : ℤ) by norm_num), ← h, ← Int.lt_add_one_iff, ← lt_tsub_iff_left]
      simp
    rw [this]

  let f : (_ : ℤ) × ℤ → ℤ × ℤ := fun ⟨s, t⟩ => (4 * t - 3, s)
  have f_inj : Function.Injective f := by
    rintro ⟨r1, s1⟩ ⟨r2, s2⟩
    simp [f]
    intro h1 h2
    exact ⟨h2, h1⟩
  have f_image : f '' ↑(Finset.sigma (Finset.Ioc 0 100) (fun s => { t ∈ Finset.Ico 1 26 | t ≡ s [ZMOD 3] })) = { (r, s) : ℤ × ℤ | r ∈ Set.Ioc 0 100 ∧ s ∈ Set.Ioc 0 100 ∧ ∃ k : ℤ, 3 + r = 4 * (s + 3 * k) } := by
    ext ⟨r, s⟩
    simp only [f, Finset.coe_sigma, Finset.coe_filter, Set.mem_image,
      Set.mem_sigma_iff, Set.mem_setOf_eq, Sigma.exists, Prod.mk.injEq]
    constructor
    . rintro ⟨s', t, ⟨hs', ht, hm⟩, hr, hs⟩
      subst hr hs
      apply And.intro
      . exact (hprop (by simp)).mpr ht
      . apply And.intro
        . rw [Finset.coe_Ioc] at hs'
          exact hs'
        . simp
          rw [← Int.modEq_iff_add_fac, Int.modEq_comm]
          exact hm
    . rintro ⟨hr, hs, hk⟩
      obtain ⟨k, hk⟩ := hk
      use s
      use s + 3 * k
      and_intros
      . simp [Finset.coe_Ioc, hs]
      . exact (hprop hk).mp hr
      . exact Int.modEq_add_fac_self
      . simp [← hk]
      . rfl
  rw [← f_image, Set.ncard_image_of_injective _ f_inj, Set.ncard_coe_Finset, Finset.card_sigma]

  have {s} : { t ∈ Finset.Ico 1 26 | t ≡ s [ZMOD 3] }.card = if s ≡ 1 [ZMOD 3] then 9 else 8 := by
    zify
    mod_cases h : s % 3
    all_goals rw [Int.ModEq] at h
    all_goals simp_rw [Int.ModEq, h]
    all_goals simp_rw [← Int.ModEq.eq_1]
    all_goals rw [Int.Ico_filter_modEq_card _ _ (by norm_num)]
    all_goals simp [Int.ModEq]
    all_goals norm_num
  simp_rw [this, Finset.sum_ite, Finset.sum_const]
  have h_1_mod_3 : { s ∈ Finset.Ioc 0 100 | s ≡ 1 [ZMOD 3] }.card = 34 := by
    zify
    rw [Int.Ioc_filter_modEq_card _ _ (by norm_num)]
    norm_num
  have h_not_1_mod_3 : { s ∈ Finset.Ioc 0 100 | ¬(s ≡ 1 [ZMOD 3]) }.card = 66 := by
    rw [← @Nat.add_left_cancel_iff _ _ { s ∈ Finset.Ioc 0 100 | s ≡ 1 [ZMOD 3] }.card]
    rw [Finset.filter_card_add_filter_neg_card_eq_card]
    simp [h_1_mod_3]
  simp only [h_1_mod_3, h_not_1_mod_3]
  all_goals norm_num