import Mathlib

/- Let $N$ be the number of complex numbers $z$ with the properties that $|z|=1$ and $z^{6!}-z^{5!}$ is a real number. Find the remainder when $N$ is divided by $1000$. -/
theorem algebra_97532 :
    {z : ℂ | Complex.abs z = 1 ∧ ∃ r : ℝ, z^(Nat.factorial 6) - z^(Nat.factorial 5) = r}.ncard % 1000 = 440 := by

  simp [Nat.factorial]

  -- First we use that fact that complex numbers with magnitude 1 are equivalent to numbers θ
  -- in (-π, π], and our condition becomes sin(720 * θ) - sin(120 * θ) = 0.
  let f : ℝ → ℂ := fun θ => Complex.exp (Complex.I * θ)
  have hfinj : Set.InjOn f {θ : ℝ | θ ∈ Set.Ioc (-Real.pi) Real.pi ∧ Real.sin (720 * θ) - Real.sin (120 * θ) = 0} := by
    rintro θ1 ⟨⟨hθ11, hθ12⟩, _⟩ θ2 ⟨⟨hθ21, hθ22⟩, _⟩ h
    simp [f] at h
    suffices : Complex.I * θ1 = Complex.I * θ2
    . rw [mul_right_inj' Complex.I_ne_zero] at this
      norm_cast at this
    apply Complex.exp_inj_of_neg_pi_lt_of_le_pi
    any_goals simp <;> linarith
    exact h
  have hfimage : f '' {θ : ℝ | θ ∈ Set.Ioc (-Real.pi) Real.pi ∧ Real.sin (720 * θ) - Real.sin (120 * θ) = 0} = {z : ℂ | Complex.abs z = 1 ∧ ∃ r : ℝ, z^720 - z^120 = r} := by
    ext z
    -- Note that a complex number is real iff its imaginary part is 0.
    have real_iff_im_zero {z : ℂ} : (∃ r : ℝ, z = r) ↔ Complex.im z = 0 := by
      constructor
      . rintro ⟨r, hr⟩
        rw [hr]
        simp
      . intro h
        use Complex.re z
        exact Complex.ext (by simp) h
    simp [f, real_iff_im_zero]
    constructor
    . rintro ⟨θ, ⟨hx1, hx2⟩, hz, hf⟩
      and_intros
      . rw [mul_comm, Complex.abs_exp_ofReal_mul_I]
      . simp [← Complex.exp_nat_mul]
        rw [show 720 * (Complex.I * θ) = (720 * θ : ℝ) * Complex.I by push_cast; ring]
        rw [show 120 * (Complex.I * θ) = (120 * θ : ℝ) * Complex.I by push_cast; ring]
        simp only [Complex.exp_ofReal_mul_I_im]
        exact hx2
    . rintro ⟨hr, hz⟩
      use Complex.arg z
      and_intros
      . exact Complex.neg_pi_lt_arg _
      . exact Complex.arg_le_pi _
      . have {n : ℕ} : (z ^ n).im = Real.sin (n * Complex.arg z) := by
          nth_rw 1 [← Complex.abs_mul_exp_arg_mul_I z]
          simp [hr]
          rw [← Complex.exp_nat_mul]
          rw [show n * (z.arg * Complex.I) = (n * z.arg : ℝ) * Complex.I by push_cast; ring]
          rw [Complex.exp_ofReal_mul_I_im]
        rw [show (720 : ℝ) = Nat.cast 720 by simp]
        rw [show (120 : ℝ) = Nat.cast 120 by simp]
        rw [← this, ← this]
        exact hz
      . nth_rw 2 [← Complex.abs_mul_exp_arg_mul_I z]
        rw [hr, mul_comm]
        simp
  rw [← hfimage, Set.ncard_image_of_injOn hfinj]

  -- Next, we can use the sum-to-product formula to rewrite the sine difference as a product.
  have {θ : ℝ} : Real.sin (720 * θ) - Real.sin (120 * θ) = 0 ↔ Real.sin (300 * θ) = 0 ∨ Real.cos (420 * θ) = 0 := by
    rw [Real.sin_sub_sin]
    ring_nf
    simp
  simp_rw [this]

  -- On (-π, π], we have Real.sin (300 * θ) = 0 iff θ = k * π / 300 for some integer k, -300 < k ≤ 300.
  -- Similarly, Real.cos (420 * θ) = 0 iff θ = (k + 1/2) * π / 420 for some integer k, -420 ≤ k < 419.
  have : {θ | θ ∈ Set.Ioc (-Real.pi) Real.pi ∧ (Real.sin (300 * θ) = 0 ∨ Real.cos (420 * θ) = 0)} =
      {θ | θ ∈ Set.Ioc (-Real.pi) Real.pi ∧ Real.sin (300 * θ) = 0} ∪ {θ | θ ∈ Set.Ioc (-Real.pi) Real.pi ∧ Real.cos (420 * θ) = 0} := by
    ext θ
    simp
    rw [and_or_left]
  rw [this]

  let f1 : ℤ → ℝ := fun k => k * Real.pi / 300
  have hf1 {θ : ℝ} : Real.sin (300 * θ) = 0 ↔ ∃ k, f1 k = θ := by
    rw [Real.sin_eq_zero_iff]
    apply exists_congr
    intro k
    simp [f1]
    nth_rw 2 [mul_comm]
    rw [div_eq_iff (show (300 : ℝ) ≠ 0 by norm_num)]
  have hf1mono : StrictMono f1 := by
    intro k1 k2 h
    simp [f1]
    rw [div_lt_div_iff_of_pos_right (show 0 < (300 : ℝ) by norm_num)]
    rw [mul_lt_mul_iff_of_pos_right Real.pi_pos]
    norm_cast
  have hf1lower {k : ℤ} : -Real.pi < f1 k ↔ -300 < k := by
    rw [show -Real.pi = f1 (-300) by simp [f1]; ring_nf]
    exact StrictMono.lt_iff_lt hf1mono
  have hf1upper {k : ℤ} : f1 k ≤ Real.pi ↔ k ≤ 300 := by
    rw [show Real.pi = f1 300 by simp [f1]]
    exact StrictMono.le_iff_le hf1mono

  let f2 : ℤ → ℝ := fun k => (2 * k + 1) * Real.pi / 840
  have hf2 {θ : ℝ} : Real.cos (420 * θ) = 0 ↔ ∃ k, f2 k = θ := by
    rw [Real.cos_eq_zero_iff]
    apply exists_congr
    intro k
    simp [f2]
    nth_rw 2 [mul_comm]
    rw [eq_div_iff (show (2 : ℝ) ≠ 0 by norm_num)]
    rw [div_eq_iff (show (840 : ℝ) ≠ 0 by norm_num)]
    ring_nf
    rw [eq_comm]
  have hf2mono : StrictMono f2 := by
    intro k1 k2 h
    simp [f2]
    rw [div_lt_div_iff_of_pos_right (show 0 < (840 : ℝ) by norm_num)]
    rw [mul_lt_mul_iff_of_pos_right Real.pi_pos]
    norm_cast
    linarith
  have hf2lower {k : ℤ} : -Real.pi < f2 k ↔ -420 ≤ k := by
    constructor
    . intro h
      rw [← Int.sub_one_lt_iff, ← StrictMono.lt_iff_lt hf2mono]
      refine lt_trans ?_ h
      simp [f2]
      ring_nf
      rw [show -Real.pi = Real.pi * -1 by simp]
      rw [mul_lt_mul_iff_of_pos_left Real.pi_pos]
      norm_num
    . intro h
      rw [← StrictMono.le_iff_le hf2mono] at h
      refine lt_of_lt_of_le ?_ h
      simp [f2]
      ring_nf
      rw [show -Real.pi = Real.pi * -1 by simp]
      rw [mul_lt_mul_iff_of_pos_left Real.pi_pos]
      norm_num
  have hf2upper {k : ℤ} : f2 k ≤ Real.pi ↔ k < 420 := by
    constructor
    . intro h
      rw [← StrictMono.lt_iff_lt hf2mono]
      refine lt_of_le_of_lt h ?_
      simp [f2]
      ring_nf
      nth_rw 1 [show Real.pi = Real.pi * 1 by simp]
      rw [mul_lt_mul_iff_of_pos_left Real.pi_pos]
      norm_num
    . intro h
      rw [← Int.le_sub_one_iff, ← StrictMono.le_iff_le hf2mono] at h
      refine le_trans h ?_
      simp [f2]
      ring_nf
      nth_rw 2 [show Real.pi = Real.pi * 1 by simp]
      rw [mul_le_mul_iff_of_pos_left Real.pi_pos]
      norm_num

  have : {θ | θ ∈ Set.Ioc (-Real.pi) Real.pi ∧ Real.sin (300 * θ) = 0} = f1 '' Set.Ioc (-300) 300 := by
    ext θ
    simp [Set.mem_setOf_eq, Set.mem_image]
    rw [hf1]
    constructor
    . rintro ⟨⟨hθ1, hθ2⟩, ⟨k, hk⟩⟩
      use k
      and_intros
      . rw [← hf1lower, hk]
        exact hθ1
      . rw [← hf1upper, hk]
        exact hθ2
      . exact hk
    . rintro ⟨k, ⟨hk1, hk2⟩, hk⟩
      and_intros
      . rw [← hk, hf1lower]
        exact hk1
      . rw [← hk, hf1upper]
        exact hk2
      . use k
  rw [this]

  have : {θ | θ ∈ Set.Ioc (-Real.pi) Real.pi ∧ Real.cos (420 * θ) = 0} = f2 '' Set.Ico (-420) 420 := by
    ext θ
    simp [Set.mem_setOf_eq, Set.mem_image]
    rw [hf2]
    constructor
    . rintro ⟨⟨hθ1, hθ2⟩, ⟨k, hk⟩⟩
      use k
      and_intros
      . rw [← hf2lower, hk]
        exact hθ1
      . rw [← hf2upper, hk]
        exact hθ2
      . exact hk
    . rintro ⟨k, ⟨hk1, hk2⟩, hk⟩
      and_intros
      . rw [← hk, hf2lower]
        exact hk1
      . rw [← hk, hf2upper]
        exact hk2
      . use k
  rw [this]

  -- Now we can count the number of elements in each set.
  have hcard1 : Set.ncard (f1 '' Set.Ioc (-300) 300) = 600 := by
    rw [Set.ncard_image_of_injective _ (StrictMono.injective hf1mono), ← Finset.coe_Ioc, Set.ncard_coe_Finset]
    simp

  -- Now we can count the number of elements in each set.
  have hcard2 : Set.ncard (f2 '' Set.Ico (-420) 420) = 840 := by
    rw [Set.ncard_image_of_injective _ (StrictMono.injective hf2mono), ← Finset.coe_Ico, Set.ncard_coe_Finset]
    simp

  -- These two sets are disjoint, so we can count them separately.
  have hdisjoint : Disjoint (f1 '' Set.Ioc (-300) 300) (f2 '' Set.Ico (-420) 420) := by
    rw [Set.disjoint_right]
    simp only [Set.mem_image]
    rintro θ ⟨k1, _, hk1⟩ ⟨k2, _, hk2⟩
    have eq1 : k2 * 840 - k1 * 600 = 300 := by
      rw [← hk1] at hk2
      simp [f1, f2] at hk2
      field_simp at hk2
      rw [show k2 * Real.pi * 840 = Real.pi * (k2 * 840) by ring] at hk2
      rw [show (2 * k1 + 1) * Real.pi * 300 = Real.pi * ((2 * k1 + 1) * 300) by ring] at hk2
      rw [mul_right_inj' Real.pi_ne_zero] at hk2
      ring_nf at hk2
      norm_cast at hk2
      rw [hk2]
      ring
    have : 120 ∣ k2 * 840 - k1 * 600 := Int.dvd_sub (Int.dvd_trans (by norm_num) (Int.dvd_mul_left _ _)) (Int.dvd_trans (by norm_num) (Int.dvd_mul_left _ _))
    rw [eq1] at this
    exact (show ¬((120 : ℤ) ∣ (300 : ℤ)) by norm_num) this

  -- Finally we can put this all together to compute the sum.
  rw [Set.ncard_union_eq hdisjoint (Set.finite_of_ncard_ne_zero (by rw [hcard1]; simp)) (Set.finite_of_ncard_ne_zero (by rw [hcard2]; simp))]
  rw [hcard1, hcard2]