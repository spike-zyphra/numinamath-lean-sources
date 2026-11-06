import Mathlib

theorem algebra_123583 : {n : ℝ | ∃ k : ℤ, (n + Complex.I)^4 = k}.ncard = 3 := by
  have h1 : {n : ℝ | ∃ k : ℤ, (n + Complex.I)^4 = k} = {-1, 0, 1} := by
    ext n 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First, show that if n in the left side, it's in the right.
      rintro ⟨k, hk⟩
      have eq1 := congr_arg Complex.re hk
      have eq2 := congr_arg Complex.im hk
      simp [pow_two, pow_succ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
        Complex.I_re, Complex.I_im] at eq1 eq2
      have h2 : (4 * n^3 - 4 * n) = (0 : ℝ) := by 
        norm_num at eq2 ⊢
        have h3 : (k : ℂ).im = (0 : ℝ) := by 
          norm_cast at eq2 ⊢
        linarith
      have h3 : n^3 - n = 0 := by 
        linarith
      have h4 : n * (n^2 - 1) = 0 := by 
        ring_nf at h3 ⊢
        linarith
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- h5: n = 0
        have hn0 : n = (0 : ℝ) := by 
          linarith
        rw [hn0]
        norm_num
      · -- h6: n^2 -1 = 0
        have h7 : n^2 = 1 := by linarith
        -- solving n^2 = 1
        have h8 : n = 1 ∨ n = -1 := by
          have h9 : n^2 - 1 = 0 := by linarith
          have h10 : (n - 1) * (n + 1) = 0 := by
            nlinarith
          cases' (mul_eq_zero.mp h10) with h11 h12
          · -- h11 : n - 1 = 0
            left
            linarith
          · -- h12 : n + 1 = 0
            right
            linarith
        cases' h8 with h1 h2
        · -- h1 : n = 1
          rw [h1]
          norm_num
        · -- h2 : n = -1
          rw [h2]
          norm_num
    · -- Now prove the converse: if n in right side, then in left
      rintro (rfl | rfl | rfl)
      · -- n = -1 
        use (-4)
        simp [pow_succ, pow_zero, Complex.ext_iff, Complex.add_re, Complex.add_im, 
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        all_goals norm_num [Complex.ext_iff]
      · -- n = 0 
        use (1)
        simp [pow_succ, pow_zero, Complex.ext_iff, Complex.add_re, Complex.add_im, 
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      · -- n = 1 
        use (-4)
        simp [pow_succ, pow_zero, Complex.ext_iff, Complex.add_re, Complex.add_im, 
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        all_goals norm_num [Complex.ext_iff]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> norm_num