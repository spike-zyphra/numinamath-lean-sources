import Mathlib

theorem algebra_7223 {x y : ℝ} (z : ℂ) (hz : z = x + Complex.I * y) :
    z + (3 - Complex.I) / z = 3 ↔ (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = -1) := by
  constructor
  · -- Forward: if z + (3 - i)/z = 3, then (x, y) are in {(2, 1), (1, -1)}
    intro h
    rw [hz] at h
    by_cases hz0 : x + Complex.I * y = 0
    · -- If z = 0, the original equation is invalid, contradiction.
      rw [hz0] at h
      norm_num [Complex.ext_iff, Complex.normSq] at h ⊢
      all_goals norm_num at h ⊢
      all_goals aesop
    · -- If z ≠ 0, multiply both sides by z. Then we get a quadratic equation. After solving simultaneously on real/imaginary equations, we get solutions.
      have hne : (x + Complex.I * y) ≠ 0 := hz0
      have h1 := h
      have eq3 : (x + Complex.I * y) + (3 - Complex.I) / (x + Complex.I * y) = 3 := by
        simpa using h1
      have eq4 : x + Complex.I * y ≠ 0 := hne
      have eq5 : (x + Complex.I * y + (3 - Complex.I) / (x + Complex.I * y) ) * (x + Complex.I * y) = 3 * (x + Complex.I * y) := by 
        rw [eq3]
        all_goals simp [eq4]
      -- Now manipulate to polynomial form.
      have eq6 : (x + Complex.I * y) ^ 2 + (3 - Complex.I) = 3 * (x + Complex.I * y) := by
        have hne : x + Complex.I * y ≠ 0 := eq4
        have eq7 : (x + Complex.I * y + (3 - Complex.I) / (x + Complex.I * y) ) * (x + Complex.I * y) = 3 * (x + Complex.I * y) := eq5
        have : (x + Complex.I * y + (3 - Complex.I) / (x + Complex.I * y) ) * (x + Complex.I * y) = (x + Complex.I * y)^2 + (3 - Complex.I) := by
          field_simp [hne]
          <;> ring_nf <;> field_simp [hne]
          <;> ring_nf
        rw [this] at eq7
        all_goals try tauto
        all_goals try nlinarith
        all_goals try { tauto }
      -- Now, extract real and imaginary parts
      have eq7 := congr_arg Complex.re eq6
      have eq8 := congr_arg Complex.im eq6
      simp [pow_two, Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im, Complex.mul_re, Complex.mul_im] at eq7 eq8 
      have h2 : (x - 2) * (x - 1) = 0 := by
        nlinarith [sq_nonneg (y - 1), sq_nonneg (x - 1), sq_nonneg (y + 1), sq_nonneg (x - 2), sq_nonneg (y * 1), sq_nonneg ((x: ℝ) ^2 + y ^ 2)]
      cases' (mul_eq_zero.mp h2) with h3 h4
      · -- Case x = 2
        have hx : x = 2 := by linarith
        have hy : y = 1 := by
          rw [hx] at eq8
          nlinarith
        left
        exact ⟨hx, hy⟩
      · -- Case x = 1
        have hx : x = 1 := by linarith
        have hy : y = -1 := by
          rw [hx] at eq8
          nlinarith
        right
        exact ⟨hx, hy⟩
  · -- Backward: z =2, 1 or z=1,-1 ⇒ equation
    rintro (h | h)
    · -- When (x = 2, y =1)
      rcases h with ⟨hx, hy⟩
      rw [hz]
      rw [hx, hy]
      field_simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.div_re, Complex.div_im, Complex.normSq, Complex.mul_re, Complex.mul_im]
      norm_num
      all_goals norm_num [Complex.ext_iff]
      <;> all_goals norm_num
    · -- When (x = 1, y = -1)
      rcases h with ⟨hx, hy⟩
      rw [hz]
      rw [hx, hy]
      field_simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.div_re, Complex.div_im, Complex.normSq, Complex.mul_re, Complex.mul_im]
      norm_num
      all_goals norm_num [Complex.ext_iff]
      <;> all_goals norm_num
      <;> try tauto
      all_goals try tauto