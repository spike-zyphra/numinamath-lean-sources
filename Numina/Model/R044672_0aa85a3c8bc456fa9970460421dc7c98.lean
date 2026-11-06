import Mathlib

theorem algebra_608626 : {k :ℂ | ∃ a b c d : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧
  a * k^3 + b * k^2 + c * k + d = 0 ∧ b * k^3 + c * k^2 + d * k + a = 0} = {1, -1, -Complex.I, Complex.I} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Forward direction: from the existence of a,b,c,d prove k is in {1, -1, -i, i}
    rintro ⟨a, b, c, d, ha, hb, hc, hd, h1, h2⟩
    have eq1 : a * k^3 + b * k^2 + c * k + d = 0 := h1
    have eq2 : b * k^3 + c * k^2 + d * k + a = 0 := h2
    have eq3 : a * k^4 + b * k^3 + c * k^2 + d * k = 0 := by
      calc
        a * k^4 + b * k^3 + c * k^2 + d * k = (a * k^3 + b * k^2 + c * k + d) * k := by ring
        _ = 0 * k := by rw [eq1]
        _ = 0 := by simp
    have eq4 : a * (k^4 - 1) = 0 := by
      calc 
        a * (k^4 - 1) = (a * k^4 + b * k^3 + c * k^2 + d * k) - (b * k^3 + c * k^2 + d * k + a) := by ring
        _ = 0 - (b * k^3 + c * k^2 + d * k + a) := by rw [eq3]
        _ = - (b * k^3 + c * k^2 + d * k + a) := by ring
        _ = - 0 := by rw [eq2]
        _ = 0 := by simp
    have eq5 : k^4 - 1 = 0 := by
      apply (mul_right_inj' ha).mp
      simpa using eq4
    have eq6 : k^4 = 1 := by
      calc
        k^4 = k^4 - 1 + 1 := by ring
        _ = 0 + 1 := by rw [eq5]
        _ = 1 := by ring
    have h3 : (k - 1) * (k + 1) * (k - Complex.I) * (k + Complex.I) = 0 := by
      have h4 : k^4 - 1 =0 := eq5
      have h5 : k^4 - 1 = (k - 1) * (k + 1) * (k - Complex.I) * (k + Complex.I) := by
        ring_nf
        simp [Complex.I_mul_I]
        ring
      rw [h5] at h4
      simpa using h4
    cases' (mul_eq_zero.mp h3) with h4 h5
    cases' (mul_eq_zero.mp h4) with h6 h7
    cases' (mul_eq_zero.mp h6) with h8 h9
    · -- k - 1 = 0, so k = 1
      left
      exact eq_of_sub_eq_zero h8
    · -- k + 1 = 0, so k = -1
      right
      left
      have : k = -1 := by
        calc
          k = (k + 1) - 1 := by ring
          _ = 0 - 1 := by rw [h9]
          _ = -1 := by ring
      exact_mod_cast this
    · -- k - Complex.I = 0, so k = Complex.I
      right
      right
      right
      have : k = Complex.I := by
        calc
          k = (k - Complex.I) + Complex.I := by ring
          _ = 0 + Complex.I := by rw [h7]
          _ = Complex.I := by ring
      exact_mod_cast this
    · -- k + Complex.I = 0, so k = -Complex.I
      right
      right
      left
      have : k = -Complex.I := by
        calc
          k = (k + Complex.I) - Complex.I := by ring
          _ = 0 - Complex.I := by rw [h5]
          _ = -Complex.I := by ring
      exact_mod_cast this
  · -- Backward direction: from k=1,-1,i,-i prove existence of coefficients
    rintro (rfl | rfl | rfl | rfl)
    · -- k=1
      use 1, 1, 1, -3
      norm_num [pow_two, pow_succ, Complex.ext_iff]
    · -- k=-1
      use 1, 1, 1, 1
      norm_num [pow_two, pow_succ, Complex.ext_iff]
    · -- k=Complex.I
      use 1, 1, 1, 1
      simp [pow_two, pow_succ, Complex.ext_iff, Complex.I_mul_I]
      all_goals norm_num
    · -- k=-Complex.I
      use 1, 1, 1, 1
      simp [pow_two, pow_succ, Complex.ext_iff, Complex.I_mul_I]
      all_goals norm_num