import Mathlib

theorem algebra_93681 : {n : ℤ | ∃ k : ℤ, (n + Complex.I)^4 = k}.encard = 3 := by
  have h1 : {n : ℤ | ∃ k : ℤ, (n + Complex.I)^4 = k} = {-1, 0, 1} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume ∃ k : ℤ, (n + Complex.I) ^ 4 = k, prove n ∈ {-1, 0, 1}
      rintro ⟨k, hk⟩
      have eq1 := congr_arg Complex.im hk
      simp [pow_two, pow_succ, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re] at eq1
      have eq2 : (n : ℝ) * (n ^ 2 - 1 : ℝ) = 0 := by
        ring_nf at eq1 ⊢
        nlinarith
      have eq3 : (n : ℤ) * ((n : ℤ) ^ 2 - 1) = 0 := by
        exact_mod_cast eq2
      have h2 : n * (n ^ 2 - 1) = 0 := by
        exact_mod_cast eq3
      have h2 : n = 0 ∨ n ^ 2 - 1 = 0 := by
        cases (mul_eq_zero.mp h2) with
        | inl h => 
          left
          linarith
        | inr h => 
          right
          linarith
      cases h2 with
      | inl hn0 => 
        rw [hn0]
        norm_num
      | inr hn1 =>
        have h3 : n ^ 2 = 1 := by
          nlinarith
        have h4 : n = 1 ∨ n = -1 := by
          rw [sq_eq_one_iff] at h3
          tauto
        tauto
    · -- Assume n ∈ {-1, 0, 1}, prove ∃ k : ℤ, (n + Complex.I) ^ 4 = k
      rintro (rfl | rfl | rfl)
      · -- n = -1
        use -4
        simp [pow_two, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        all_goals norm_num
      · -- n = 0
        use 1
        simp [pow_two, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        all_goals norm_num
      · -- n = 1
        use -4
        simp [pow_two, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp