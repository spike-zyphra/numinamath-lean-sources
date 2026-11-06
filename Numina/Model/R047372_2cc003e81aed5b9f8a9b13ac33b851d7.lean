import Mathlib

open Complex 

theorem algebra_21215 (a : ℂ) (f : ℂ → ℂ) (hf : f = fun z => z^4 + a*z^3 + 5*z^2 - I*z - 6) (h : f (2*I) = 0) :
  {c : ℂ | c ≠ 2 * I ∧ f c = 0} = {1, -1, -3 * I}:= by
  have ha : a = I := by
    simp [hf] at h
    norm_num [pow_two, pow_succ, Complex.ext_iff, mul_add, mul_assoc, Complex.I_re, Complex.I_im] at h ⊢
    constructor
    · -- Real part must be zero
      nlinarith
    · -- Imaginary part must be 1
      nlinarith
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First implication: if c is a root different from 2i, then c in {1, -1, -3i}
    intro h1
    rcases h1 with ⟨hc1, hc2⟩
    have h2 : c^4 + a*c^3 + 5*c^2 - I*c - 6 = 0 := by
      simp [hf] at hc2 ⊢
      simpa using hc2
    rw [ha] at h2
    have eq1 : c^4 + I*c^3 + 5*c^2 - I*c - 6 = (c - 1)*(c + 1)*(c + 3*I)*(c - 2*I) := by
      ring_nf
      simp [Complex.ext_iff, pow_two, pow_succ, Complex.add_re, Complex.add_im, 
            Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring_nf
      <;> norm_num [Complex.I_mul_I]
    rw [eq1] at h2
    cases' (mul_eq_zero.mp h2) with h3 h4
    · cases' (mul_eq_zero.mp h3) with h5 h6
      · cases' (mul_eq_zero.mp h5) with h7 h8
        · -- c - 1 = 0, so c = 1
          have : c = 1 := by
            calc
              c = (c - 1) + 1 := by ring
              _ = (0) + 1 := by rw [h7]
              _ = 1 := by ring
          simp [this]
        · -- c + 1 = 0, so c = -1
          have : c = -1 := by
            calc
              c = (c + 1) - 1 := by ring
              _ = (0) - 1 := by rw [h8]
              _ = -1 := by ring
          simp [this]
      · -- c + 3I = 0, so c = -3I
        have : c = -3 * I := by
          have h8 : c + 3 * I = 0 := by
            simpa using h6
          calc
            c = (c + 3 * I) - 3 * I := by ring
            _ = (0) - 3 * I := by rw [h8]
            _ = -3 * I := by ring
        simp [this]
    · -- c - 2I = 0, contradiction with c ≠ 2I
      exfalso
      apply hc1
      have h9 : c = 2 * I := by
        have h10 : c - 2 * I = 0 := by
          simpa using h4
        calc
          c = (c - 2 * I) + 2 * I := by ring
          _ = (0) + 2 * I := by rw [h10]
          _ = 2 * I := by ring
      simpa using h9
  · -- Second implication: if c in {1, -1, -3i}, then c is a root different from 2i
    rintro (rfl | rfl | rfl)
    · constructor
      · -- Show 1 ≠ 2I
        norm_num [Complex.ext_iff]
      · -- Show f 1 = 0
        simp [hf, ha]
        norm_num [pow_two, pow_succ, Complex.ext_iff, mul_add, mul_assoc, Complex.I_re, Complex.I_im]
    · constructor
      · -- Show -1 ≠ 2I
        norm_num [Complex.ext_iff]
      · -- Show f (-1) = 0
        simp [hf, ha]
        norm_num [pow_two, pow_succ, Complex.ext_iff, mul_add, mul_assoc, Complex.I_re, Complex.I_im]
    · constructor
      · -- Show -3I ≠ 2I
        norm_num [Complex.ext_iff]
      · -- Show f (-3I) = 0
        simp [hf, ha]
        norm_num [pow_two, pow_succ, Complex.ext_iff, mul_add, mul_assoc, Complex.I_re, Complex.I_im]