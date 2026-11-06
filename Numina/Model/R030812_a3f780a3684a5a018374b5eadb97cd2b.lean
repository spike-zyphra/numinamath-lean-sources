import Mathlib


theorem algebra_11723 : {x : ℂ | (x - 3) ^ 4 + (x - 5) ^ 4 = -8} =
    {4 + .I, 4 - .I, 4 + .I * (√5 : ℂ), 4 - .I * (√5 : ℂ)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- First, prove that if $(x - 3)^4 + (x - 5)^4 = -8$, then $x \in \{4 \pm i, 4 \pm i\sqrt{5}\}$.
    intro h
    have h1 : (x - 3) ^ 4 + (x - 5) ^ 4 = -8 := h
    have eq1 : (x - 3) = (x - 4) + 1 := by ring_nf
    have eq2 : (x - 5) = (x - 4) - 1 := by ring_nf
    rw [eq1, eq2] at h1
    have eq3 : ((x - 4) + 1) ^ 4 + ((x - 4) - 1) ^ 4 + 8 = 0 := by
      calc
        ((x - 4) + 1) ^ 4 + ((x - 4) - 1) ^ 4 + 8 = (-8) + 8 := by rw [← h1]
        _ = 0 := by ring_nf
    have eq4 : ((x - 4) ^ 2 + 1) * ((x - 4) ^ 2 + 5) = 0 := by
      have eq5 : ((x - 4) + 1) ^ 4 + ((x - 4) - 1) ^ 4 + 8 = 0 := eq3
      ring_nf at eq5 ⊢
      norm_num [pow_two, pow_three, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at eq5 ⊢
      constructor
      · 
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ 5 by norm_num)]
      · 
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ 5 by norm_num)]
    cases' (mul_eq_zero.mp eq4) with h2 h3
    · -- First case: (x - 4) ^ 2 + 1 = 0
      have eq5 : (x - 4) ^ 2 + 1 = 0 := h2
      have eq6 : (x - 4) = Complex.I ∨ (x - 4) = -Complex.I := by
        have h1 : (x - 4) ^ 2 + 1 = 0 := eq5
        have h2 : (x - 4) ^ 2 = -1 := by
          calc
            (x - 4) ^ 2 = (x - 4) ^ 2 + 1 - 1 := by ring
            _ = -1 := by rw [h1]; ring
        have h3 : (x - 4) ^ 2 + 1 = 0 := h1
        have h4 : (x - 4) = Complex.I ∨ (x - 4) = -Complex.I := by
          have h5 : (x - 4) ^ 2 + 1 = 0 := h1
          have h6 : (x - 4) ^ 2 + 1 = (x - 4 - Complex.I) * (x - 4 + Complex.I) := by
            ring_nf
            simp [Complex.I_mul_I]
            ring
          rw [h6] at h5
          cases (mul_eq_zero.mp h5) with
          | inl h7 =>
            left
            calc
              x - 4 = (x - 4 - Complex.I) + Complex.I := by ring
              _ = Complex.I := by
                rw [h7]
                ring
          | inr h8 =>
            right
            calc
              x - 4 = (x - 4 + Complex.I) - Complex.I := by ring
              _ = -Complex.I := by
                rw [h8]
                ring
        assumption
      cases eq6 with
      | inl h7 =>
        have hx : x = 4 + Complex.I := by
          calc
            x = (x - 4) + 4 := by ring
            _ = Complex.I + 4 := by rw [h7]
            _ = 4 + Complex.I := by ring
        simp [hx]
      | inr h8 =>
        have hx : x = 4 - Complex.I := by
          calc
            x = (x - 4) + 4 := by ring
            _ = -Complex.I + 4 := by rw [h8]
            _ = 4 - Complex.I := by ring
        simp [hx]
    · -- Second case: (x - 4) ^ 2 + 5 = 0
      have eq7 : (x - 4) ^ 2 + 5 = 0 := h3
      have eq9 : (x - 4) = Complex.I * (√5 : ℂ) ∨ (x - 4) = -Complex.I * (√5 : ℂ) := by
        have h4 : (x - 4) ^ 2 + 5 = 0 := eq7
        have h5 : (x - 4) ^ 2 + 5 = (x - 4 - Complex.I * (√5 : ℂ)) * (x - 4 + Complex.I * (√5 : ℂ)) := by
          ring_nf
          simp [Complex.ext_iff, pow_two, mul_add, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Real.sqrt_mul_self]
          ring
        rw [h5] at h4
        cases (mul_eq_zero.mp h4) with
        | inl h6 =>
          left
          calc
            x - 4 = (x - 4 - Complex.I * (√5 : ℂ)) + Complex.I * (√5 : ℂ) := by ring
            _ = Complex.I * (√5 : ℂ) := by
              rw [h6]
              ring
        | inr h7 =>
          right
          calc
            x - 4 = (x - 4 + Complex.I * (√5 : ℂ)) - Complex.I * (√5 : ℂ) := by ring
            _ = -Complex.I * (√5 : ℂ) := by
              rw [h7]
              ring
      cases eq9 with
      | inl h10 =>
        have hx : x = 4 + Complex.I * (√5 : ℂ) := by
          calc
            x = (x - 4) + 4 := by ring
            _ = Complex.I * (√5 : ℂ) + 4 := by rw [h10]
            _ = 4 + Complex.I * (√5 : ℂ) := by ring
        simp [hx]
      | inr h11 =>
        have hx : x = 4 - Complex.I * (√5 : ℂ) := by
          calc
            x = (x - 4) + 4 := by ring
            _ = -Complex.I * (√5 : ℂ) + 4 := by rw [h11]
            _ = 4 - Complex.I * (√5 : ℂ) := by ring
        simp [hx]
  · -- Now prove the reverse: each root satisfies the equation.
    rintro (h | h | h | h)
    · -- First case: x = 4 + i
      rw [h]
      norm_num [pow_two, pow_three, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    · -- Second case: x = 4 - i
      rw [h]
      norm_num [pow_two, pow_three, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    · -- Third case: x = 4 + i*sqrt(5)
      rw [h]
      simp [pow_two, pow_three, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, add_mul, pow_two]
      ring_nf
      norm_num [pow_two, mul_add, mul_assoc, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Real.sqrt_mul_self]
    · -- Fourth case: x = 4 - i*sqrt(5)
      rw [h]
      simp [pow_two, pow_three, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, add_mul, pow_two]
      ring_nf
      norm_num [pow_two, mul_add, mul_assoc, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Real.sqrt_mul_self]