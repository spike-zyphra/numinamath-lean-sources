import Mathlib

theorem algebra_156527 (x : ℂ) :
    x^4 + 2 * x^3 + 2 * x^2 + 2 * x + 1 = 0 ↔
    x = -1 ∨ x = Complex.I ∨ x = -Complex.I := by
  have h1 : x^4 + 2 * x^3 + 2 * x^2 + 2 * x + 1 = (x ^ 2 + 1) * (x + 1) ^ 2 := by
    ring_nf
  rw [h1]
  constructor
  · -- Assume (x^2 + 1) * (x + 1) ^ 2 = 0, prove x = -1 ∨ x = Complex.I ∨ x = -Complex.I
    intro h
    cases' (mul_eq_zero.mp h) with h2 h3
    · -- Case where x^2 + 1 = 0
      have h4 : x ^ 2 + 1 = 0 := by
        exact_mod_cast h2
      have h5 : x^2 = -1 := by
        calc
          x ^ 2 = (x ^ 2 + 1) - 1 := by ring_nf
          _ = -1 := by rw [h4]; norm_num
      have h7 : x = Complex.I ∨ x = -Complex.I := by
        have h8 : x^2 + 1 = 0 := h4
        have h11 : (x - Complex.I) * (x + Complex.I) = 0 := by
          calc
            (x - Complex.I) * (x + Complex.I)
              = x^2 + 1 := by
                simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
                <;> ring_nf <;> norm_num
            _ = (0 : ℂ) := by
              rw [show x^2 + 1 = (0 : ℂ) by exact_mod_cast h8]
              all_goals simp
        cases' (mul_eq_zero.mp h11) with h12 h13
        · -- Case x -i =0
          left
          exact eq_of_sub_eq_zero h12
        · -- Case x +i =0
          right
          have h14 : x + Complex.I = 0 := h13
          have h15 : x = -Complex.I := by
            calc
              x = x + Complex.I - Complex.I := by ring_nf
              _ = -Complex.I := by rw [h14]; ring_nf
          exact h15
      cases h7 with
      | inl h8 =>
        right
        left
        exact h8
      | inr h9 =>
        right
        right
        exact h9
    · -- Case where (x + 1) ^ 2 = 0
      have h4 : x + 1 = 0 := by
        apply pow_eq_zero 
        exact h3
      left
      have h5 : x = -1 := by
        have h6 : x + 1 = 0 := h4
        calc
          x = x + 1 - 1 := by ring_nf
          _ = (-1 : ℂ) := by rw [h6]; norm_num
      exact h5
  · -- Assume x = -1 ∨ x = Complex.I ∨ x = -Complex.I, prove (x ^ 2 + 1) * (x + 1) ^ 2 = 0
    rintro (h | h | h)
    · -- Case x = -1
      rw [h]
      norm_num [pow_two, pow_succ, Complex.ext_iff]
    · -- Case x = Complex.I
      rw [h]
      norm_num [pow_two, pow_succ, Complex.ext_iff, Complex.I_sq]
    · -- Case x = -Complex.I
      rw [h]
      norm_num [pow_two, pow_succ, Complex.ext_iff, Complex.I_sq]