import Mathlib
open Polynomial

theorem algebra_608603 :
    {x : ℂ | x ^ 4 + 2 * x ^ 3 + 2 * x ^ 2 + 2 * x + 1 = 0}
    =  {-1, - Complex.I, Complex.I} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Forward direction: if x^4 + 2x^3 + 2x^2 + 2x + 1 = 0 then x ∈ {-1, -i, i}
    intro h
    have h1 : x ^ 4 + 2 * x ^ 3 + 2 * x ^ 2 + 2 * x + 1 = 0 := h
    have h2 : (x + 1) ^ 2 * (x ^ 2 + 1) = 0 := by 
      ring_nf at h1 ⊢
      <;> norm_num [Complex.ext_iff] at h1 ⊢ 
      <;> constructor <;> nlinarith 
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where (x + 1)^2 = 0
      have h5 : x + 1 = 0 := by
        apply pow_eq_zero 
        exact h3
      have h6 : x = -1 := by 
        calc 
          x = (x + 1) - 1 := by ring_nf
          _ = (-1) := by rw [show x + 1 = 0 by simpa using h5]; ring_nf 
      left 
      exact h6 
    · -- Case where x^2 + 1 = 0 
      have h5 : x ^ 2 + 1 = 0 := h4 
      have h6 : x ^ 2 = -1 := by 
        calc 
          x ^ 2 = x ^ 2 + 1 - 1 := by ring_nf 
          _ = -1 := by rw [h5]; ring_nf 
      have h7 : x = Complex.I ∨ x = -Complex.I := by 
        have h8 : x ^ 2 + 1 = 0 := h5 
        have h9 : x ^ 2 + 1 = (x - Complex.I) * (x + Complex.I) := by 
          ring_nf 
          <;> simp [Complex.I_mul_I] 
          <;> ring_nf 
        have h10 : (x - Complex.I) * (x + Complex.I) = 0 := by 
          rw [←h9] 
          exact h5 
        cases' (mul_eq_zero.mp h10) with h11 h12 
        · -- Case where x - i = 0 
          left 
          exact eq_of_sub_eq_zero h11 
        · -- Case where x + i = 0 
          right 
          have h13 : x = -Complex.I := by 
            calc 
              x = (x + Complex.I) - Complex.I := by ring_nf 
              _ = -Complex.I := by rw [show x + Complex.I = 0 by simpa using h12]; ring_nf 
          exact h13 
      cases h7 with 
      | inl h8 => 
        right 
        right 
        exact h8 
      | inr h8 => 
        right 
        left 
        exact h8 
  · -- Backward direction: if x ∈ {-1, -i, i} then x^4 + 2x^3 + 2x^2 + 2x + 1 = 0 
    rintro (rfl | rfl | rfl)
    · -- Case where x = -1 
      norm_num [pow_two, pow_succ, Complex.ext_iff] 
    · -- Case where x = -i 
      simp [pow_two, pow_succ, Complex.ext_iff, Complex.I_mul_I]
      <;> norm_num 
    · -- Case where x = i 
      simp [pow_two, pow_succ, Complex.ext_iff, Complex.I_mul_I]
      <;> norm_num