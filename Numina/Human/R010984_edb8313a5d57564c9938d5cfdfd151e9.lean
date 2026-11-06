import Mathlib

-- we write the verification of the root as a lemma
lemma lemma_1: (5 + √(21 + √7)) ^ 4 - 20 * (5 + √(21 + √7)) ^ 3 +
  108 * (5 + √(21 + √7)) ^ 2 - 80 * (5 + √(21 + √7)) + 9 = 0 := by
      
      ring_nf
      have o1: √(21 + √7) ^ 2 = 21 + √7 := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        have o: 0 ≤ √7 := by
          apply Real.sqrt_nonneg
        nlinarith
        apply Real.sqrt_nonneg
      rw [show √(21 + √7) ^ 4 = (√(21 + √7) ^ 2) ^ 2 by ring]
      simp [o1]
      clear o1
      ring_nf
      have o2: √7 ^ 2 = 7 := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        norm_num
        apply Real.sqrt_nonneg
      simp [o2] 

/-There is a unique quadruple of positive integers
(a,b,c,k) such that c is not a perfect square and
a + √(b + √c) is a root of the polynomial
x ^ 4 - 20 x ^ 3 + 108 x ^ 2 -kx + 9. Compute c.-/

theorem algebra_610663 (a b c k: ℤ)
(h: ∀ a' b' c' k': ℤ, 0 < a' ∧ 0 < b' ∧ 0 < c' ∧ 0 < k' ∧ ¬ IsSquare c' ∧
  (a' + √(b' + √c')) ^ 4 - 20 * (a' + √(b' + √c')) ^ 3 + 108 * (a' + √(b' + √c')) ^ 2 - k' * (a' + √(b' + √c')) + 9 = 0 →
  a = a' ∧ b = b' ∧ c = c' ∧ k = k') : c = 7 := by

  set a':= (5: ℤ)
  set b':= (21: ℤ)
  set c':= (7: ℤ)
  set k':= (80: ℤ)
  have u: a = a' ∧ b = b' ∧ c = c' ∧ k = k':= by
    specialize h a' b' c' k'
    apply h
    simp [a', b', c', k']
    clear *-
    constructor
    .
      native_decide
    .
      exact lemma_1

  simp [u]

