import Mathlib

/-Let $i=\sqrt{-1}$. Then the product of the real parts of the roots of $z^{2}-z=5-5 i$ is
(A) -25 .
(B) -6 .
(C) -5 .
(D) $\frac{1}{4}$.
(E) 25 .-/
theorem algebra_240752 (z1 z2 : ℂ) (hz1 : z1^2 - z1 = 5 - 5 * Complex.I) (hz2 : z2^2 - z2 = 5 - 5 * Complex.I)
    (hz12 : z1 ≠ z2) :
    (z1.re * z2.re) = -6 := by 
  have h1 : z1^2 - z1 - (5 - 5 * Complex.I) = 0 := by 
    rw [hz1]
    ring
  have h2 : z2^2 - z2 - (5 - 5 * Complex.I) = 0 := by 
    rw [hz2]
    ring
  have h3 : (z1 - z2) * (z1 + z2 - 1) = 0 := by 
    have eq1 : z1^2 - z1 - (5 - 5 * Complex.I) - (z2^2 - z2 - (5 - 5 * Complex.I)) = 0 := by 
      rw [h1, h2]
      ring
    have eq2 : z1^2 - z1 - (5 - 5 * Complex.I) - (z2^2 - z2 - (5 - 5 * Complex.I)) = 
      (z1 - z2) * (z1 + z2 - 1) := by ring
    rw [eq2] at eq1
    exact eq1
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- z1 - z2 = 0, which contradicts z1 ≠ z2
    exfalso
    exact hz12 (eq_of_sub_eq_zero h4)
  · -- z1 + z2 - 1 = 0, so z1 + z2 = 1
    have hsum : z1 + z2 = 1 := by 
      have h : z1 + z2 - 1 = 0 := by assumption
      exact eq_of_sub_eq_zero h
    have hz1_eq : z1 = 3 - Complex.I ∨ z1 = -2 + Complex.I := by
      have h : z1^2 - z1 - (5 - 5 * Complex.I) = 0 := by assumption
      have h_eq : (z1 - (3 - Complex.I)) * (z1 - (-2 + Complex.I)) = 0 := by
        have h1 : z1^2 - z1 - (5 - 5 * Complex.I) = 0 := by assumption
        ring_nf at h1 ⊢
        simp [Complex.ext_iff, pow_two] at h1 ⊢
        constructor
        · linarith
        · linarith
      cases mul_eq_zero.1 h_eq with
      | inl h1 => 
        left
        exact eq_of_sub_eq_zero h1
      | inr h2 =>
        right
        exact eq_of_sub_eq_zero h2
    have hz2_eq : z2 = 3 - Complex.I ∨ z2 = -2 + Complex.I := by
      have h : z2^2 - z2 - (5 - 5 * Complex.I) = 0 := by assumption
      have h_eq : (z2 - (3 - Complex.I)) * (z2 - (-2 + Complex.I)) = 0 := by
        have h1 : z2^2 - z2 - (5 - 5 * Complex.I) = 0 := by assumption
        ring_nf at h1 ⊢
        simp [Complex.ext_iff, pow_two] at h1 ⊢
        constructor
        · linarith
        · linarith
      cases mul_eq_zero.1 h_eq with
      | inl h1 => 
        left
        exact eq_of_sub_eq_zero h1
      | inr h2 =>
        right
        exact eq_of_sub_eq_zero h2
    rcases hz1_eq with hz1_eq | hz1_eq
    · -- z1 = 3 - i 
      rcases hz2_eq with hz2_eq | hz2_eq
      · -- z2 = 3 - i, which contradicts z1 ≠ z2
        exfalso
        exact hz12 (by rw [hz1_eq, hz2_eq])
      · -- z2 = -2 + i 
        rw [hz1_eq, hz2_eq]
        norm_num
    · -- z1 = -2 + i 
      rcases hz2_eq with hz2_eq | hz2_eq
      · -- z2 = 3 - i 
        rw [hz1_eq, hz2_eq]
        norm_num
      · -- z2 = -2 + i, which contradicts z1 ≠ z2
        exfalso
        exact hz12 (by rw [hz1_eq, hz2_eq])