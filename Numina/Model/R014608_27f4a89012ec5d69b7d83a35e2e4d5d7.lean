import Mathlib

theorem algebra_170197 (a : ℝ) (A B : Set ℝ)
    (hA : A = {2, 4, a^3 - 2*a^2 - a + 7})
    (hB : B = {-4, a + 3, a^2 - 2*a + 2, a^3 + a^2 + 3*a + 7})
    (hAB : A ∩ B = {2, 5}) :
    a = 2 := by
  have h1 : 2 ∈ A ∩ B := by
    rw [hAB]
    simp
  have h2 : 5 ∈ A ∩ B := by
    rw [hAB]
    simp
  have h1A : 2 ∈ A := by
    have h1' : 2 ∈ A ∩ B := h1
    simp at h1' ⊢
    tauto
  have h1B : 2 ∈ B := by
    have h1' : 2 ∈ A ∩ B := h1
    simp at h1' ⊢
    tauto
  have h2A : 5 ∈ A := by
    have h2' : 5 ∈ A ∩ B := h2
    simp at h2' ⊢
    tauto
  have h2B : 5 ∈ B := by
    have h2' : 5 ∈ A ∩ B := h2
    simp at h2' ⊢
    tauto
  rw [hA] at h2A
  simp at h2A
  have eq1 : a^3 - 2*a^2 - a + 2 = 0 := by
    nlinarith
  have h_eq2 : (a - 1) * (a - 2) * (a + 1) = 0 := by
    ring_nf at eq1 ⊢
    linarith
  cases' (mul_eq_zero.mp h_eq2) with h3 h4
  · cases' (mul_eq_zero.mp h3) with h5 h6
    · -- a - 1 = 0, so a = 1. Contradiction with h2B
      have ha1 : a = 1 := by linarith
      rw [hB, ha1] at h2B
      norm_num at h2B
    · -- a - 2 = 0, so a = 2
      linarith
  · -- a + 1 = 0, so a = -1. Contradiction because 4 is in the intersection.
    have ha1 : a = -1 := by linarith
    have h3 : (4 : ℝ) ∈ A ∩ B := by
      constructor
      · -- Show 4 ∈ A
        rw [hA, ha1]
        norm_num
      · -- Show 4 ∈ B
        rw [hB, ha1]
        norm_num
    rw [hAB] at h3
    norm_num at h3