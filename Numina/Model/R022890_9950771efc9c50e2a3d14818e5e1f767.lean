import Mathlib

theorem algebra_312523 {f g : ℝ → ℝ}
    (hf : f = fun x => -x^2 - 3 * x + 4) (hg : g = fun x => x^2 - 3 * x - 4)
    (A B P Q : ℝ × ℝ)
    (hA : f A.1 = g A.1) (hB : f B.1 = g B.1)
    (hP : f P.1 = g P.1) (hQ : f Q.1 = g Q.1)
    (hAB : A.1 < B.1) (hPQ : P.1 ∈ Set.Ioo A.1 B.1) (hQW : Q.1 ∈ Set.Ioo A.1 B.1) :
    B.1 - A.1 = 8 ∧ P.2 = Q.2 := by
  have h1 : - (A.1) ^2 - 3 * A.1 + 4 = (A.1) ^2 - 3 * A.1 - 4 := by
    rw [hf] at hA
    rw [hg] at hA
    simp at hA ⊢
    linarith
  have h2 : - (B.1) ^2 - 3 * B.1 + 4 = (B.1) ^2 - 3 * B.1 - 4 := by
    rw [hf] at hB
    rw [hg] at hB
    simp at hB ⊢
    linarith
  have eq1 : (A.1) ^2 = 4 := by
    nlinarith
  have eq2 : (B.1) ^2 = 4 := by
    nlinarith
  have eq3 : A.1 = -2 := by
    have h1 : A.1 ^2 = 4 := by
      nlinarith
    have h6 : A.1 = 2 ∨ A.1 = -2 := by
      have h1 : A.1 ^2 - 4 = 0 := by
        linarith
      have h2 : (A.1 - 2) * (A.1 + 2) = 0 := by
        linarith
      cases' (mul_eq_zero.mp h2) with h4 h5
      · left
        linarith
      · right
        linarith
    cases' h6 with h7 h8
    · -- A.1 = 2, which would not satisfy A.1 < B.1
      nlinarith [sq_nonneg (B.1), sq_nonneg (A.1), sq_nonneg (B.1 - A.1), sq_nonneg (B.1 + 2)]
    · -- A.1 = -2
      linarith
  have eq4 : B.1 = 2 := by
    have h1 : B.1 ^2 = 4 := by
      nlinarith
    have h6 : B.1 = 2 ∨ B.1 = -2 := by
      have h1 : B.1 ^2 - 4 = 0 := by
        linarith
      have h2 : (B.1 - 2) * (B.1 + 2) = 0 := by
        linarith
      cases' (mul_eq_zero.mp h2) with h4 h5
      · left
        linarith
      · right
        linarith
    cases' h6 with h7 h8
    · -- B.1 = 2
      linarith
    · -- B.1 = -2, which would not satisfy A.1 < B.1
      nlinarith [sq_nonneg (B.1), sq_nonneg (A.1), sq_nonneg (B.1 - A.1), sq_nonneg (B.1 + 2)]
  have h3 : P.1 ∈ Set.Ioo A.1 B.1 := hPQ
  rw [Set.mem_Ioo] at h3
  have h11 : -2 < P.1 := by
    nlinarith [eq3, h3.1]
  have h12 : P.1 < 2 := by
    nlinarith [eq4, h3.2]
  have h4 : - (P.1) ^2 - 3 * P.1 + 4 = (P.1) ^2 - 3 * P.1 - 4 := by
    rw [hf] at hP
    rw [hg] at hP
    simp at hP ⊢
    linarith
  nlinarith