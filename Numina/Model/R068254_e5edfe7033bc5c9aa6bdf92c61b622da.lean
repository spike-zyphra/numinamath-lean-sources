import Mathlib

theorem algebra_21775 (A B C D E F G H : ℝ × ℝ)
    (h₀ : A = (0, 10)) (h₁ : B = (0, 0)) (h₂ : C = (10, 0))
    (h₃ : D = (10, 6)) (h₄ : E = (6, 6)) (h₅ : F = (6, 2))
    (h₆ : G = (2, 2)) (h₇ : H = (2, 10)) :
    Real.sqrt ((B.1 - A.1)^2 + (B.2 - A.2)^2) +
    Real.sqrt ((C.1 - B.1)^2 + (C.2 - B.2)^2) +
    Real.sqrt ((D.1 - C.1)^2 + (D.2 - C.2)^2) +
    Real.sqrt ((E.1 - D.1)^2 + (E.2 - D.2)^2) +
    Real.sqrt ((F.1 - E.1)^2 + (F.2 - E.2)^2) +
    Real.sqrt ((G.1 - F.1)^2 + (G.2 - F.2)^2) +
    Real.sqrt ((H.1 - G.1)^2 + (H.2 - G.2)^2) +
    Real.sqrt ((A.1 - H.1)^2 + (A.2 - H.2)^2) = 48 := by

  have h_AB : Real.sqrt ((B.1 - A.1)^2 + (B.2 - A.2)^2) = 10 := by
    rw [h₀, h₁]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h_BC : Real.sqrt ((C.1 - B.1)^2 + (C.2 - B.2)^2) = 10 := by
    rw [h₁, h₂]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h_CD : Real.sqrt ((D.1 - C.1)^2 + (D.2 - C.2)^2) = 6 := by
    rw [h₂, h₃]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h_DE : Real.sqrt ((E.1 - D.1)^2 + (E.2 - D.2)^2) = 4 := by
    rw [h₃, h₄]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h_EF : Real.sqrt ((F.1 - E.1)^2 + (F.2 - E.2)^2) = 4 := by
    rw [h₄, h₅]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h_FG : Real.sqrt ((G.1 - F.1)^2 + (G.2 - F.2)^2) = 4 := by
    rw [h₅, h₆]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h_GH : Real.sqrt ((H.1 - G.1)^2 + (H.2 - G.2)^2) = 8 := by
    rw [h₆, h₇]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h_HA : Real.sqrt ((A.1 - H.1)^2 + (A.2 - H.2)^2) = 2 := by
    rw [h₀, h₇]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  rw [h_AB, h_BC, h_CD, h_DE, h_EF, h_FG, h_GH, h_HA]
  norm_num