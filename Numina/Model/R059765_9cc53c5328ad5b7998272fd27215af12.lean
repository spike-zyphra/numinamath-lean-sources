import Mathlib

theorem algebra_6541
    {A B C D : ℝ}
    (hAB : A / B = 1 / 4)
    (hBC : B / C = 3 / 2)
    (hCD : C / D = 1 / 4)
    (hsum : A + B + C + D = 550) :
    D = 320 := by
  have h1 : B ≠ 0 := by
    by_contra h
    rw [h] at hAB
    norm_num at hAB
  have h2 : C ≠ 0 := by
    by_contra h
    rw [h] at hBC
    norm_num at hBC
  have h3 : D ≠ 0 := by
    by_contra h
    rw [h] at hCD
    norm_num at hCD
  have hA : A = B / 4 := by
    field_simp [h1] at hAB
    linarith
  have hB : B = 3 / 2 * C := by
    field_simp [h2] at hBC
    linarith
  have hC : C = 1 / 4 * D := by
    field_simp [h3] at hCD
    linarith
  have hB' : B = 3 / 8 * D := by
    rw [show C = 1 / 4 * D by linarith [hC] ] at hB
    linarith
  have hA' : A = 3 / 32 * D := by
    rw [show B = 3 / 8 * D by linarith [hB'] ] at hA
    linarith
  -- Substitute A, B, C into the equation using the values expressed in terms of D
  rw [show A = 3 / 32 * D by linarith [hA'] ] at hsum
  rw [show B = 3 / 8 * D by linarith [hB'] ] at hsum
  rw [show C = 1 / 4 * D by linarith [hC] ] at hsum
  linarith