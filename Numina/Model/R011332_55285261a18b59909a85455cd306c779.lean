import Mathlib
theorem Inequalities_239474 (AB BC CA AX XY BX XC: ℝ )(hside : AB > 0 ∧ BC > 0 ∧ CA > 0 ∧ AX > 0 ∧ XY > 0 ∧ BX > 0 ∧ XC > 0)
(hBC : BC=BX+XC)(intersecting_chords : AX*XY=BX*XC):1/AX+1/XY ≥ 4/BC:=by

  rcases hside with ⟨hAB, hBC_pos, hCA, hAX, hXY, hBX, hXC⟩

  have h1 : 1 / AX + 1 / XY = (AX + XY) / (AX * XY) := by
    field_simp
    <;> linarith

  rw [h1] 

  have h2 : 0 < BC := hBC_pos
  have h3 : 0 < AX := hAX
  have h4 : 0 < XY := hXY
  have h5 : 0 < AX * XY := mul_pos h3 h4
  have h6 : 0 < (AX + XY) := by linarith
  have h7 : 0 < (BC) := hBC_pos

  have h8 : (AX + XY) * BC ≥ 4 * (AX * XY) := by
    have h9 : BC = BX + XC := hBC
    have h10 : 0 < BX := hBX
    have h11 : 0 < XC := hXC
    have h12 : BX * XC > 0 := mul_pos h10 h11
    have h13 : AX * XY = BX * XC := by linarith
    nlinarith [sq_nonneg (AX - XY), sq_nonneg (BX - XC), sq_nonneg (AX + XY - (BX + XC)), sq_nonneg (AX * XY - BX * XC), mul_pos h10 h11, mul_pos h3 h4, mul_pos h3 h4, mul_pos h10 h11, h13, mul_pos h10 h11, mul_pos h3 h4]

  have h9 : 0 < (AX * XY) := h5
  have h10 : 0 < (BC) := h7

  apply (div_le_div_iff (by positivity) (by positivity)).mpr 
  nlinarith