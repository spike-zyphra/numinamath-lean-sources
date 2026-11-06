import Mathlib
/-A ray emanating from the vertex $A$ of the triangle $A B C$ intersects the side $B C$ at $X$ and the circumcircle of $A B C$ at $Y$. Prove that $\frac{1}{A X}+\frac{1}{X Y} \geq \frac{4}{B C}$.-/
theorem Inequalities_239474 (AB BC CA AX XY BX XC: ℝ )(hside : AB > 0 ∧ BC > 0 ∧ CA > 0 ∧ AX > 0 ∧ XY > 0 ∧ BX > 0 ∧ XC > 0)
(hBC : BC=BX+XC)(intersecting_chords : AX*XY=BX*XC):1/AX+1/XY ≥ 4/BC:=by
    rcases hside with ⟨AB_pos, BC_pos, CA_pos, AX_pos, XY_pos, BX_pos, XC_pos⟩
    have h1 : BC = BX + XC := by linarith
    have h2 : AX * XY = BX * XC := by linarith

    have h3 : 1 / AX + 1 / XY = (AX + XY) / (AX * XY) := by
      field_simp [AX_pos, XY_pos]
      linarith

    have h4 : 1 / AX + 1 / XY - 4 / BC ≥ 0 := by
        have h5 : BC * (AX + XY) ≥ 4 * (AX * XY) := by
            nlinarith [sq_nonneg (AX - XY), sq_nonneg (BX - XC), sq_nonneg (AX - BX), sq_nonneg (AX - XC), sq_nonneg (XY - BX), sq_nonneg (XY - XC), mul_pos AX_pos XY_pos, mul_pos BX_pos XC_pos, hBC, intersecting_chords]

        have h6 : AX * XY > 0 := mul_pos AX_pos XY_pos
        have h7 : BC > 0 := BC_pos

        have h8 : (AX + XY) / (AX * XY) - 4 / BC ≥ 0 := by
            have h9 : AX * XY > 0 := h6
            have h10 : BC > 0 := h7

            have h11 : (AX + XY) / (AX * XY) - 4 / BC = (BC * (AX + XY) - 4 * (AX * XY)) / (AX * XY * BC) := by
                field_simp [h9, h10]
                ring

            have h12 : BC * (AX + XY) - 4 * (AX * XY) ≥ 0 := by linarith [h5]

            have h13 : AX * XY * BC > 0 := mul_pos (mul_pos AX_pos XY_pos) BC_pos

            rw [h11]
            exact div_nonneg h12 (by positivity)

        have h14 : 1 / AX + 1 / XY - 4 / BC = (AX + XY) / (AX * XY) - 4 / BC := by
            rw [h3]

        linarith [h14, h8]

    linarith [h4]