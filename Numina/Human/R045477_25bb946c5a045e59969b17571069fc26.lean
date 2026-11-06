import Mathlib
open Real

/- ■Let $a, b, c \in \mathbf{R}^{+}$, prove: $a^{2 a} b^{2 b} c^{2 c} \geqslant a^{b+c} b^{c+a} c^{a+b}$. -/
theorem inequalities_597760 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^(2 * a) * b^(2 * b) * c^(2 * c) ≥ a^(b + c) * b^(c + a) * c^(a + b) := by
  have h_main : a^(2 * a) * b^(2 * b) * c^(2 * c) ≥ a^(b + c) * b^(c + a) * c^(a + b) := by
    -- Use wlog to assume $a ≥ b ≥ c$.
    wlog h1 : a ≥ b
    · -- If $a < b$, swap $a$ and $b$ and apply symmetry.
      have h₂ := this b a c (by linarith) (by linarith) (by linarith) (by linarith)
      have h₃ : b^(2 * b) * a^(2 * a) * c^(2 * c) ≥ b^(a + c) * a^(c + b) * c^(b + a) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using h₂
      have h₄ : a^(2 * a) * b^(2 * b) * c^(2 * c) ≥ a^(b + c) * b^(c + a) * c^(a + b) := by
        calc
          a^(2 * a) * b^(2 * b) * c^(2 * c) = b^(2 * b) * a^(2 * a) * c^(2 * c) := by ring
          _ ≥ b^(a + c) * a^(c + b) * c^(b + a) := by simpa [mul_assoc, mul_comm, mul_left_comm] using h₃
          _ = a^(b + c) * b^(c + a) * c^(a + b) := by ring_nf
      exact h₄
    · -- Continue to assume $b ≥ c$.
      wlog h2 : b ≥ c
      · -- If $b < c$, swap $b$ and $c$ and apply symmetry.
        have h₃ := this a c b ha hc hb
        by_cases h4 : a ≥ c
        · -- If $a ≥ c$.
          have h₅ : a^(2 * a) * c^(2 * c) * b^(2 * b) ≥ a^(c + b) * c^(b + a) * b^(a + c) := by
            simpa [mul_assoc, mul_comm, mul_left_comm] using h₃ h4 (by linarith)
          have h₆ : a^(2 * a) * b^(2 * b) * c^(2 * c) ≥ a^(b + c) * b^(c + a) * c^(a + b) := by
            calc
              a^(2 * a) * b^(2 * b) * c^(2 * c) = a^(2 * a) * c^(2 * c) * b^(2 * b) := by ring
              _ ≥ a^(c + b) * c^(b + a) * b^(a + c) := by simpa [mul_assoc, mul_comm, mul_left_comm] using h₅
              _ = a^(b + c) * b^(c + a) * c^(a + b) := by ring_nf
          exact h₆
        · -- If $a < c$.
          have h₅ : c^(2 * c) * b^(2 * b) * a^(2 * a) ≥ c^(a + b) * b^(c + a) * a^(b + c) := by
            have h₅₁ := this c a b hc ha hb (by linarith) (by linarith)
            simpa [mul_assoc, mul_comm, mul_left_comm,add_comm] using h₅₁
          have h₆ : a^(2 * a) * b^(2 * b) * c^(2 * c) ≥ a^(b + c) * b^(c + a) * c^(a + b) := by
            calc
              a^(2 * a) * b^(2 * b) * c^(2 * c) = c^(2 * c) * b^(2 * b) * a^(2 * a) := by ring
              _ ≥ c^(a + b) * b^(c + a) * a^(b + c) := by simpa [mul_assoc, mul_comm, mul_left_comm] using h₅
              _ = a^(b + c) * b^(c + a) * c^(a + b) := by ring
          exact h₆
      · -- Now assume $a ≥ b ≥ c$.
        have h_ratio : a^(2 * a) * b^(2 * b) * c^(2 * c) / (a^(b + c) * b^(c + a) * c^(a + b)) =
          (a / b)^(a - b) * (b / c)^(b - c) * (a / c)^(a - c) := by
          -- Compute the exponent of the quotient.
          calc
            a^(2 * a) * b^(2 * b) * c^(2 * c) / (a^(b + c) * b^(c + a) * c^(a + b))
              = a^(2 * a - (b + c)) * b^(2 * b - (c + a)) * c^(2 * c - (a + b)) := by
                rw [div_eq_mul_inv, mul_inv]
                rw [rpow_sub ha, rpow_sub hb, rpow_sub hc]
                field_simp [ha, hb, hc]
              _ = a^((a - b) + (a - c)) * b^((b - c) + (b - a)) * c^((c - a) + (c - b)) := by
                congr <;> ring
              _ = (a^(a - b) * a^(a - c)) * (b^(b - c) * b^(b - a)) * (c^(c - a) * c^(c - b)) := by
                rw [rpow_add ha, rpow_add hb, rpow_add hc]
              _ = (a^(a - b) / b^(a - b)) * (b^(b - c) / c^(b - c)) * (a^(a - c) / c^(a - c)) := by
                have h1 : a^(a - b) * b^(b - a) = a^(a - b) / b^(a - b) := by
                  have h1_aux : b^(b - a) = b^(-(a - b)) := by
                    congr
                    ring
                  rw [h1_aux, rpow_neg (le_of_lt hb)]
                  field_simp [hb]
                have h2 : b^(b - c) * c^(c - b) = b^(b - c) / c^(b - c) := by
                  have h2_aux : c^(c - b) = c^(-(b - c)) := by
                    congr
                    ring
                  rw [h2_aux, rpow_neg (le_of_lt hc)]
                  field_simp [hc]
                have h3 : a^(a - c) * c^(c - a) = a^(a - c) / c^(a - c) := by
                  have h3_aux : c^(c - a) = c^(-(a - c)) := by
                    congr
                    ring
                  rw [h3_aux, rpow_neg (le_of_lt hc)]
                  field_simp [hc]
                have h_rearrange : (a^(a - b) * a^(a - c)) * (b^(b - c) * b^(b - a)) * (c^(c - a) * c^(c - b)) =
                  (a^(a - b) * b^(b - a)) * (b^(b - c) * c^(c - b)) * (a^(a - c) * c^(c - a)) := by
                  ring
                rw [h_rearrange]
                rw [h1, h2, h3]
              _ = (a / b)^(a - b) * (b / c)^(b - c) * (a / c)^(a - c) := by
                rw [div_rpow (le_of_lt ha) (le_of_lt hb), div_rpow (le_of_lt hb) (le_of_lt hc), div_rpow (le_of_lt ha) (le_of_lt hc)]
        have h_ratio_ge_1 : (a / b)^(a - b) * (b / c)^(b - c) * (a / c)^(a - c) ≥ 1 := by
          -- Since $a ≥ b ≥ c$, check each term.
          have h_ab : a / b ≥ 1 := by
            rw [ge_iff_le, one_le_div₀ hb]
            exact h1
          have h_bc : b / c ≥ 1 := by
            rw [ge_iff_le, one_le_div₀ hc]
            exact h2
          have h_ac : a / c ≥ 1 := by
            rw [ge_iff_le, one_le_div₀ hc]
            exact le_trans h2 h1
          have h_exp_ab : a - b ≥ 0 := by exact sub_nonneg.mpr h1
          have h_exp_bc : b - c ≥ 0 := by exact sub_nonneg.mpr h2
          have h_exp_ac : a - c ≥ 0 := by exact sub_nonneg.mpr (le_trans h2 h1)
          -- Each term $(x)^y ≥ 1$ when $x ≥ 1$ and $y ≥ 0$.
          have h_term1 : (a / b)^(a - b) ≥ 1 := by
            exact Real.one_le_rpow h_ab h_exp_ab
          have h_term2 : (b / c)^(b - c) ≥ 1 := by
            exact Real.one_le_rpow h_bc h_exp_bc
          have h_term3 : (a / c)^(a - c) ≥ 1 := by
            exact Real.one_le_rpow h_ac h_exp_ac
          -- The product $ge 1$.
          calc
            (a / b)^(a - b) * (b / c)^(b - c) * (a / c)^(a - c)
              ≥ 1 * 1 * 1 := by gcongr
            _ = 1 := by ring
        have h_ineq : a^(2 * a) * b^(2 * b) * c^(2 * c) ≥ a^(b + c) * b^(c + a) * c^(a + b) := by
          -- The quotient $ge 1$ implies the original inequality holds.
          have h_rhs_pos : a^(b + c) * b^(c + a) * c^(a + b) > 0 := by
            apply mul_pos
            · apply mul_pos
              · exact Real.rpow_pos_of_pos ha (b + c)
              · exact Real.rpow_pos_of_pos hb (c + a)
            · exact Real.rpow_pos_of_pos hc (a + b)
          have h_div_ge_1: a^(2 * a) * b^(2 * b) * c^(2 * c) / (a^(b + c) * b^(c + a) * c^(a + b)) ≥ 1 := by
            rw [h_ratio]
            exact h_ratio_ge_1
          have : a^(b + c) * b^(c + a) * c^(a + b) ≤ a^(2 * a) * b^(2 * b) * c^(2 * c) := by
            rw [ge_iff_le] at h_div_ge_1
            rw [one_le_div h_rhs_pos] at h_div_ge_1
            exact h_div_ge_1
          exact this
        exact h_ineq
  exact h_main