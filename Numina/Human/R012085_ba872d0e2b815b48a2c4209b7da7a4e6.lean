import Mathlib

/- Man beweise oder widerlege, dass für alle positiven reellen Zahlen $a, b$ und $c$ die Ungleichung

$$
3 \leq \frac{4 a+b}{a+4 b}+\frac{4 b+c}{b+4 c}+\frac{4 c+a}{c+4 a}<\frac{33}{4}
$$ -/
theorem inequalities_604589 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 ≤ (4 * a + b) / (a + 4 * b) + (4 * b + c) / (b + 4 * c) + (4 * c + a) / (c + 4 * a) ∧
    (4 * a + b) / (a + 4 * b) + (4 * b + c) / (b + 4 * c) + (4 * c + a) / (c + 4 * a) < 33 / 4 := by

  -- the denominator is positive
  have h1 : 0 < a + 4 * b := by
    apply add_pos ha
    exact mul_pos (by simp) hb
  have h2 : 0 < b + 4 * c := by
    apply add_pos hb
    exact mul_pos (by simp) hc
  have h3 : 0 < c + 4 * a := by
    apply add_pos hc
    exact mul_pos (by simp) ha

  constructor
  · -- Proof of $3 \leq \frac{4 a+b}{a+4 b}+\frac{4 b+c}{b+4 c}+\frac{4 c+a}{c+4 a}$:
    -- Multiplying by the main denominator and simplifying leads to the equivalent inequality
    -- $45 a b c \leq 7\left(a^{2} b+b^{2} c+c^{2} a\right)+8\left(a b^{2}+b c^{2}+c a^{2}\right)$.
    suffices h :  45 * a * b * c ≤ 7 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) + 8 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2)
    · field_simp
      apply le_div_iff₀ (mul_pos (mul_pos h1 h2) h3) |>.mpr
      calc
        _ = 3 * (45 * a * b * c) + 60 * a * b * c + a * b ^ 2 * 48 + a * c ^ 2 * 12 + a ^ 2 * b * 12 + a ^ 2 * c * 48 + b * c ^ 2 * 48 + b ^ 2 * c * 12 := by ring
        _ ≤ 3 * (7 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) + 8 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2)) + 60 * a * b * c +
            a * b ^ 2 * 48 + a * c ^ 2 * 12 + a ^ 2 * b * 12 + a ^ 2 * c * 48 + b * c ^ 2 * 48 + b ^ 2 * c * 12 := by rel [h]
        _ = _ := by ring
    · -- This follows from the inequality between the arithmetic and geometric mean
      -- (e.g., $a^{2} b+b^{2} c+c^{2} a \geq 3 \sqrt[3]{a^{2} b \cdot b^{2} c \cdot c^{2} a}=3 a b c$).
      have hle1 : a ^ 2 * b + b ^ 2 * c + c ^ 2 * a ≥ 3 * (a * b * c) := by
        obtain h := @Real.geom_mean_le_arith_mean3_weighted (1 / 3) (1 / 3) (1 / 3) (a ^ 2 * b) (b ^ 2 * c) (c ^ 2 * a)
            (by simp) (by simp) (by simp) (le_of_lt (mul_pos (sq_pos_of_pos ha) hb)) (le_of_lt (mul_pos (sq_pos_of_pos hb) hc)) (le_of_lt (mul_pos (sq_pos_of_pos hc) ha)) (by norm_num)
        calc
          _ = 3 * (1 / 3 * (a ^ 2 * b) + 1 / 3 * (b ^ 2 * c) + 1 / 3 * (c ^ 2 * a)) := by ring
          _ ≥ 3 * ((a ^ 2 * b) ^ (1 / 3 : ℝ) * (b ^ 2 * c) ^ (1 / 3 : ℝ) * (c ^ 2 * a) ^ (1 / 3 : ℝ)) := by rel [h]
          _ = _ := by
            rw [Real.mul_rpow (sq_nonneg a) (le_of_lt hb), Real.mul_rpow (sq_nonneg b) (le_of_lt hc), Real.mul_rpow (sq_nonneg c) (le_of_lt ha)]
            rw [←Real.rpow_natCast, ←Real.rpow_natCast, ←Real.rpow_natCast]
            rw [←Real.rpow_mul (le_of_lt ha), ←Real.rpow_mul (le_of_lt hb), ←Real.rpow_mul (le_of_lt hc)]
            field_simp
            calc
              _ = a ^ (2 / 3 : ℝ) * a ^ (1 / 3 : ℝ) * (b ^ (2 / 3 : ℝ) * b ^ (1 / 3 : ℝ)) * (c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ)) := by ring
              _ = _ := by
                rw [←Real.rpow_add ha, ←Real.rpow_add hb, ←Real.rpow_add hc]
                norm_num
      -- We can also apply the inequality between the arithmetic and geometric mean to the terms $a b^{2}, b c^{2}, c a^{2}$, which leads to the inequality
      have hle2 : a * b ^ 2 + b * c ^ 2 + c * a ^ 2 ≥ 3 * (a * b * c) := by
        obtain h := @Real.geom_mean_le_arith_mean3_weighted (1 / 3) (1 / 3) (1 / 3) (a * b ^ 2) (b * c ^ 2) (c * a ^ 2)
            (by simp) (by simp) (by simp) (le_of_lt (mul_pos ha (sq_pos_of_pos hb))) (le_of_lt (mul_pos hb (sq_pos_of_pos hc))) (le_of_lt (mul_pos hc (sq_pos_of_pos ha))) (by norm_num)
        calc
          _ = 3 * (1 / 3 * (a * b ^ 2) + 1 / 3 * (b * c ^ 2) + 1 / 3 * (c * a ^ 2)) := by ring
          _ ≥ 3 * ((a * b ^ 2) ^ (1 / 3 : ℝ) * (b * c ^ 2) ^ (1 / 3 : ℝ) * (c * a ^ 2) ^ (1 / 3 : ℝ)) := by rel [h]
          _ = _ := by
            rw [Real.mul_rpow (le_of_lt ha) (sq_nonneg b), Real.mul_rpow (le_of_lt hb) (sq_nonneg c), Real.mul_rpow (le_of_lt hc) (sq_nonneg a)]
            rw [←Real.rpow_natCast, ←Real.rpow_natCast, ←Real.rpow_natCast]
            rw [←Real.rpow_mul (le_of_lt ha), ←Real.rpow_mul (le_of_lt hb), ←Real.rpow_mul (le_of_lt hc)]
            field_simp
            calc
              _ = a ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ) * (b ^ (1 / 3 : ℝ) * b ^ (2 / 3 : ℝ)) * (c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ)) := by ring
              _ = _ := by
                rw [←Real.rpow_add ha, ←Real.rpow_add hb, ←Real.rpow_add hc]
                norm_num
      calc
        _ = 7 * (3 * (a * b * c)) + 8 * (3 * (a * b * c)) := by ring
        _ ≤ 7 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) + 8 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) := by rel [hle1, hle2]
  · -- wlog, we assume that a ≥ b and a ≥ c.
    clear h1 h2 h3
    wlog h : a ≥ b ∧ a ≥ c with H
    · -- otherwise, perform a permutation of the variables
      simp at h
      by_cases h₁ : b ≤ a
      · obtain h := h h₁
        obtain H := H c a b hc ha hb ⟨le_of_lt h, le_trans h₁ (le_of_lt h)⟩
        exact lt_of_eq_of_lt (by ring) H
      · simp at h₁
        by_cases h₂ : c ≤ b
        · obtain H := H b c a hb hc ha ⟨h₂, (le_of_lt h₁)⟩
          exact lt_of_eq_of_lt (by ring) H
        · simp at h₂
          obtain H := H c a b hc ha hb ⟨le_of_lt (lt_trans h₁ h₂), le_of_lt h₂⟩
          exact lt_of_eq_of_lt (by ring) H
    · -- then if b ≤ c
      by_cases hbc : b ≤ c
      · -- It is easy to show that (4 * a + b) / (a + 4 * b) ≤ 4
        have h1 : (4 * a + b) / (a + 4 * b) ≤ 4 := by
          apply div_le_iff₀ (add_pos ha (mul_pos (by simp) hb)) |>.mpr
          calc
            _ = 4 * (a + 4 * b) - 15 * b := by ring
            _ ≤ 4 * (a + 4 * b) := by simp; exact le_of_lt hb
        -- and (4 * b + c) / (b + 4 * c) ≤ 1
        have h2 : (4 * b + c) / (b + 4 * c) ≤ 1 := by
          apply div_le_iff₀ (add_pos hb (mul_pos (by simp) hc)) |>.mpr
          calc
            _ = b + c + 3 * b := by ring
            _ ≤ b + c + 3 * c := by rel [hbc]
            _ = _ := by ring
        -- and (4 * c + a) / (c + 4 * a) ≤ 1
        have h3 : (4 * c + a) / (c + 4 * a) ≤ 1 := by
          apply div_le_iff₀ (add_pos hc (mul_pos (by simp) ha)) |>.mpr
          calc
            _ = c + a + 3 * c := by ring
            _ ≤ c + a + 3 * a := by rel [h.2]
            _ = _ := by ring
        -- then the sum is less than 6 < 33 / 4
        calc
          _ ≤ (4 : ℝ) + 1 + 1 := by rel [h1, h2, h3]
          _ < 33 / 4 := by norm_num
      · simp at hbc
        -- otherwise, c < b
        -- then (4 * c + a) / (c + 4 * a) ≤ (4 * b + a) / (b + 4 * a)
        have h1 : (4 * c + a) / (c + 4 * a) ≤ (4 * b + a) / (b + 4 * a) := by
          apply div_le_div_iff ?_ ?_ |>.mpr
          · apply le_of_sub_nonneg
            ring_nf
            calc
              _ = b * a * 15 - a * b * 15 := by ring
              _ ≤ _ := by apply sub_le_sub (by simp); rel [le_of_lt hbc]
          · exact add_pos hc (mul_pos (by simp) ha)
          · exact add_pos hb (mul_pos (by simp) ha)
        -- and (4 * b + c) / (b + 4 * c) < 4
        have h2 : (4 * b + c) / (b + 4 * c) < 4 := by
          apply div_lt_iff₀ (add_pos hb (mul_pos (by simp) hc)) |>.mpr
          apply lt_of_sub_pos
          ring_nf
          simp
          exact hc
        -- (4 * a + b) / (a + 4 * b) + (4 * b + a) / (b + 4 * a) ≤ 17 / 4 since b ≤ a ≤ 1
        have h3 : (4 * a + b) / (a + 4 * b) + (4 * b + a) / (b + 4 * a) ≤ 17 / 4 := by
          field_simp
          apply div_le_div_iff ?_ ?_ |>.mpr
          · apply le_of_sub_nonneg
            ring_nf
            exact mul_nonneg (mul_nonneg (le_of_lt ha) (le_of_lt hb)) (by simp)
          · apply mul_pos
            · exact add_pos ha (mul_pos (by simp) hb)
            · exact add_pos hb (mul_pos (by simp) ha)
          · simp
        -- suming up all the inequalities gives
        -- (4 * a + b) / (a + 4 * b) + (4 * b + c) / (b + 4 * c) + (4 * c + a) / (c + 4 * a) < 33 / 4
        calc
          _ ≤ (4 * a + b) / (a + 4 * b) + (4 * b + c) / (b + 4 * c) + (4 * b + a) / (b + 4 * a) := by rel [h1]
          _ < (4 * a + b) / (a + 4 * b) + 4 + (4 * b + a) / (b + 4 * a) := by rel [h2]
          _ = (4 * a + b) / (a + 4 * b) + (4 * b + a) / (b + 4 * a) + 4 := by ring
          _ ≤ 17 / 4 + 4 := by rel [h3]
          _ = _ := by ring
