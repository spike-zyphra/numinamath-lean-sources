import Mathlib

/- Given real numbers $x, y, z$ such that $x+y+z=0$, show that

$$
\frac{x(x+2)}{2 x^{2}+1}+\frac{y(y+2)}{2 y^{2}+1}+\frac{z(z+2)}{2 z^{2}+1} \geq 0 .
$$

When does equality hold? -/
theorem inequalities_604175 (x y z : ℝ) (h : x + y + z = 0) :
    0 ≤ x * (x + 2) / (2 * x ^ 2 + 1) + y * (y + 2) / (2 * y ^ 2 + 1) + z * (z + 2) / (2 * z ^ 2 + 1) ∧
    (0 = x * (x + 2) / (2 * x ^ 2 + 1) + y * (y + 2) / (2 * y ^ 2 + 1) + z * (z + 2) / (2 * z ^ 2 + 1) ↔
    (x, y, z) ∈ ({(0, 0, 0), (1, -1 / 2, -1/ 2), (-1 / 2, 1, -1 / 2), (-1 / 2, -1 / 2, 1)} : Set <| ℝ × ℝ × ℝ)) := by
  -- The inequality is clear if $x y z=0$, in which case equality holds if and only if $x=y=z=0$.
  by_cases hmul : x * y * z = 0
  · simp at hmul
    rcases hmul with (hx | hy) | hz
    · simp [hx] at h ⊢
      have : y = -z := by exact eq_neg_of_add_eq_zero_left h
      rw [this, neg_sq, ←add_div, mul_add, mul_add, neg_mul, mul_neg, neg_neg]
      constructor
      · apply div_nonneg
        · ring_nf
          apply mul_nonneg
          · apply sq_nonneg
          · simp
        · apply add_nonneg
          · apply mul_nonneg
            · simp
            · apply sq_nonneg
          · simp
      · field_simp
        have : z * z + -(z * 2) + (z * z + z * 2) = 2 * z ^ 2 := by ring
        rw [this]
        simp only [zero_eq_mul, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, false_or]
    · simp [hy] at h ⊢
      have : x = -z := by exact eq_neg_of_add_eq_zero_left h
      rw [this, neg_sq, ←add_div, mul_add, mul_add, neg_mul, mul_neg, neg_neg]
      constructor
      · apply div_nonneg
        · ring_nf
          apply mul_nonneg
          · apply sq_nonneg
          · simp
        · apply add_nonneg
          · apply mul_nonneg
            · simp
            · apply sq_nonneg
          · simp
      · field_simp
        have : z * z + -(z * 2) + (z * z + z * 2) = 2 * z ^ 2 := by ring
        rw [this]
        simp only [zero_eq_mul, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, false_or]
    · simp [hz] at h ⊢
      have : x = -y := by exact eq_neg_of_add_eq_zero_left h
      rw [this, neg_sq, ←add_div, mul_add, mul_add, neg_mul, mul_neg, neg_neg]
      constructor
      · apply div_nonneg
        · ring_nf
          apply mul_nonneg
          · apply sq_nonneg
          · simp
        · apply add_nonneg
          · apply mul_nonneg
            · simp
            · apply sq_nonneg
          · simp
      · field_simp
        have : y * y + -(y * 2) + (y * y + y * 2) = 2 * y ^ 2 := by ring
        rw [this]
        simp only [zero_eq_mul, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, false_or]
  · -- Henceforth assume $x y z \neq 0$ and rewrite the inequality as
    -- $$ \frac{(2 x+1)^{2}}{2 x^{2}+1}+\frac{(2 y+1)^{2}}{2 y^{2}+1}+\frac{(2 z+1)^{2}}{2 z^{2}+1} \geq 3 . $$
    have h₀ : (2 * x + 1) ^ 2 / (2 * x ^ 2 + 1) + (2 * y + 1) ^ 2 / (2 * y ^ 2 + 1) + (2 * z + 1) ^ 2 / (2 * z ^ 2 + 1) =
        2 * (x * (x + 2) / (2 * x ^ 2 + 1) + y * (y + 2) / (2 * y ^ 2 + 1) + z * (z + 2) / (2 * z ^ 2 + 1)) + 3 := by
      field_simp
      ring
    have h₁ : x * (x + 2) / (2 * x ^ 2 + 1) + y * (y + 2) / (2 * y ^ 2 + 1) + z * (z + 2) / (2 * z ^ 2 + 1) ≥ 0 ↔
        (2 * x + 1) ^ 2 / (2 * x ^ 2 + 1) + (2 * y + 1) ^ 2 / (2 * y ^ 2 + 1) + (2 * z + 1) ^ 2 / (2 * z ^ 2 + 1) ≥ 3 := by
      rw [h₀]
      simp only [ge_iff_le, le_add_iff_nonneg_left, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    have h₂ : 0 = x * (x + 2) / (2 * x ^ 2 + 1) + y * (y + 2) / (2 * y ^ 2 + 1) + z * (z + 2) / (2 * z ^ 2 + 1) ↔
        (2 * x + 1) ^ 2 / (2 * x ^ 2 + 1) + (2 * y + 1) ^ 2 / (2 * y ^ 2 + 1) + (2 * z + 1) ^ 2 / (2 * z ^ 2 + 1) = 3 := by
      rw [h₀]
      simp only [add_left_eq_self, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      simp only [eq_comm]
    simp only [h₁, h₂]
    clear h₀ h₁ h₂
    -- Notice that (exactly) one of the products $x y, y z, z x$ is positive, say $y z&gt;0$, to get
    wlog hyz : y * z > 0 with H
    · by_cases hxz : x * z > 0
      · obtain H := H y x z (by rw [←h]; ring) (by intro h; rw [←h] at hmul; apply hmul; ring) hxz
        constructor
        · apply le_trans H.1
          apply le_of_eq
          ring
        · have : (y, x, z) ∈ ({(0, 0, 0), (1, -1 / 2, -1 / 2), (-1 / 2, 1, -1 / 2), (-1 / 2, -1 / 2, 1)} : Set <| ℝ × ℝ × ℝ) ↔
              (x, y, z) ∈ ({(0, 0, 0), (1, -1 / 2, -1 / 2), (-1 / 2, 1, -1 / 2), (-1 / 2, -1 / 2, 1)} : Set <| ℝ × ℝ × ℝ) := by
            simp
            constructor <;> intro h
            all_goals
              rcases h with h | h | h | h
              all_goals
                obtain ⟨hx, hy, hz⟩ := h
                simp [hx, hy, hz]
          simp only [←this, ←H.2]
          constructor <;> intro h
          all_goals
            rw [←h]
            ring
      · have hxy : x * y > 0 := by
          by_contra hxy
          have : (x * y * z) ^ 2 ≤ 0 := by
            trans x * y * (y * z) * (x * z)
            · apply le_of_eq
              ring
            · apply mul_nonpos_of_nonneg_of_nonpos
              · apply mul_nonneg_of_nonpos_of_nonpos
                · exact le_of_not_lt hxy
                · exact le_of_not_lt hyz
              · exact le_of_not_lt hxz
          apply hmul
          apply le_antisymm (sq_nonneg _) at this
          exact pow_eq_zero (id (Eq.symm this))
        obtain H := H z x y (by rw [←h]; ring) (by intro h; rw [←h] at hmul; apply hmul; ring) hxy
        constructor
        · apply le_trans H.1
          apply le_of_eq
          ring
        · have : (z, x, y) ∈ ({(0, 0, 0), (1, -1 / 2, -1 / 2), (-1 / 2, 1, -1 / 2), (-1 / 2, -1 / 2, 1)} : Set <| ℝ × ℝ × ℝ) ↔
              (x, y, z) ∈ ({(0, 0, 0), (1, -1 / 2, -1 / 2), (-1 / 2, 1, -1 / 2), (-1 / 2, -1 / 2, 1)} : Set <| ℝ × ℝ × ℝ) := by
            simp
            constructor <;> intro h
            all_goals
              rcases h with h | h | h | h
              all_goals
                obtain ⟨hx, hy, hz⟩ := h
                simp [hx, hy, hz]
          simp only [←this, ←H.2]
          constructor <;> intro h
          all_goals
            rw [←h]
            ring
    · -- $$ \begin{array}{rlr} \frac{(2 y+1)^{2}}{2 y^{2}+1}+\frac{(2 z+1)^{2}}{2 z^{2}+1} & \geq \frac{2(y+z+1)^{2}}{y^{2}+z^{2}+1} & \text { (by Jensen) } \ & =\frac{2(x-1)^{2}}{x^{2}-2 y z+1} & (\text { for } x+y+z=0) \ & \geq \frac{2(x-1)^{2}}{x^{2}+1} . & (\text { for } y z&gt;0) \end{array} $$
      have hjensen : (2 * y + 1) ^ 2 / (2 * y ^ 2 + 1) + (2 * z + 1) ^ 2 / (2 * z ^ 2 + 1) ≥ 2 * (y + z + 1) ^ 2 / (y ^ 2 + z ^ 2 + 1) := by
        let f (i : Fin 2) : ℝ :=
          match i with
          | 0 => 2 * y + 1
          | 1 => 2 * z + 1
        let g (i : Fin 2) : ℝ :=
          match i with
          | 0 => 2 * y ^ 2 + 1
          | 1 => 2 * z ^ 2 + 1
        have hg : ∀ i ∈ Finset.univ, 0 < g i := by
          intro i _
          simp [g]
          fin_cases i
          all_goals positivity
        obtain h := Finset.sq_sum_div_le_sum_sq_div _ f hg
        simp [f, g] at h
        trans (2 * y + 1) ^ 2 / (2 * y ^ 2 + 1) + (2 * z + 1) ^ 2 / (2 * z ^ 2 + 1)
        · apply le_of_eq
          ring
        · apply le_trans ?_ h
          apply le_of_eq
          field_simp
          ring
      -- Here equality holds if and only if $x=1$ and $y=z=-1 / 2$.
      have hjensen_gt (h1 : y ≠ z) (h2 : 2 * y * z + y + z - 1 ≠ 0) : (2 * y + 1) ^ 2 / (2 * y ^ 2 + 1) + (2 * z + 1) ^ 2 / (2 * z ^ 2 + 1) > 2 * (y + z + 1) ^ 2 / (y ^ 2 + z ^ 2 + 1) := by
        have {a b c d : ℝ} (h : a * d ≠ b * c) (hc : c > 0) (hd : d > 0) : (a + b) ^ 2 / (c + d) < a ^ 2 / c + b ^ 2 / d := by
          field_simp
          apply div_lt_div_iff₀ ?_ ?_ |>.mpr
          · apply sub_pos.mp
            apply lt_of_lt_of_eq (b := (a * d - b * c) ^ 2)
            · apply sq_pos_of_ne_zero
              exact sub_ne_zero_of_ne h
            · ring
          · positivity
          · positivity
        let a := 2 * y + 1
        let b := 2 * z + 1
        let c := 2 * y ^ 2 + 1
        let d := 2 * z ^ 2 + 1
        have h : a * d ≠ b * c := by
          intro h
          unfold a d b c at h
          apply sub_eq_zero.mpr at h
          have : (2 * y + 1) * (2 * z ^ 2 + 1) - (2 * z + 1) * (2 * y ^ 2 + 1) = 2 * (z - y) * (2 * y * z + y + z - 1) := by ring
          rw [this] at h
          simp [h2] at h
          apply sub_eq_zero.mp at h
          exact h1.elim (Eq.symm h)
        have hc : c > 0 := by positivity
        have hd : d > 0 := by positivity
        apply this h hc at hd
        unfold a b c d at hd
        apply lt_of_le_of_lt (le_of_eq ?_) hd
        field_simp
        ring
      have hden_le : 2 * (y + z + 1) ^ 2 / (y ^ 2 + z ^ 2 + 1) ≥ 2 * (x - 1) ^ 2 / (x ^ 2 + 1) := by
        have : y + z + 1 = -(x - 1) := by linarith
        rw [this, neg_sq]
        apply div_le_div_of_nonneg_left
        · apply mul_nonneg
          · simp
          · apply sq_nonneg
        · positivity
        · simp
          have : x = -(y + z) := by linarith
          rw [this, neg_sq, add_sq, mul_assoc]
          simp
          exact le_of_lt hyz
      have hden_lt (h : x ≠ 1) : 2 * (y + z + 1) ^ 2 / (y ^ 2 + z ^ 2 + 1) > 2 * (x - 1) ^ 2 / (x ^ 2 + 1) := by
        have : y + z + 1 = -(x - 1) := by linarith
        rw [this, neg_sq]
        apply div_lt_div_of_pos_left
        · apply mul_pos
          · simp
          · apply sq_pos_of_ne_zero
            exact sub_ne_zero_of_ne h
        · positivity
        · simp
          have : x = -(y + z) := by linarith
          rw [this, neg_sq, add_sq, mul_assoc]
          simp
          exact hyz
      -- Finally, since
      -- $$ \frac{(2 x+1)^{2}}{2 x^{2}+1}+\frac{2(x-1)^{2}}{x^{2}+1}-3=
      -- \frac{2 x^{2}(x-1)^{2}}{\left(2 x^{2}+1\right)\left(x^{2}+1\right)} \geq 0, \quad x \in \mathbb{R}, $$
      have final : (2 * x + 1) ^ 2 / (2 * x ^ 2 + 1) + 2 * (x - 1) ^ 2 / (x ^ 2 + 1) ≥ 3 := by
        apply sub_nonneg.mp
        trans 2 * x ^ 2 * (x - 1) ^ 2 / ((2 * x ^ 2 + 1) * (x ^ 2 + 1))
        · positivity
        · apply le_of_eq
          field_simp
          ring
      have hge : (2 * x + 1) ^ 2 / (2 * x ^ 2 + 1) + (2 * y + 1) ^ 2 / (2 * y ^ 2 + 1) + (2 * z + 1) ^ 2 / (2 * z ^ 2 + 1) ≥ 3 := by
        trans (2 * x + 1) ^ 2 / (2 * x ^ 2 + 1) + 2 * (y + z + 1) ^ 2 / (y ^ 2 + z ^ 2 + 1)
        · rw [add_assoc]
          apply add_le_add
          · rfl
          · apply hjensen
        · trans (2 * x + 1) ^ 2 / (2 * x ^ 2 + 1) + 2 * (x - 1) ^ 2 / (x ^ 2 + 1)
          · gcongr
          · exact final
      -- the conclusion follows.
      constructor
      · exact hge
      · -- Clearly, equality holds if and only if $x=1$, so $y=z=-1 / 2$.
        constructor <;> intro h'
        · have hfinal_eq : (2 * x + 1) ^ 2 / (2 * x ^ 2 + 1) + 2 * (x - 1) ^ 2 / (x ^ 2 + 1) = 3 := by
            apply le_antisymm ?_ final
            rw [←h', add_assoc _ ((2 * y + 1) ^ 2 / (2 * y ^ 2 + 1))]
            apply add_le_add
            · rfl
            · apply le_trans hden_le
              apply hjensen
          have hden_eq : 2 * (y + z + 1) ^ 2 / (y ^ 2 + z ^ 2 + 1) = 2 * (x - 1) ^ 2 / (x ^ 2 + 1) := by
            apply le_antisymm ?_ hden_le
            rw [←h', add_assoc _ ((2 * y + 1) ^ 2 / (2 * y ^ 2 + 1))] at hfinal_eq
            simp at hfinal_eq
            rw [hfinal_eq]
            apply hjensen
          have hjensen_eq : (2 * y + 1) ^ 2 / (2 * y ^ 2 + 1) + (2 * z + 1) ^ 2 / (2 * z ^ 2 + 1) = 2 * (y + z + 1) ^ 2 / (y ^ 2 + z ^ 2 + 1) := by
            apply le_antisymm ?_ hjensen
            rw [hden_eq]
            rw [←h', add_assoc _ ((2 * y + 1) ^ 2 / (2 * y ^ 2 + 1))] at hfinal_eq
            simp at hfinal_eq
            rw [←hfinal_eq]
          have h₀ : x = 1 := by
            by_contra h
            apply hden_lt at h
            rw [hden_eq] at h
            apply lt_self_iff_false _ |>.mp h
          have h₁ : y = z := by
            by_contra h
            have : 2 * y * z + y + z - 1 ≠ 0 := by
              have : y + z = -1 := by
                rw [←h₀]
                rename_i hsum
                linarith only [hsum]
              rw [add_assoc, this]
              by_contra h
              have hyz : y * z = 1 := by
                linarith only [h]
              have h : y ^ 2 + z ^ 2 = - 1 := by
                trans (y + z) ^ 2 - 2 * (y * z)
                · ring
                · rw [this, hyz]
                  norm_num
              have h' : y ^ 2 + z ^ 2 ≥ 0 := by positivity
              simp [h] at h'
              norm_num at h'
            apply hjensen_gt h at this
            rw [hjensen_eq] at this
            apply lt_self_iff_false _ |>.mp this
          simp [h₀, h₁]
          norm_num
          rw [h₀, h₁] at h
          linarith only [h]
        · simp at h'
          rcases h' with h' | h' | h' | h'
          all_goals
            obtain ⟨hx, hy, hz⟩ := h'
            simp [hx, hy, hz]
            norm_num
