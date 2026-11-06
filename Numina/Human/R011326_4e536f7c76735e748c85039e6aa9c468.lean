import Mathlib

open Real Finset

/-
For positive real numbers $a, b, c$ such that $a^2 + b^2 + c^2 = 3$, prove that
\[
\frac{a^2}{2 + 2a + ab} + \frac{b^2}{2 + 2b + bc} + \frac{c^2}{2 + 2c + ca} \le \frac{9}{5(ab + bc + ca)}
\]
-/
theorem inequalities_619152 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hsum : a ^ 2 + b ^ 2 + c ^ 2 = 3) :
    a ^ 2 / (2 + 2 * a + a * b) + b ^ 2 / (2 + 2 * b + b * c) + c ^ 2 / (2 + 2 * c + c * a) ≤ 9 / (5 * (a * b + b * c + c * a)) := by
  --  1. By the Cauchy-Schwarz inequality (C-S), we have: [ (2 + 2a + ab)\left(2 + ab^2 + ac^2 + \frac{bc^2}{a}\right) \ge (2 + ab + ac + bc)^2 ]
  have h_cauchy_schwarz {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : (2 + 2 * a + a * b) * (2 + a * b ^ 2 + a * c ^ 2 + b * c ^ 2 / a) ≥ (2 + a * b + a * c + b * c) ^ 2 := by
    let f := ![2, a, a, a * b]
    let g := ![2, a * b ^ 2, a * c ^ 2, b * c ^ 2 / a]
    let r := ![2, a * b, a * c, b * c]
    have hf : ∀ i ∈ univ, 0 ≤ f i := by
      intro i _
      fin_cases i
      all_goals
        simp [f]
        all_goals positivity
    have hg : ∀ i ∈ univ, 0 ≤ g i := by
      intro i _
      fin_cases i
      all_goals
        simp [g]
        all_goals positivity
    have hr : ∀ i ∈ univ, r i ^ 2 = f i * g i := by
      intro i _
      fin_cases i
      all_goals
        simp [f, g, r]
        any_goals ring_nf
      field_simp
    obtain h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ hf hg hr
    simp [f, g, r, Fin.sum_univ_four] at h
    apply le_of_le_of_eq h
    ring
  --  2. Therefore, [ \sum \frac{a^2}{2 + 2a + ab} \le \frac{\sum a^2 \left(2 + ab^2 + ac^2 + \frac{bc^2}{a}\right)}{(2 + ab + bc + ca)^2} ]
  have h_div_le {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) :
      a ^ 2 / (2 + 2 * a + a * b) ≤ a ^ 2 * (2 + a * b ^ 2 + a * c ^ 2 + b * c ^ 2 / a) / (2 + a * b + b * c + c * a) ^ 2 := by
    trans a ^ 2 * (2 + a * b ^ 2 + a * c ^ 2 + b * c ^ 2 / a) / ((2 + 2 * a + a * b) * (2 + a * b ^ 2 + a * c ^ 2 + b * c ^ 2 / a))
    · apply le_of_eq
      field_simp
      ring
    · gcongr
      apply le_trans ?_ (h_cauchy_schwarz ha hb hc)
      apply le_of_eq
      ring
  --  3. Simplifying the numerator, we get: [ \sum a^2 \left(2 + ab^2 + ac^2 + \frac{bc^2}{a}\right) = 6 + \sum a^3(b^2 + c^2) + abc \sum a ]
  trans (a ^ 2 * (2 + a * b ^ 2 + a * c ^ 2 + b * c ^ 2 / a) + b ^ 2 * (2 + b * c ^ 2 + b * a ^ 2 + c * a ^ 2 / b) + c ^ 2 * (2 + c * a ^ 2 + c * b ^ 2 + a * b ^ 2 / c)) / (2 + a * b + b * c + c * a) ^ 2
  · rw [add_div, add_div]
    nth_rw 2 [show 2 + a * b + b * c + c * a = 2 + b * c + c * a + a * b by ring]
    nth_rw 2 [show 2 + a * b + b * c + c * a = 2 + c * a + a * b + b * c by ring]
    apply add_le_add (add_le_add ?_ ?_)
    all_goals
      apply le_of_eq_of_le
      · congr 1
      · apply h_div_le
        all_goals positivity
  --  4. Thus, [ \sum \frac{a^2}{2 + 2a + ab} \le \frac{6 + \sum a^3(b^2 + c^2) + abc \sum a}{(2 + ab + bc + ca)^2} ]
  trans (6 + (a ^ 3 * (b ^ 2 + c ^ 2) + b ^ 3 * (c ^ 2 + a ^ 2) + c ^ 3 * (a ^ 2 + b ^ 2)) + a * b * c * (a + b + c)) / (2 + a * b + b * c + c * a) ^ 2
  · apply le_of_eq
    congr 1
    rw [show 6 = 2 * (a ^ 2 + b ^ 2 + c ^ 2) by rw [hsum]; ring]
    field_simp
    ring
  --  5. Using the inequality $\sum a^3(b^2 + c^2) \le 6$ (which follows from Vasc's inequality for $x = a^2$, $y = b^2$, $z = c^2$ with $\sum a^2 = 3$), we have: [ \sum \frac{a^2}{2 + 2a + ab} \le \frac{12 + abc \sum a}{(2 + ab + bc + ca)^2} ]
  have hvasc : a ^ 3 * (b ^ 2 + c ^ 2) + b ^ 3 * (c ^ 2 + a ^ 2) + c ^ 3 * (a ^ 2 + b ^ 2) ≤ 6 :=  by
    trans a ^ 2 * (a * (3 - a ^ 2)) + b ^ 2 * (b * (3 - b ^ 2)) + c ^ 2 * (c * (3 - c ^ 2))
    · rw [←hsum]
      apply le_of_eq
      ring
    trans a ^ 2 * (2 - (a - 1) ^ 2 * (a + 2)) + b ^ 2 * (2 - (b - 1) ^ 2 * (b + 2)) + c ^ 2 * (2 - (c - 1) ^ 2 * (c + 2))
    · apply le_of_eq
      ring
    trans a ^ 2 * 2 + b ^ 2 * 2 + c ^ 2 * 2
    · gcongr
      all_goals simp; positivity
    · rw [←add_mul, ←add_mul, hsum]
      norm_num
  trans (6 + 6 + a * b * c * (a + b + c)) / (2 + a * b + b * c + c * a) ^ 2
  · rel [hvasc]
  · --  6. Let $\sum ab = X$ and $abc \sum a = Y$.
    let X := a * b + b * c + c * a
    let Y := a * b * c * (a + b + c)
    -- We know that: [ 3 = \sum a^2 \ge \sum ab = X \quad \text{and} \quad 3X \ge X^2 \ge 3Y \implies X \ge Y ]
    have hXY : X ≥ Y := by
      have h₁ : X ^ 2 ≥ 3 * Y := by
        unfold X Y
        clear * - ha hb hc
        wlog h : a ≤ b ∧ b ≤ c with H
        · simp at h
          by_cases hab : a ≤ b
          · obtain h := h hab
            by_cases hca : c ≤ a
            · obtain H := H hc ha hb  ⟨hca, hab⟩
              apply le_of_eq_of_le ?_ (le_of_le_of_eq H ?_) <;> ring
            · simp at hca
              obtain H := H ha hc hb ⟨le_of_lt hca, le_of_lt h⟩
              apply le_of_eq_of_le ?_ (le_of_le_of_eq H ?_) <;> ring
          · simp at hab
            by_cases hcb : c ≤ b
            · obtain H := H hc hb ha ⟨hcb, le_of_lt hab⟩
              apply le_of_eq_of_le ?_ (le_of_le_of_eq H ?_) <;> ring
            · simp at hcb
              by_cases hac : a ≤ c
              · obtain H := H hb ha hc ⟨le_of_lt hab, hac⟩
                apply le_of_eq_of_le ?_ (le_of_le_of_eq H ?_) <;> ring
              · simp at hac
                obtain H := H hb hc ha ⟨le_of_lt hcb, le_of_lt hac⟩
                apply le_of_eq_of_le ?_ (le_of_le_of_eq H ?_) <;> ring
        · apply sub_nonneg.mp
          ring_nf
          let f (i : Fin 3) :=
            match i with
            | 0 => 1 / a
            | 1 => 1 / b
            | 2 => 1 / c
          let g (i : Fin 3) :=
            match i with
            | 0 => b * c
            | 1 => c * a
            | 2 => a * b
          obtain ⟨hab, hbc⟩ := h
          have hfg : Monovary f g := by
            refine Antitone.monovary ?_ ?_
            · intro i j h
              fin_cases i
              all_goals
                fin_cases j
                any_goals
                  simp at h ⊢
                all_goals
                  simp [f]
                  apply inv_le_inv₀ ?_ ?_ |>.mpr
                  · linarith only [hab, hbc]
                  all_goals positivity
            · intro i j h
              fin_cases i
              all_goals
                fin_cases j
                any_goals
                  simp at h ⊢
                all_goals
                  simp [g]
                  nlinarith
          let σ : Equiv.Perm (Fin 3) := by
            apply Equiv.mk (![2, 0, 1]) (![1, 2, 0])
            · intro i
              fin_cases i
              all_goals
                simp
            · intro i
              fin_cases i
              all_goals
                simp
          obtain h := Monovary.sum_mul_comp_perm_le_sum_mul (σ := σ) hfg
          simp [Fin.sum_univ_three, f, g, σ] at h
          apply mul_le_mul_of_nonneg_left (a := a * b * c) at h
          obtain hmul : 0 ≤ a * b * c := by positivity
          apply h at hmul
          field_simp at hmul
          apply sub_nonneg.mpr at hmul
          apply le_of_le_of_eq hmul
          ring
      have h₂ : 3 * X ≥ X ^ 2 := by
        rw [sq]
        apply mul_le_mul_of_nonneg_right
        · rw [←hsum]
          unfold X
          let f (i : Fin 3) :=
            match i with
            | 0 => a
            | 1 => b
            | 2 => c
          have hfg : Monovary f f := by exact monovary_self f
          let σ : Equiv.Perm (Fin 3) := by
            apply Equiv.mk (![1, 2, 0]) (![2, 0, 1])
            · intro i
              fin_cases i
              all_goals
                simp
            · intro i
              fin_cases i
              all_goals
                simp
          obtain h := Monovary.sum_mul_comp_perm_le_sum_mul (σ := σ) hfg
          simp [Fin.sum_univ_three, f, σ] at h
          rw [sq, sq, sq]
          exact h
        · positivity
      apply le_trans h₁ at h₂
      linarith only [h₂]
    --  7. It is sufficient to show: [ \frac{12 + Y}{(X + 2)^2} \le \frac{9}{5X} ]
    suffices h : (12 + Y) / (X + 2) ^ 2 ≤ 9 / (5 * X)
    · apply le_of_eq_of_le ?_ (le_of_le_of_eq h ?_)
      · congr 1
        · unfold Y
          ring
        · unfold X
          ring
      · unfold X
        rfl
    · --  8. This inequality is equivalent to: [ 60X + 5XY \le 9(X^2 + 4X + 4) ]
      --  9. Simplifying, we get: [ 9X^2 + 36 \ge 24X + 5XY ]
      suffices h : 9 * X ^ 2 + 36 ≥ 24 * X + 5 * X * Y
      · apply div_le_div_iff₀ ?_ ?_ |>.mpr
        any_goals positivity
        linarith only [h]
      · -- 10. By the AM-GM inequality, we have: [ 4X^2 + 36 \ge 24X \quad \text{and} \quad 5X^2 \ge 5XY ]
        -- 11. Therefore, the inequality holds, and the proof is complete. Equality holds when $a = b = c = 1$
        apply sub_nonneg.mp
        trans 4 * (X - 3) ^ 2 + 5 * X * (X - Y)
        · apply add_nonneg
          · positivity
          · apply mul_nonneg
            · positivity
            · apply sub_nonneg.mpr
              exact hXY
        · apply le_of_eq
          ring
