import Mathlib
open Finset Real

/--
  Find the smallest real constant $\alpha$ such that for all positive integers $n$ and real numbers $0=y_{0}<$ $y_{1}<\cdots < y_{n}$,
  the following inequality holds:
  $$
  \alpha \sum_{k=1}^{n} \frac{(k+1)^{3 / 2}}{\sqrt{y_{k}^{2}-y_{k-1}^{2}}} \geq \sum_{k=1}^{n} \frac{k^{2}+3 k+3}{y_{k}} \text {. }
  $$
-/
theorem inequalities_610173 :
    IsLeast {α : ℝ | ∀ n : ℕ, n > 0 → ∀ y : ℕ → ℝ, y 0 = 0 →
    (∀ i ∈ range n, y i < y (i + 1)) →
    α * ∑ k ∈ Icc 1 n, (k + 1) ^ (3 / 2 : ℝ) / √(y k ^ 2 - y (k - 1) ^ 2) ≥
    ∑ k ∈ Icc 1 n, (k ^ 2 + 3 * k + 3) / y k} (16 * √2 / 9) := by
  simp [IsLeast]
  constructor
  · intro n hn y hy0 hylt
    have hy_pos {k : ℕ} (hk : k ∈ Icc 1 n) : y k > 0 := by
      simp at hk
      obtain ⟨h₁, h₂⟩ := hk
      induction k, h₁ using Nat.le_induction
      · simp
        rw [←hy0]
        apply hylt
        exact hn
      · rename_i k hk' ih
        apply lt_trans (ih (Nat.le_of_succ_le h₂))
        apply hylt
        exact h₂
    -- We first prove the following lemma by holder's inequality
    have lem {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) :
      a ^ (3 / 2 : ℝ) / √c + b ^ (3 / 2 : ℝ) / √d ≥ (a + b) ^ (3 / 2 : ℝ) / √(c + d) := by
      let f (x : Fin 2) :=
        match x with
        | 0 => a / c ^ (1 / 3 : ℝ)
        | 1 => b / d ^ (1 / 3 : ℝ)
      let g (x : Fin 2) :=
        match x with
        | 0 => c ^ (1 / 3 : ℝ)
        | 1 => d ^ (1 / 3 : ℝ)
      let p : ℝ := 3 / 2
      let q : ℝ := 3
      have hpq : p.IsConjExponent q := by
        apply IsConjExponent.mk
        · unfold p; norm_num
        · unfold p q; norm_num
      obtain h := inner_le_Lp_mul_Lq univ f g hpq
      rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at h
      simp [f, g, p ,q] at h
      rw [div_mul_cancel₀, div_mul_cancel₀] at h
      trans ((|a / c ^ (3 : ℝ)⁻¹| ^ (3 / 2 : ℝ) + |b / d ^ (3 : ℝ)⁻¹| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) * (|c ^ (3 : ℝ)⁻¹| ^ (3 : ℝ) + |d ^ (3 : ℝ)⁻¹| ^ (3 : ℝ)) ^ (3 : ℝ)⁻¹) ^ (3 / 2 : ℝ) / √(c + d)
      · apply le_of_eq
        rw [abs_of_nonneg, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg]
        rw [mul_rpow]
        rw [div_rpow, div_rpow, ←rpow_mul, ←rpow_mul, ←rpow_mul, ←rpow_mul]
        rw [←rpow_mul, ←rpow_mul, sqrt_eq_rpow, sqrt_eq_rpow, sqrt_eq_rpow]
        norm_num
        rw [mul_div_cancel_right₀]
        all_goals positivity
      · gcongr
      all_goals positivity
    -- For $k≥2$, applying the lemma to $a=(k-1)^2, b = 8 k +8,c=y_{k-1}^2, d = y ^ k ^ 2 - y_{k-1}^2$ yields
    -- (k-1)^3/y_{k-1}^2 + 8 k + 8 / (y_k^2 - y_{k-1}^2) ≥ (k+3)^3/y_k
    have hge {k : ℕ} (hk : k ∈ Icc 2 n) : (k - 1) ^ 3 / y (k - 1) + (8 * k + 8) ^ (3 / 2 : ℝ) / √(y k ^ 2 - y (k - 1) ^ 2) ≥
        (k + 3) ^ 3 / y k := by
      simp at hk
      obtain ⟨h₁, h₂⟩ := hk
      have ha : ((k - 1) ^ 2 : ℝ) > 0 := by
        apply pow_pos
        simp
        exact h₁
      have hb : 8 * k + 8 > (0 : ℝ) := by
        simp
        linarith only [h₁]
      have hc : y (k - 1) ^ 2 > 0 := by
        apply pow_pos
        apply hy_pos
        simp
        constructor
        · exact Nat.le_sub_one_of_lt h₁
        · exact Nat.le_add_right_of_le h₂
      have hd : y k ^ 2 - y (k - 1) ^ 2 > 0 := by
        simp
        apply pow_lt_pow_left₀ ?_ ?_ ?_
        · nth_rw 2 [←Nat.sub_add_cancel (Nat.one_le_of_lt h₁)]
          apply hylt
          apply Nat.sub_one_lt_of_le ?_ h₂
          exact Nat.zero_lt_of_lt h₁
        · apply le_of_lt
          apply hy_pos
          simp
          constructor
          · exact Nat.le_sub_one_of_lt h₁
          · exact Nat.le_add_right_of_le h₂
        · simp
      obtain h := lem ha hb hc hd
      rw [sqrt_sq, add_sub_cancel, sqrt_sq] at h
      trans ((↑k - 1) ^ 2) ^ (3 / 2 : ℝ) / y (k - 1) + (8 * ↑k + 8) ^ (3 / 2 : ℝ) / √(y k ^ 2 - y (k - 1) ^ 2)
      · apply le_of_eq
        congr 2
        rw [←rpow_natCast _ 2, ←rpow_mul]
        norm_num
        norm_cast
        simp
        exact Nat.one_le_of_lt h₁
      · apply le_trans ?_ h
        apply le_of_eq
        congr 1
        have : (↑k - 1 : ℝ) ^ 2 + (8 * ↑k + 8) = (k + 3) ^ 2 := by ring
        rw [this, ←rpow_natCast _ 2, ←rpow_mul]
        norm_num
        · norm_cast
        · norm_cast
          simp
      · apply le_of_lt
        apply hy_pos
        simp
        constructor
        · exact Nat.one_le_of_lt h₁
        · exact h₂
      · apply le_of_lt
        apply hy_pos
        simp
        constructor
        · exact Nat.le_sub_one_of_lt h₁
        · exact Nat.le_add_right_of_le h₂
    -- We also have (k - 1) ^ 3 / y (k - 1) + (8 * k + 8) ^ (3 / 2 : ℝ) / √(y k ^ 2 - y (k - 1) ^ 2) ≥ (k + 3) ^ 3 / y k when k = 1
    have hge1 : (8 * 1 + 8) ^ (3 / 2 : ℝ) / √(y 1 ^ 2 - y 0 ^ 2) ≥
        (1 + 3) ^ 3 / y 1 := by
      simp [hy0]
      rw [sqrt_sq]
      apply le_of_eq
      congr 1
      norm_num
      · rw [show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num]
        rw [←rpow_natCast _ 2, ←rpow_mul]
        norm_num
        simp
      · apply le_of_lt
        apply hy_pos
        simp
        exact hn
    -- Summing the inequalities from $k=2$ to $k=n$ yields
    have hsum : ∑ k ∈ Icc 1 n, (8 * ↑k + 8) ^ (3 / 2 : ℝ) / √(y k ^ 2 - y (k - 1) ^ 2) ≥ 9 * ∑ k ∈ Icc 1 n, (k ^ 2 + 3 * k + 3) / y k := by
      trans (1 + 3) ^ 3 / y 1 + ∑ k ∈ Icc 2 n, ((k + 3) ^ 3 / y k - (k - 1) ^ 3 / y (k - 1))
      · rw [Icc_eq_cons_Ioc hn, sum_cons]
        apply add_le_add
        · simp at hge1 ⊢
          exact hge1
        · rw [←Nat.Icc_succ_left]
          apply sum_le_sum
          intro i hi
          linarith only [hge hi]
      · rw [sum_sub_distrib]
        trans ∑ k ∈ Icc 1 n, ((k + 3) ^ 3 - k ^ 3) / y k + n ^ 3 / y n
        · simp [sub_div, sum_sub_distrib]
          rw [Icc_eq_cons_Ioc hn, sum_cons, add_sub_assoc, add_assoc]
          apply add_le_add
          · simp
          · rw [Nat.Icc_succ_left]
            rw [←Icc_eq_cons_Ioc hn, Icc_eq_cons_Ico hn, sum_cons]
            rw [add_comm, sub_add_eq_sub_sub, ←add_sub_assoc, add_sub_cancel]
            gcongr
            apply le_of_eq
            have : (Ioc 1 n).image (fun k : ℕ => k - 1) = Ico 1 n := by
              ext k
              simp
              constructor <;> intro h
              · obtain ⟨a, ⟨h₁, h₂⟩, heq⟩ := h
                rw [←heq]
                constructor
                · exact Nat.le_sub_one_of_lt h₁
                · apply Nat.sub_one_lt_of_le
                  exact Nat.zero_lt_of_lt h₁
                  exact h₂
              · obtain ⟨h₁, h₂⟩ := h
                use k + 1
                constructor
                · constructor
                  · exact Nat.lt_add_of_pos_left h₁
                  · exact h₂
                · rw [Nat.add_sub_cancel]
            rw [←this, sum_image]
            · apply sum_congr rfl
              intro k hk
              rw [Nat.cast_sub]
              simp
              simp at hk
              apply le_of_lt hk.1
            · intro x hx y hy h
              apply tsub_left_inj ?_ ?_ |>.mp h
              · simp at hx
                exact le_of_lt hx.1
              · simp at hy
                exact le_of_lt hy.1
        · trans ∑ k ∈ Icc 1 n, ((k + 3) ^ 3 - k ^ 3) / y k + 0
          · apply add_le_add
            · simp
            · apply div_nonneg
              · positivity
              · apply le_of_lt
                apply hy_pos
                simp
                exact hn
          · simp
            apply le_of_eq
            rw [mul_sum]
            congr
            ext i
            field_simp
            congr
            ring
    field_simp
    apply le_div_iff₀ ?_ |>.mpr
    · rw [mul_comm]
      apply le_trans hsum
      apply le_of_eq
      rw [mul_sum]
      congr
      ext i
      field_simp
      congr
      rw [show 8 * (i : ℝ) + 8 = 8 * (i + 1) by ring, mul_rpow]
      congr
      apply rpow_left_inj ?_ ?_ (show 2 ≠ 0 by simp) |>.mp
      rw [←rpow_mul, mul_rpow]
      norm_num
      all_goals positivity
    all_goals positivity
  · -- In the reverse direction, this is sharp when yn=n(n+1)(n+2)(n+3)
    unfold lowerBounds
    apply Set.mem_setOf.mpr
    intro r hr
    by_contra hlt
    push_neg at hlt
    simp at hr
    let y (n : ℕ) : ℝ := n * (n + 1) * (n + 2) * (n + 3)
    have hr {n : ℕ} (hn : n > 0) :  ∑ k ∈ Icc 1 n, (↑k ^ 2 + 3 * ↑k + 3) / y k ≤
        r * ∑ k ∈ Icc 1 n, (↑k + 1) ^ (3 / 2 : ℝ) / √(y k ^ 2 - y (k - 1) ^ 2) := by
      apply hr n hn
      · simp [y]
      · intro i hi
        simp [y]
        apply sub_pos.mp
        ring_nf
        positivity
    have LHS {n : ℕ} (hn : n > 0) : ∑ k ∈ Icc 1 n, (↑k + 1) ^ (3 / 2 : ℝ) / √(y k ^ 2 - y (k - 1) ^ 2) = 1 / (2 * √2) * ∑ k ∈ Icc 1 n, 1 / (k * (k + 2) : ℝ) := by
      have {k : ℕ} (hk : k ≥ 1) : y k ^ 2 - y (k - 1) ^ 2 = 8 * k ^ 2 * (k + 2) ^ 2 * (k + 1) ^ 3 := by
        unfold y
        rw [Nat.cast_sub hk]
        ring
      have {k : ℕ} (hk : k ≥ 1) : (↑k + 1) ^ (3 / 2 : ℝ) / √(y k ^ 2 - y (k - 1) ^ 2) = 1 / (2 * √2) * (1 / (k * (k + 2))) := by
        rw [this hk, sqrt_eq_rpow, mul_rpow, ←rpow_natCast _ 3, ←rpow_mul, show (8 : ℝ) = 2 ^ 2 * 2 by ring]
        rw [←sqrt_eq_rpow, sqrt_mul, sqrt_mul, sqrt_mul, sqrt_sq, sqrt_sq, sqrt_sq]
        field_simp
        ring
        all_goals positivity
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [this]
      simp at hk
      exact hk.1
    have RHS {n : ℕ} (hn : n > 0) : ∑ k ∈ Icc 1 n, (↑k ^ 2 + 3 * ↑k + 3) / y k =
        ∑ k ∈ Icc 1 n, 1 / (k * (k + 2) : ℝ) - ∑ k ∈ Icc 1 n, 1 / ((k + 1) * (k + 2) * (k + 3) : ℝ) := by
      rw [←sum_sub_distrib]
      apply sum_congr rfl
      intro k hk
      simp at hk
      obtain hk := hk.1
      unfold y
      field_simp
      ring
    have hr {n : ℕ} (hn : n > 0) : (1 - r / (2 * √2)) * ∑ k ∈ Icc 1 n, 1 / (k * (k + 2) : ℝ) ≤ ∑ k ∈ Icc 1 n, 1 / ((k + 1) * (k + 2) * (k + 3) : ℝ) := by
      obtain hr := hr hn
      rw [LHS hn, RHS hn] at hr
      apply sub_nonneg.mp
      apply sub_nonneg.mpr at hr
      apply le_of_le_of_eq hr
      ring
    have LHS {n : ℕ} (hn : n > 0) : ∑ k ∈ Icc 1 n, 1 / (k * (k + 2) : ℝ) = 3 / 4 - (2 * n + 3) / (2 * (n + 1) * (n + 2)) := by
      induction n, hn using Nat.le_induction
      · simp
        norm_num
      · rename_i n hn ih
        rw [←Nat.Icc_insert_succ_right, sum_insert]
        · rw [ih]
          field_simp
          ring
        · simp
        · simp
    have LHS_gt {n : ℕ} (hn : n > 0) : ∑ k ∈ Icc 1 n, 1 / (k * (k + 2) : ℝ) > 3 / 4 - 1 / n := by
      rw [LHS hn]
      simp only [sub_lt_sub_iff_left]
      apply div_lt_div_iff₀ ?_ ?_ |>.mpr
      apply sub_pos.mp
      ring_nf
      all_goals positivity
    have RHS {n : ℕ} (hn : n > 0) : ∑ k ∈ Icc 1 n, 1 / ((k + 1) * (k + 2) * (k + 3) : ℝ) =
        1 / 12 - 1 / (2 * (n + 2) * (n + 3)) := by
      induction n, hn using Nat.le_induction
      · simp
        norm_num
      · rename_i n hn ih
        rw [←Nat.Icc_insert_succ_right, sum_insert]
        · rw [ih]
          field_simp
          ring
        · simp
        · simp
    have RHS_lt {n : ℕ} (hn : n > 0) : ∑ k ∈ Icc 1 n, 1 / ((k + 1) * (k + 2) * (k + 3) : ℝ) < 1 / 12 := by
      rw [RHS hn]
      simp
      positivity
    have hrlt : r / (2 * √2) < 8 / 9 := by
      apply lt_of_lt_of_eq (b := (16 * √2 / 9) / (2 * √2))
      · rel [hlt]
      · field_simp
        ring
    have hr {n : ℕ} (hn : n > 0) : (1 - r / (2 * √2)) * (3 / 4 - 1 / n) < 1 / 12 := by
      trans (1 - r / (2 * √2)) * ∑ k ∈ Icc 1 n, 1 / (k * (k + 2) : ℝ)
      · apply mul_lt_mul_of_pos_left
        · apply LHS_gt
          exact hn
        · simp
          apply lt_trans hrlt
          norm_num
      · apply lt_of_le_of_lt (hr hn)
        exact RHS_lt hn
    let n' : ℕ := Nat.ceil (1 / (3 / 4 - (1 / 12) / (1 - r / (2 * √2)))) + 1
    have hnpos : n' > 0 := by simp
    have hn' : n' ≥ 1 / (3 / 4 - (1 / 12) / (1 - r / (2 * √2))) := by
      trans (Nat.ceil (1 / (3 / 4 - (1 / 12) / (1 - r / (2 * √2)))) : ℝ)
      · unfold n'
        norm_cast
        simp
      · apply Nat.le_ceil
    have : ¬ (1 - r / (2 * √2)) * (3 / 4 - 1 / n') < 1 / 12 := by
      push_neg
      trans (1 - r / (2 * √2)) * (3 / 4 - 1 / (1 / (3 / 4 - (1 / 12) / (1 - r / (2 * √2)))))
      · apply le_of_eq
        rw [div_div_eq_mul_div, one_mul, div_one, sub_sub_self, mul_div_cancel₀]
        apply ne_of_gt
        simp
        apply lt_trans hrlt
        norm_num
      · apply mul_le_mul_of_nonneg_left
        · apply sub_le_sub_left
          apply one_div_le_one_div ?_ ?_ |>.mpr hn'
          · positivity
          · apply div_pos
            · positivity
            · apply sub_pos.mpr
              apply lt_of_lt_of_eq (b := 1 / 12 / (1 - 8 / 9))
              · apply div_lt_div_iff_of_pos_left ?_ ?_ ?_|>.mpr
                · apply sub_lt_sub_left hrlt
                · positivity
                · apply sub_pos.mpr
                  apply lt_trans hrlt
                  norm_num
                · positivity
              · norm_num
        · apply sub_nonneg.mpr
          apply le_trans (le_of_lt hrlt)
          norm_num
    exact this.elim (hr hnpos)