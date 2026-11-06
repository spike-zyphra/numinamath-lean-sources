import Mathlib
open Finset Set Nat Real
set_option maxHeartbeats 500000
noncomputable section

-- Define $g(x) = max_{a ≤ t ≤ b} |x + t|$.
def g (a b x : ℝ) : ℝ := sSup {y : ℝ | ∃ t ∈ Icc a b, y = |x + t|}

-- Prove that the set ${ |x + t| | t ∈ [a, b] }$ has an upper bound $b - a + |x + a|$.
lemma bdd_above_abs_x_plus_t (a b x : ℝ) (hab : a < b) :
  BddAbove {y : ℝ | ∃ t ∈ Icc a b, y = |x + t|} := by
  use b - a + |x + a|
  rintro y ⟨t, ht, rfl⟩
  have h_t_ge_a : a ≤ t := by exact ht.1
  have h_t_le_b : t ≤ b := by exact ht.2
  have h_val_le_bound : |x + t| ≤ b - a + |x + a| := by
    cases' le_total 0 (x + t) with h_xt_nonneg h_xt_nonneg
    · rw [abs_of_nonneg h_xt_nonneg]
      cases' le_total 0 (x + a) with h_xa_nonneg h_xa_nonneg
      · rw [abs_of_nonneg h_xa_nonneg]
        linarith
      · rw [abs_of_nonpos h_xa_nonneg]
        linarith
    · rw [abs_of_nonpos h_xt_nonneg]
      cases' le_total 0 (x + a) with h_xa_nonneg h_xa_nonneg
      · rw [abs_of_nonneg h_xa_nonneg]
        linarith
      · rw [abs_of_nonpos h_xa_nonneg]
        linarith
  exact h_val_le_bound

/-10. Let $a, b \in \mathbf{R}, a<b$, the function $g(x)=\max _{a \leq t \leq b}|x+t|(x \in \mathbf{R})$ (where $\max _{a \leq t \leq b}$ denotes the maximum value of the expression $|x+t|$ for $x \in \mathbf{R}$ when $t \in[a, b]$), then the minimum value of $g(x)$ is-/
theorem algebra_244434 (a b : ℝ) (hab : a < b) : 
    IsLeast {y | ∃ x : ℝ, g a b x = y} ((b - a) / 2) := by
  have h_exists_x : ∃ (x : ℝ), g a b x = (b - a) / 2 := by
    use -(a + b) / 2
    have h_g_at_mid : g a b (-(a + b) / 2) = (b - a) / 2 := by
      have h_g_def : g a b (-(a + b) / 2) = sSup {y : ℝ | ∃ t ∈ Icc a b, y = |(-(a + b) / 2 : ℝ) + t|} := rfl
      rw [h_g_def]
      have h_sup_eq : sSup {y : ℝ | ∃ t ∈ Icc a b, y = |(-(a + b) / 2 : ℝ) + t|} = (b - a) / 2 := by
        have h_set_eq : {y : ℝ | ∃ t ∈ Icc a b, y = |(-(a + b) / 2 : ℝ) + t|} = {|(-(a + b) / 2 : ℝ) + t| | t ∈ Icc a b} := by
          ext y
          simp [Set.mem_setOf_eq, Set.mem_image]
          aesop
        rw [h_set_eq]
        -- The maximum of $|-(a + b)/2 + t|$ on $[a, b]$ is achieved at $t = a$ or $t = b$.
        have h_is_greatest : IsGreatest {|(-(a + b) / 2 : ℝ) + t| | t ∈ Icc a b} ((b - a) / 2) := by
          constructor
          · -- Prove that $(b - a)/2$ is in the set.
            use b
            constructor
            · -- Prove that b is in [a, b]
              exact ⟨by linarith, by linarith⟩
            · -- Prove that $|-(a + b)/2 + b| = (b - a)/2$.
              have h_val_at_b : |(-(a + b) / 2 : ℝ) + b| = (b - a) / 2 := by
                have h_expr_simp : (-(a + b) / 2 : ℝ) + b = (b - a) / 2 := by ring
                rw [h_expr_simp]
                have h_pos_ba : (b - a : ℝ) > 0 := by linarith
                have h_pos_half_ba : (b - a : ℝ) / 2 > 0 := by linarith
                rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b - a) / 2)]
              rw [h_val_at_b]
          · -- Prove that $(b - a)/2$ is the greatest element in the set.
            rintro y ⟨t, ht, rfl⟩
            -- For any y in the set, $y ≤ (b - a)/2$.
            have h_t_in_Icc : t ∈ Icc a b := ht
            have h_t_ge_a : a ≤ t := h_t_in_Icc.1
            have h_t_le_b : t ≤ b := h_t_in_Icc.2
            have h_val_le_half : |(-(a + b) / 2 : ℝ) + t| ≤ (b - a) / 2 := by
              rw [abs_le]
              constructor
              · -- Prove that $-((b - a)/2) ≤ -(a + b)/2 + t$.
                have h_bound_lower : -((b - a) / 2 : ℝ) ≤ (-(a + b) / 2 : ℝ) + t := by linarith
                linarith
              · -- Prove that $-(a + b)/2 + t ≤ (b - a)/2$.
                have h_bound_upper : (-(a + b) / 2 : ℝ) + t ≤ (b - a) / 2 := by linarith
                linarith
            exact h_val_le_half
        have h_sup_is_greatest : sSup {|(-(a + b) / 2 : ℝ) + t| | t ∈ Icc a b} = (b - a) / 2 := by
          exact IsGreatest.csSup_eq h_is_greatest
        rw [h_sup_is_greatest]
      rw [h_sup_eq]
    rw [h_g_at_mid]
  have h_lower_bound : ∀ (y : ℝ), (∃ (x : ℝ), g a b x = y) → (b - a) / 2 ≤ y := by
    intro y h
    rcases h with ⟨x, rfl⟩
    have h_g_ge_half : (b - a) / 2 ≤ g a b x := by
      have h_g_sup : g a b x = sSup {y : ℝ | ∃ t ∈ Icc a b, y = |x + t|} := rfl
      rw [h_g_sup]
      have h_sup_ge_half : (b - a) / 2 ≤ sSup {y : ℝ | ∃ t ∈ Icc a b, y = |x + t|} := by
        -- We need to show that $(b - a)/2$ Less than or equal to the supremum of ${ |x + t| | t ∈ [a, b] }$.
        have h_exists_t : ∃ (t : ℝ), t ∈ Icc a b ∧ |x + t| ≥ (b - a) / 2 := by
          by_cases h_xa_nonneg : x + a ≥ 0
          · -- Case :$ x + a ≥ 0$.
            by_cases h_xb_nonneg : x + b ≥ 0
            · have h_abs_xa : |x + a| = x + a := by rw [abs_of_nonneg h_xa_nonneg]
              have h_abs_xb : |x + b| = x + b := by rw [abs_of_nonneg h_xb_nonneg]
              by_cases h_xa_ge_half : x + a ≥ (b - a) / 2
              · exact ⟨a, ⟨by linarith, by linarith⟩, by linarith⟩
              · have h_xb_ge_half : x + b ≥ (b - a) / 2 := by linarith
                exact ⟨b, ⟨by linarith, by linarith⟩, by linarith⟩
            · have h_abs_xa : |x + a| = x + a := by rw [abs_of_nonneg h_xa_nonneg]
              have h_abs_xb : |x + b| = -(x + b) := by rw [abs_of_nonpos (by linarith)]
              have h_xa_ge_half : x + a ≥ (b - a) / 2 := by
                by_contra h_contra
                have h_xa_lt_half : x + a < (b - a) / 2 := by linarith
                have h_xb_neg : x + b < 0 := by linarith
                have h_neg_xb_pos : -(x + b) > 0 := by linarith
                have h_neg_xb_ge_half : -(x + b) > (b - a) / 2 := by linarith
                have h_abs_xa_lt_half : |x + a| < (b - a) / 2 := by
                  rw [abs_of_nonneg h_xa_nonneg]
                  linarith
                have h_abs_xb_gt_half : |x + b| > (b - a) / 2 := by
                  rw [abs_of_nonpos (by linarith)]
                  linarith
                linarith
              exact ⟨a, ⟨by linarith, by linarith⟩, by linarith⟩
          -- Case : $x + a < 0$
          · by_cases h_xb_nonneg : x + b ≥ 0
            · have h_abs_xa : |x + a| = -(x + a) := by rw [abs_of_nonpos (by linarith)]
              have h_abs_xb : |x + b| = x + b := by rw [abs_of_nonneg h_xb_nonneg]
              by_cases h_neg_xa_ge_half : -(x + a) ≥ (b - a) / 2
              · exact ⟨a, ⟨by linarith, by linarith⟩, by linarith⟩
              · have h_neg_xa_lt_half : -(x + a) < (b - a) / 2 := by linarith
                have h_xb_ge_half : x + b ≥ (b - a) / 2 := by
                  have h_xa_gt_neg_half : x + a > -(b - a) / 2 := by linarith
                  have h_xb_eq : x + b = x + a + (b - a) := by ring
                  have h_xb_gt : x + b > -(b - a) / 2 + (b - a) := by linarith
                  have h_expr_half : -(b - a) / 2 + (b - a) = (b - a) / 2 := by
                    field_simp
                    ring
                  linarith
                exact ⟨b, ⟨by linarith, by linarith⟩, by linarith⟩
            · have h_abs_xa : |x + a| = -(x + a) := by rw [abs_of_nonpos (by linarith)]
              have h_abs_xb : |x + b| = -(x + b) := by rw [abs_of_nonpos (by linarith)]
              -- We need to show that $-(x + a) ≥ (b - a)/2 or -(x + b) ≥ (b - a)/2$.
              have h_neg_xa_or_xb : -(x + a) ≥ (b - a) / 2 ∨ -(x + b) ≥ (b - a) / 2 := by
                by_cases h_neg_xa_ge_half : -(x + a) ≥ (b - a) / 2
                · exact Or.inl h_neg_xa_ge_half
                -- If $-(x + a) < (b - a)/2$, then we need to show that $-(x + b) ≥ (b - a)/2$.
                · have h_neg_xb_ge_half : -(x + b) ≥ (b - a) / 2 := by
                    by_contra h_contra
                    have h_neg_xb_lt_half : -(x + b) < (b - a) / 2 := by linarith
                    have h_neg_xa_lt_half : -(x + a) < (b - a) / 2 := by linarith
                    have h_xa_neg : x + a < 0 := by linarith
                    have h_xb_neg : x + b < 0 := by linarith
                    have h_abs_xa_gt_half : |x + a| > (b - a) / 2 := by
                      rw [abs_of_nonpos (by linarith)]
                      linarith
                    have h_abs_xb_gt_half : |x + b| > (b - a) / 2 := by
                      rw [abs_of_nonpos (by linarith)]
                      linarith
                    linarith
                  exact Or.inr h_neg_xb_ge_half
              cases h_neg_xa_or_xb with
              | inl h_neg_xa_ge_half => exact ⟨a, ⟨by linarith, by linarith⟩, by linarith⟩
              | inr h_neg_xb_ge_half => exact ⟨b, ⟨by linarith, by linarith⟩, by linarith⟩
        rcases h_exists_t with ⟨t, ht, h_t_ge_half⟩
        have h_val_ge_half : (b - a) / 2 ≤ |x + t| := by linarith
        have h_val_in_set : |x + t| ∈ {y : ℝ | ∃ t ∈ Icc a b, y = |x + t|} := by
          refine' ⟨t, ht, _⟩
          simp
        -- Prove that the supremum is at least $(b - a) / 2$.
        have h_sup_ge_half : (b - a) / 2 ≤ sSup {y : ℝ | ∃ t ∈ Icc a b, y = |x + t|} := by
          have h_set_bdd_above := bdd_above_abs_x_plus_t a b x hab
          exact le_csSup_of_le h_set_bdd_above h_val_in_set h_val_ge_half
        exact h_sup_ge_half
      exact h_sup_ge_half
    exact h_g_ge_half
  exact ⟨h_exists_x, h_lower_bound⟩