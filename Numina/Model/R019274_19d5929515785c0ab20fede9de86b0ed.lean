import Mathlib.Tactic

open Real

theorem inequalities_111354 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hsum : ∑ k, a k = ∑ k, b k) :
    ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, a i) / 2 := by
  have h1 : ∀ i : Fin n, 0 < a i + b i := by
    intro i
    have ha_i : 0 < a i := ha i
    have hb_i : 0 < b i := hb i
    linarith
  have h2 : ∑ i, (a i) ^ 2 / (a i + b i) ≥ (∑ i, a i) ^ 2 / (∑ i, (a i + b i)) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    intro i hi
    have h1' : 0 < a i + b i := h1 i
    exact h1'
  have h3 : ∑ i, (a i + b i) = 2 * (∑ i, a i) := by
    calc
      ∑ i, (a i + b i) = ∑ i, (a i) + ∑ i, (b i) := by
        simp [Finset.sum_add_distrib]
      _ = (∑ i, a i) + (∑ i, a i) := by
        have h4 : ∑ i, (b i) = ∑ i, (a i) := by
          linarith [hsum]
        rw [h4]
      _ = 2 * (∑ i, a i) := by
        ring_nf
  have h4 : (∑ i, a i) ^ 2 / (∑ i, (a i + b i)) = (∑ i, a i) / 2 := by
    rw [h3]
    have h5 : (∑ i, a i) ≥ 0 := by
      apply Finset.sum_nonneg
      intro i hi
      have ha_i_pos : 0 < a i := ha i
      linarith
    have h6 : (∑ i, a i) ^ 2 / (2 * (∑ i, a i)) = (∑ i, a i) / 2 := by
      have h7 : 2 * (∑ i, a i) ≠ 0 := by
        nlinarith [h5, show (∑ i, a i) > 0 by
          apply Finset.sum_pos
          intro i hi
          have ha_i_pos : 0 < a i := ha i
          linarith
          use ⟨0, by linarith [hn]⟩
          simp [ha ⟨0, by linarith [hn]⟩]
          all_goals linarith [hn]
        ]
      field_simp [h7]
      <;> ring_nf
    nlinarith [h6]
  nlinarith [h2, h4]