import Mathlib

open Real

theorem inequalities_302604 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (h : ∑ i, a i = ∑ i, b i) :
    ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, a i) / 2 := by
  have h6 : (∑ i : Fin n, (a i : ℝ) ) > 0 := by
    have h7 : ∀ i : Fin n, a i > 0 := ha
    have h8 : (∑ i : Fin n, (a i : ℝ) ) > 0 := by
      apply Finset.sum_pos
      · -- Show that each term in the sum is positive
        intro i hi
        have h9 : (a i : ℝ) > 0 := h7 i
        simpa using h9
      · -- Show that the set is non-empty
        use ⟨0, by linarith⟩
        simp
    linarith
  have h7 : ∑ i : Fin n, (a i : ℝ) ^ 2 / (a i + b i) ≥ (∑ i : Fin n, (a i : ℝ) ) ^ 2 / (∑ i : Fin n, (a i + b i : ℝ) ) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    all_goals
    intro i hi
    have h1 : 0 < (a i + b i : ℝ) := by
      have ha_i : 0 < a i := ha i
      have hb_i : 0 < b i := hb i
      linarith
    positivity
  have h8 : (∑ i : Fin n, (a i + b i : ℝ) ) = 2 * (∑ i : Fin n, (a i : ℝ) ) := by
    calc
      (∑ i : Fin n, (a i + b i : ℝ) ) = (∑ i : Fin n, (a i : ℝ) ) + (∑ i : Fin n, (b i : ℝ) ) := by
        simp [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, (a i : ℝ) ) + (∑ i : Fin n, (a i : ℝ) ) := by
        have h1 : (∑ i : Fin n, (b i : ℝ) ) = (∑ i : Fin n, (a i : ℝ) ) := by
          linarith [h]
        rw [h1]
      _ = 2 * (∑ i : Fin n, (a i : ℝ) ) := by
        ring
  have h9 : ( (∑ i : Fin n, (a i : ℝ) ) ^ 2 / (∑ i : Fin n, (a i + b i : ℝ) ) ) = ( (∑ i : Fin n, (a i : ℝ) ) / 2 ) := by
    rw [h8]
    have h10 : (∑ i : Fin n, (a i : ℝ) ) ≠ 0 := by
      linarith [h6]
    field_simp [h10]
    <;> nlinarith
  linarith [h7, h9]