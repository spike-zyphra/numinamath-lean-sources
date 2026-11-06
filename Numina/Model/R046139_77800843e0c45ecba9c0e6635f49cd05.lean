import Mathlib

open Real

theorem inequalities_231266 (n : ℕ) (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (h : ∑ i, a i = ∑ i, b i) :
    ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, a i) / 2 := by

  have h1 : ∀ i, 0 < a i + b i := by
    intro i
    have ha_i : 0 < a i := ha i
    have hb_i : 0 < b i := hb i
    linarith

  have h2 : ∑ i, (a i) ^ 2 / (a i + b i) ≥ (∑ i, (a i)) ^ 2 / (∑ i, (a i + b i)) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    all_goals
      intro i hi
      have h1_i : 0 < a i + b i := h1 i
      positivity

  have h3 : ∑ i, (a i + b i) = 2 * (∑ i, (a i)) := by
    calc
      ∑ i, (a i + b i) = ∑ i, (a i) + ∑ i, (b i) := by simp [Finset.sum_add_distrib]
      _ = ∑ i, (a i) + ∑ i, (a i) := by rw [show ∑ i, (b i) = ∑ i, (a i) by linarith [h]]
      _ = 2 * (∑ i, (a i)) := by ring

  have h4 : (∑ i, (a i)) ^ 2 / (∑ i, (a i + b i)) = (∑ i, (a i)) / 2 := by
    rw [h3]
    have h5 : ∑ i, (a i) > 0 := by
      have ha1 : ∀ i, 0 < a i := ha
      have : ∑ i, (a i) > 0 := by
        apply Finset.sum_pos
        intro i hi
        exact ha1 i
        use ⟨0, by linarith⟩
        simp [ha1]
      assumption
    field_simp
    <;> nlinarith [h5]

  linarith [h2, h4]