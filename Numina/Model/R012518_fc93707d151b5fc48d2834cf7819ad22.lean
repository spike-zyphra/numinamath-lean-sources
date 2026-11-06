import Mathlib

open Real

theorem inequalities_304038 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (h : ∑ i, a i = ∑ i, b i) :
    ∑ i, (a i)^2 / (a i + b i) ≥ 1 / 2 * ∑ i, a i := by

  have h1 : ∀ i, 0 < a i + b i := by
    intro i
    have ha1 : 0 < a i := ha i
    have hb1 : 0 < b i := hb i
    linarith
  
  have h2 : ∑ i, (a i : ℝ) ^ 2 / (a i + b i) ≥ (∑ i, (a i : ℝ)) ^ 2 / (∑ i, (a i + b i : ℝ)) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    intro i hi
    have h4 : i < (n : ℕ) := by 
      simp at hi ⊢
      all_goals linarith
    have h5 : 0 < a ⟨i, by linarith⟩ := by 
      apply ha
    have h6 : 0 < b ⟨i, by linarith⟩ := by 
      apply hb
    have : 0 < a ⟨i, by linarith⟩ + b ⟨i, by linarith⟩ := by
      linarith
    have h7 : (a ⟨i, by linarith⟩ : ℝ) + (b ⟨i, by linarith⟩ : ℝ) > 0 := by 
      linarith
    exact h7

  have h3 : ∑ i, (a i + b i : ℝ) = 2 * (∑ i, (a i : ℝ)) := by
    calc
      ∑ i, (a i + b i : ℝ) = ∑ i, (a i : ℝ) + ∑ i, (b i : ℝ) := by 
        simp [Finset.sum_add_distrib]
      _ = (∑ i, (a i : ℝ)) + (∑ i, (a i : ℝ)) := by
        have h2 : ∑ i, (b i : ℝ) = ∑ i, (a i : ℝ) := by 
          linarith [h]
        rw [h2]
      _ = 2 * (∑ i, (a i : ℝ)) := by
        ring

  have h4 : (∑ i, (a i : ℝ)) ^ 2 / (∑ i, (a i + b i : ℝ)) = 1 / 2 * (∑ i, (a i : ℝ)) := by
    rw [h3]
    have h5 : (∑ i, (a i : ℝ)) > 0 := by
      have ha1 : ∀ i, 0 < a i := by
        intro i
        exact ha i
      apply Finset.sum_pos
      · intro i hi
        exact ha1 i
      · use ⟨0, by linarith [hn]⟩
        simp [hn]
    field_simp [h5]
    <;> nlinarith
  
  linarith [h2, h4]