import Mathlib

open Real

theorem inequalities_323785 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, a i = ∑ i, b i) :
    ∑ i, (a i ^ 2 / (a i + b i)) ≥ 1 / 2 * ∑ i, a i := by
  have h1 : ∀ i, 0 < a i + b i := by
    intro i 
    have ha' : 0 < a i := ha i 
    have hb' : 0 < b i := hb i 
    linarith 
  have h2 : ∑ i, (a i ^ 2 / (a i + b i)) ≥ (∑ i, a i) ^ 2 / (∑ i, (a i + b i)) := by 
    apply Finset.sq_sum_div_le_sum_sq_div
    intro i hi 
    have ha' : 0 < a i := ha i 
    have hb' : 0 < b i := hb i 
    positivity 
  have h3 : ∑ i, (a i + b i) = 2 * (∑ i, a i) := by
    calc
      ∑ i, (a i + b i) = ∑ i, (a i) + ∑ i, (b i) := by 
        simp [Finset.sum_add_distrib] 
      _ = (∑ i, a i) + (∑ i, a i) := by 
        rw [show ∑ i, b i = ∑ i, a i by rw [hsum]] 
      _ = 2 * (∑ i, a i) := by 
        ring
  rw [h3] at h2
  have h4 : (∑ i, a i) ^ 2 / (2 * (∑ i, a i)) = 1 / 2 * (∑ i, a i) := by
    have h5 : ∑ i, a i > 0 := by 
      have h6 : ∀ i, a i > 0 := by 
        intro i 
        specialize ha i 
        linarith 
      have h7 : ∑ i, a i > 0 := by 
        apply Finset.sum_pos 
        intro i hi 
        specialize ha i 
        linarith 
        use ⟨0, by linarith [hn]⟩ 
        simp 
        all_goals linarith
      positivity 
    have h5_pos : 2 * (∑ i, a i) ≠ 0 := by 
      nlinarith 
    field_simp 
    <;> nlinarith [h5]
  linarith [h2, h4]