import Mathlib

open Real

theorem inequalities_316974 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hsum : ∑ i, a i = 1) (hsum' : ∑ i, b i = 1) :
    ∑ i, (a i)^2 / (a i + b i) ≥ 1 / 2 := by
  have h1 : ∀ i, 0 < a i + b i := by
    intro i
    have ha' := ha i
    have hb' := hb i
    linarith
  have h2 : ∑ i : Fin n, (a i) ^ 2 / (a i + b i) ≥ (∑ i : Fin n, (a i)) ^ 2 / (∑ i : Fin n, (a i + b i)) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    intro i hi
    specialize h1 i
    linarith
  have h3 : ∑ i : Fin n, (a i + b i) = 2 := by
    calc
      ∑ i : Fin n, (a i + b i) = ∑ i : Fin n, (a i) + ∑ i : Fin n, (b i) := by 
        simp [Finset.sum_add_distrib]
      _ = 1 + 1 := by 
        rw [hsum, hsum']
      _ = (2 : ℝ) := by 
        norm_num
  have h4 : (∑ i : Fin n, (a i)) ^ 2 / (∑ i : Fin n, (a i + b i)) = 1 / 2 := by
    rw [h3]
    rw [hsum]
    all_goals norm_num
    all_goals linarith
  linarith [h2, h4]
  all_goals linarith
  all_goals linarith