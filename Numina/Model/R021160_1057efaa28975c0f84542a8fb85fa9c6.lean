import Mathlib

open Real

theorem inequalities_322307 (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i ∧ x i ≤ 1) :
    ∑ i, x i / (1 + (n - 1) * x i) ≤ 1 := by
  have h1 : ∀ i, 0 < x i := by 
    intro i
    exact (hx i).left
  have h2 : ∀ i, x i ≤ 1 := by 
    intro i
    exact (hx i).right
  have h3 : ∀ i, x i / (1 + (n - 1) * x i) ≤ 1 / (n : ℝ) := by
    intro i
    have h4 : x i ≤ 1 := h2 i
    have h5 : (1 : ℝ) + (n - 1) * x i > 0 := by 
      have h6 : x i > 0 := h1 i
      have h7 : (n : ℝ) ≥ 1 := by exact_mod_cast hn
      have h8 : (n - 1 : ℝ) ≥ 0 := by nlinarith
      nlinarith
    have h6 : (n : ℝ) ≥ 1 := by exact_mod_cast hn
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  have h8 : ∑ i : Fin n, x i / (1 + (n - 1) * x i) ≤ ∑ i : Fin n, (1 / (n : ℝ)) := by 
    apply Finset.sum_le_sum
    intro i hi
    specialize h3 i
    linarith
  have h9 : ∑ i : Fin n, (1 / (n : ℝ)) = 1 := by 
    simp
    all_goals 
      field_simp at *
      all_goals 
        ring_nf 
        all_goals 
          norm_num 
          all_goals 
            linarith 
  linarith [h8, h9]