import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_598957 {n : ℕ} (hn : 0 < n) :
  IsLeast {x | ∃ a b : Fin n → ℝ,
    (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧
    (∑ i, a i) = 1 ∧ (∑ i, b i) = 1 ∧
    x = ∑ i, (a i)^2 / (a i + b i)} (1 / 2) := by
  constructor
  · -- Show that 1/2 is in the set
    use (fun _ => (1 : ℝ) / n), (fun _ => (1 : ℝ) / n)
    constructor
    · -- Show all a_i > 0
      intro i
      positivity
    constructor
    · -- Show all b_i > 0
      intro i
      positivity
    constructor
    · -- Show sum a_i = 1
      simp [Finset.sum_const, Finset.card_univ, hn]
      <;> field_simp
      <;> ring
    constructor
    · -- Show sum b_i = 1
      simp [Finset.sum_const, Finset.card_univ, hn]
      <;> field_simp
      <;> ring
    · -- Show x = 1/2
      simp [Finset.sum_congr, Finset.sum_const, Finset.card_univ, hn]
      <;> field_simp
      <;> ring
  · -- Now prove minimality
    intro x hx
    rcases hx with ⟨a, b, ha_pos, hb_pos, ha1, hb1, hx⟩
    have h1 : ∑ i, (a i) = 1 := by
      simpa using ha1
    have h2 : ∑ i, (b i) = 1 := by
      simpa using hb1
    have h3 : ∑ i, (a i)^2 / (a i + b i) ≥ 1 / 2 := by
      have h4 : ∀ i, 0 < a i + b i := by
        intro i
        have ha_i : 0 < a i := by
          exact ha_pos i
        have hb_i : 0 < b i := by
          exact hb_pos i
        linarith
      have h5 : ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, (a i)) ^ 2 / (∑ i, (a i + b i)) := by
        apply Finset.sq_sum_div_le_sum_sq_div
        intro i _
        exact h4 i
      have h6 : (∑ i, (a i + b i)) = 2 := by
        calc
          (∑ i, (a i + b i)) = (∑ i, (a i)) + (∑ i, (b i)) := by
            simp [Finset.sum_add_distrib]
          _ = (1 : ℝ) + (1 : ℝ) := by
            rw [h1, h2]
          _ = (2 : ℝ) := by
            norm_num
      have h7 : (∑ i, (a i)) ^ 2 / (∑ i, (a i + b i)) = (1 / 2 : ℝ) := by
        rw [h6]
        rw [h1]
        all_goals norm_num
      linarith [h5, h7]
    rw [hx]
    linarith [h3]