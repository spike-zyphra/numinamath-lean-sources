import Mathlib

open Real

theorem inequalities_323389 (n : ℕ) (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (h : ∑ i, a i = ∑ i, b i) :
    ∑ i, (a i)^2 / (a i + b i) ≥ 1 / 2 * ∑ i, a i := by 
  have h1 : ∀ i, 0 < a i + b i := by
    intro i
    have ha' := ha i
    have hb' := hb i
    linarith

  have h2 : ∑ i, (a i) ^ 2 / (a i + b i) ≥ (∑ i, (a i)) ^ 2 / (∑ i, (a i + b i)) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    all_goals
      intro i hi
      have h1' := h1 i
      all_goals
        simp at *
        <;> try linarith

  have h3 : ∑ i : Fin n, (a i + b i) = 2 * (∑ i, (a i)) := by
    calc 
      ∑ i, (a i + b i) = ∑ i, (a i) + ∑ i, (b i) := by 
        simp [Finset.sum_add_distrib]
        <;> try norm_num
        all_goals try linarith
      _ = (∑ i, (a i)) + (∑ i, (a i)) := by 
        rw [show ∑ i, b i = ∑ i, a i by rw [h]]
        all_goals try norm_num
        all_goals try linarith
      _ = 2 * (∑ i, (a i)) := by 
        ring

  have h4 : (∑ i, (a i)) ^ 2 / (∑ i, (a i + b i)) ≥ 1 / 2 * (∑ i, (a i)) := by
    rw [h3]
    have h0 : 0 < 2 * (∑ i : Fin n, a i) := by
      have h01 : ∀ i : Fin n, a i > 0 := by
        intro i
        apply ha
      have h02 : ∑ i : Fin n, a i > 0 := by
        apply Finset.sum_pos
        · intro i hi
          exact h01 i
        · use ⟨0, by linarith⟩
          simp [ha]
          all_goals try linarith
          all_goals try positivity 
      nlinarith 
    apply (le_div_iff₀ (by positivity)).mpr
    all_goals
      nlinarith 
      all_goals try positivity

  linarith [h2, h4]