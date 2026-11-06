import Mathlib

open Real

theorem inequalities_186656 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (h : ∑ i, a i = ∑ i, b i) :
    ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, a i) / 2 := by

  have h1 : ∀ i : Fin n, 0 < a i + b i := by
    intro i
    have ha1 := ha i
    have hb1 := hb i
    linarith

  have h2 : ∑ i : Fin n, (a i + b i) = 2 * (∑ i : Fin n, a i) := by
    calc
      ∑ i : Fin n, (a i + b i) = ∑ i : Fin n, a i + ∑ i : Fin n, b i := by
        simp [Finset.sum_add_distrib]
      _ = ∑ i : Fin n, a i + ∑ i : Fin n, a i := by
        rw [show ∑ i : Fin n, b i = ∑ i : Fin n, a i by linarith [h]]
      _ = 2 * (∑ i : Fin n, a i) := by
        ring

  have h3 : ∑ i, (a i) ^ 2 / (a i + b i) ≥ (∑ i, (a i)) ^ 2 / (∑ i, (a i + b i)) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    all_goals
      intro i hi
      have h1_i := h1 i
      positivity

  have h4 : (∑ i, (a i + b i)) = 2 * (∑ i, (a i)) := h2

  have h5 : (∑ i, (a i)) ^ 2 / (∑ i, (a i + b i)) = (∑ i, (a i)) / 2 := by
    rw [h4]
    have h6 : (∑ i, (a i)) > 0 := by
      have h9 : ∀ i, 0 < a i := ha
      have h10 : ∑ i, (a i) > 0 := by
        apply Finset.sum_pos
        · intro i hi
          specialize h9 i
          linarith
        · use ⟨0, hn⟩
          simp
      linarith
    field_simp [h6]
    <;> nlinarith

  linarith [h3, h5]