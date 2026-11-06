import Mathlib

open Real

theorem inequalities_38707 {n : ℕ} (hn : 1 < n) (α : ℝ) (hα : 0 < α ∧ α < 2)
    (a c : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hc : ∀ i, 0 < c i)
    (f : ℝ → ℝ) (hf : ∀ y, 0 < y → f y = ((∑ i, if a i ≤ y then c i * a i ^ 2 else 0) ^ (1 / 2)) +
      ((∑ i, if a i > y then c i * a i ^ α else 0) ^ (1 / α))) :
    ∀ x, 0 < x → ∃ y, 0 < y ∧ x ≥ f y → f x ≤ 8 ^ (1 / α) * x := by
  intro x hx
  use x
  intro h
  have h2 : 0 < x := h.1
  have h1 : x ≥ f x := h.2
  have hx2 : f x ≤ x := by linarith
  have h3 : (8 : ℝ) ^ (1 / α) ≥ (1 : ℝ) := by
    have h4 : α > 0 := hα.1
    have h5 : α < 2 := hα.2
    have h6 : (1 / α : ℝ) > 0 := by
      positivity
    have h7 : (8 : ℝ) ≥ (1 : ℝ) := by
      norm_num
    have h8 : (8 : ℝ) ^ (1 / α) ≥ (1 : ℝ) ^ (1 / α) := by
      apply Real.rpow_le_rpow
      all_goals
        linarith
    have h9 : (1 : ℝ) ^ (1 / α) = 1 := by
      simp
    linarith [h8, h9]
  have h8 : x ≤ (8 : ℝ) ^ (1 / α) * x := by
    have h9 : (8 : ℝ) ^ (1 / α) ≥ (1 : ℝ) := h3
    nlinarith
  linarith [hx2, h8]