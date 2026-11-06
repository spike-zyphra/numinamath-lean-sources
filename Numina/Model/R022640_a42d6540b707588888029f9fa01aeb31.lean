import Mathlib

theorem algebra_607467 {x : Fin 5 → ℝ} (h : ∀ i j, i + 1 = j ∨ j + 1 = i → |x j - x i| = (i.1 + 1) * |x (i.1 + 1) - x j| ∧ |x j - x i| ≠ 0) : ∀ i j, x i = x j := by

  have h1 := h ⟨0, by omega⟩ ⟨1, by omega⟩ (Or.inl rfl)
  simp [Fin.ext_iff] at h1 ⊢
  all_goals
  norm_num [abs_nonneg] at h1 ⊢
  all_goals
    tauto