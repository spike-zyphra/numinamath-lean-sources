import Mathlib

def A : Set ℝ := {1, 2, 1 / 2}
def B : Set ℝ := {y | ∃ x ∈ A, y = x ^ 2}

theorem algebra_12623 : A ∩ B = {1} := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume y ∈ A ∩ B, prove y = 1
    intro h
    rcases h with ⟨hA, hB⟩
    have hx1 : y = 1 ∨ y = 2 ∨ y = (1 / 2 : ℝ) := by
      have h2 : y ∈ (A : Set ℝ) := hA
      norm_num [A] at h2 ⊢
      tauto
    rcases hx1 with (rfl | rfl | rfl)
    · -- Case y = 1
      norm_num at *
    · -- Case y = 2
      exfalso
      norm_num [B, A] at hB
    · -- Case y = 1 / 2
      exfalso
      norm_num [B, A] at hB
  · -- Assume y = 1, prove y ∈ A ∩ B
    intro h_eq
    rw [h_eq]
    constructor
    · -- Show 1 ∈ A
      norm_num [A]
    · -- Show 1 ∈ B
      norm_num [B, A]