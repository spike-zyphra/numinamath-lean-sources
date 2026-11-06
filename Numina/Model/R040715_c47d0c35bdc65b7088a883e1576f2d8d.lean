import Mathlib


open Set


lemma lemma_1 (A : Set ℝ) (hA : A = {2, 0, 1, 3}) :
    {x : ℝ | -x ∈ A ∧ ¬(2 - x ^ 2) ∈ A} = {-2, -3} := by
  ext x
  simp [hA]
  constructor
  ·
    rintro ⟨h1, h2⟩
    have h10 : (-x = (2 : ℝ) ∨ -x = (0 : ℝ) ∨ -x = (1 : ℝ) ∨ -x = (3 : ℝ)) := by
      simpa using h1
    rcases h10 with (h | h | h | h)
    ·
      have hx1 : x = (-2 : ℝ) := by linarith
      rw [hx1]
      norm_num at *
    ·
      have hx1 : x = (0 : ℝ) := by linarith
      rw [hx1] at h2
      norm_num at h2
    ·
      have hx1 : x = (-1 : ℝ) := by linarith
      rw [hx1] at h2
      norm_num at h2
    ·
      have hx1 : x = (-3 : ℝ) := by linarith
      rw [hx1]
      norm_num at *
  ·
    rintro (rfl | rfl)
    ·
      constructor
      ·
        norm_num
      ·
        norm_num
    ·
      constructor
      ·
        norm_num
      ·
        norm_num


theorem algebra_130953 {A B : Finset ℝ} (hA : A = {2, 0, 1, 3}) (hB : B = {x | -x ∈ A ∧ ¬(2 - x^2 ∈ A)}) :
    ∑ x ∈ B, x = -5 := by
  have h20 : (B : Set ℝ) = {-2, -3} := by
    have h100 : (B : Set ℝ) = {x : ℝ | -x ∈ (A : Set ℝ) ∧ ¬(2 - x ^ 2 ∈ (A : Set ℝ))} := by
      rw [hB]
      all_goals
        aesop
    rw [h100]
    rw [lemma_1 (A : Set ℝ) (by
      simp [hA]
    )]

  have h30 : B = ({-2, -3} : Finset ℝ) := by
    have h300 : (↑B : Set ℝ) = {-2, -3} := h20
    have h400 : B = ({-2, -3} : Finset ℝ) := by
      have h500 : (↑B : Set ℝ) = (↑({-2, -3} : Finset ℝ) : Set ℝ) := by
        rw [h300]
        all_goals
          norm_num
      have h501 : B = ({-2, -3} : Finset ℝ) := by
        simp at h500 ⊢
        all_goals
          try { tauto }
      assumption
    assumption

  rw [h30]
  norm_num [Finset.sum_insert, Finset.sum_singleton]