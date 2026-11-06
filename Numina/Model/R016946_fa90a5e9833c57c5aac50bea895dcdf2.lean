import Mathlib

theorem algebra_272253 {a b : ℝ} (A B : Set ℝ)
    (hA : A = {1, b, a + b}) (hB : B = {a - b, a * b})
    (hAB : A ∩ B = {-1, 0}) :
    a = -1 ∧ b = 0 := by

  have h1 : -1 ∈ A ∩ B := by
    rw [hAB]
    simp

  have h2 : (0 : ℝ) ∈ A ∩ B := by
    rw [hAB]
    simp

  have h3 : -1 ∈ A := by
    have h1' : -1 ∈ A ∩ B := h1
    simp at h1' ⊢
    tauto

  have h4 : -1 ∈ B := by
    have h1' : -1 ∈ A ∩ B := h1
    simp at h1' ⊢
    tauto

  have h5 : (0 : ℝ) ∈ A := by
    have h2' : (0 : ℝ) ∈ A ∩ B := h2
    simp at h2' ⊢
    tauto

  have h6 : (0 : ℝ) ∈ B := by
    have h2' : (0 : ℝ) ∈ A ∩ B := h2
    simp at h2' ⊢
    tauto

  have h7 : -1 = (1 : ℝ) ∨ -1 = b ∨ -1 = a + b := by
    rw [hA] at h3
    simp at h3 ⊢
    tauto

  have h8 : (0 : ℝ) = (1 : ℝ) ∨ (0 : ℝ) = b ∨ (0 : ℝ) = a + b := by
    rw [hA] at h5
    simp at h5 ⊢
    tauto

  have h9 : -1 = a - b ∨ -1 = a * b := by
    rw [hB] at h4
    simp at h4 ⊢
    tauto

  have h10 : (0 : ℝ) = a - b ∨ (0 : ℝ) = a * b := by
    rw [hB] at h6
    simp at h6 ⊢
    tauto

  have h12 : -1 = b ∨ -1 = a + b := by
    rcases h7 with (h | h | h)
    · exfalso
      norm_num at h
    · tauto
    · tauto

  have h13 : (0 : ℝ) = b ∨ (0 : ℝ) = a + b := by
    rcases h8 with (h | h | h)
    · exfalso
      norm_num at h
    · tauto
    · tauto

  rcases h10 with (h15 | h15)
  · -- case $0 = a - b$
    have h16 : a = b := by
      nlinarith
    rw [show b = a by linarith [h16]] at h9
    rcases h9 with (h14 | h14)
    · 
      exfalso
      nlinarith
    · 
      have h17 : a ^ 2 ≥ 0 := by
        apply sq_nonneg
      nlinarith [sq_nonneg a]

  · -- case $0 = a * b$
    have h18 : a * b = 0 := by
      linarith
    have h19 : a = 0 ∨ b = 0 := by
      cases (mul_eq_zero.mp h18) with
      | inl h => 
        left; linarith
      | inr h => 
        right; linarith

    rcases h19 with (ha | hb)
    · 
      have h20 : a = 0 := ha
      rw [h20] at h9
      rcases h9 with (h21 | h22)
      · 
        have h23 : b = 1 := by
          nlinarith
        rw [show b = 1 by linarith [h23], show a = 0 by linarith [h20]] at h13
        norm_num at h13
      · 
        exfalso
        nlinarith

    · 
      have h20 : b = 0 := hb
      rw [h20] at h9
      rcases h9 with (h21 | h22)
      · 
        have h23 : a = -1 := by
          nlinarith
        constructor
        · linarith
        · linarith
      · 
        exfalso
        nlinarith