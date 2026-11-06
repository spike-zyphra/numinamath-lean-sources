import Mathlib

theorem algebra_308824 (a : ℕ → ℤ) (h₀ : a 1 = 1) (h₁ : ∀ n, a n + a (n + 1) = -n ^ 2) :
    a 15 = -104 := by
  have h2 := h₁ 0
  have h3 : a 0 = -1 := by
    simp [h₀] at h2
    omega
  have h4 := h₁ 1
  have h5 : a 2 = -2 := by
    simp [h₀] at h4
    omega
  have h6 := h₁ 2
  have h7 : a 3 = -2 := by
    simp [h5] at h6
    omega
  have h8 := h₁ 3
  have h9 : a 4 = -7 := by
    simp [h7] at h8
    omega
  have h10 := h₁ 4
  have h11 : a 5 = -9 := by
    simp [h9] at h10
    omega
  have h12 := h₁ 5
  have h13 : a 6 = -16 := by
    simp [h11] at h12
    omega
  have h14 := h₁ 6
  have h15 : a 7 = -20 := by
    simp [h13] at h14
    omega
  have h16 := h₁ 7
  have h17 : a 8 = -29 := by
    simp [h15] at h16
    omega
  have h18 := h₁ 8
  have h19 : a 9 = -35 := by
    simp [h17] at h18
    omega
  have h20 := h₁ 9
  have h21 : a 10 = -46 := by
    simp [h19] at h20
    omega
  have h22 := h₁ 10
  have h23 : a 11 = -54 := by
    simp [h21] at h22
    omega
  have h24 := h₁ 11
  have h25 : a 12 = -67 := by
    simp [h23] at h24
    omega
  have h26 := h₁ 12
  have h27 : a 13 = -77 := by
    simp [h25] at h26
    omega
  have h28 := h₁ 13
  have h29 : a 14 = -92 := by
    simp [h27] at h28
    omega
  have h30 := h₁ 14
  have h31 : a 15 = -104 := by
    simp [h29] at h30
    omega
  exact h31