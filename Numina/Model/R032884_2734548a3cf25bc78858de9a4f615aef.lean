import Mathlib

theorem algebra_235338 (A B : Set ℕ) (hA : A = {1, 2, x, 5, 9}) (hB : B = {2, y, 3})
    (hB1 : B ⊆ A) (hB2 : B.encard = 3) :
    x = 3 ∧ y = 1 ∨ x = 3 ∧ y = 5 ∨ x = 3 ∧ y = 9 := by 

  have h1 : 3 ∈ B := by
    rw [hB]
    simp
  have h2 : 3 ∈ A := hB1 h1
  rw [hA] at h2
  have hx : x = 3 := by
    simp at h2
    omega

  have h3 : y ∈ B := by
    rw [hB]
    simp
  have h4 : y ∈ A := hB1 h3
  rw [hA] at h4
  rw [hx] at h4

  have h5 : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 5 ∨ y = 9 := by
    simp at h4 ⊢
    omega

  have h6 : y ≠ 2 := by
    by_contra h_eq
    have h11 : y = 2 := by omega
    have h7 : B = {2, 2, 3} := by
      rw [hB]
      simp [h11]
    



    have h9 : (B : Set ℕ).encard = 2 := by 
      rw [h7]
      rw [Set.encard]
      simp [Set.ncard]
    rw [h9] at hB2 
    norm_num at hB2 ⊢ 

  have h8 : y ≠ 3 := by
    by_contra h_eq
    have h11 : y = 3 := by omega
    have h7 : B = {2, 3, 3} := by
      rw [hB]
      simp [h11]
    have h9 : (B : Set ℕ).encard = 2 := by 
      rw [h7]
      rw [Set.encard]
      simp [Set.ncard]
    rw [h9] at hB2 
    norm_num at hB2 ⊢ 

  have hy1 : y = 1 ∨ y = 5 ∨ y = 9 := by
    have h9 : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 5 ∨ y = 9 := by
      simp at h4 ⊢
      omega
    have h6 : y ≠ 2 := h6
    have h8 : y ≠ 3 := h8

    have h5 : y = 1 ∨ y = 5 ∨ y = 9 := by 
      rcases h9 with (ha | ha | ha | ha | ha)
      · tauto
      · exfalso; apply h6; linarith
      · exfalso; apply h8; linarith
      · tauto
      · tauto
    exact h5

  have hx1 : x = 3 := hx

  rcases hy1 with (r | r | r)
  · left
    exact ⟨by omega, by omega⟩
  · right
    left
    exact ⟨by omega, by omega⟩
  · right
    right
    exact ⟨by omega, by omega⟩