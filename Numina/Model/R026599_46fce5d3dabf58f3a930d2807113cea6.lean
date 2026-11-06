import Mathlib

theorem number_theory_285279 (j d a h : ℤ)
    (h₀ : Odd (d + 3 * j))
    (h₁ : Odd (5 * (a - h)))
    (h₂ : Even (d * h + 17)) :
    Odd d ∧ Odd h ∧ Even j ∧ Even a := by 
  have h1 : (d + 3 * j) % 2 = 1 := by 
    obtain ⟨k, hk⟩ := h₀
    omega
  have h5 : (d % 2 + (3 * j) % 2) % 2 = 1 := by 
    omega
  have h6 : (3 * j) % 2 = j % 2 := by 
    omega
  rw [h6] at h5
  have h7 : d % 2 ≠ j % 2 := by
    omega
  have h8 : (5 * (a - h)) % 2 = 1 := by
    obtain ⟨k, hk⟩ := h₁
    omega
  have h10 : (a - h) % 2 = 1 := by 
    have h11 : (5 * (a - h)) % 2 = (5 % 2 * ((a - h) % 2)) % 2 := by 
      simp [Int.mul_emod]
    rw [h11] at h8
    have h9 : (5 : ℤ) % 2 = 1 := by norm_num
    rw [h9] at h8
    omega
  have h12 : a % 2 ≠ h % 2 := by
    omega
  have h13 : (d * h + 17) % 2 = 0 := by 
    obtain ⟨k, hk⟩ := h₂
    omega
  have h14 : (d * h) % 2 = 1 := by 
    omega
  have h15 : d % 2 = 1 := by
    have h16 : (d * h) % 2 = (d % 2 * (h % 2)) % 2 := by 
      simp [Int.mul_emod]
    rw [h16] at h14
    have : d % 2 = 0 ∨ d % 2 = 1 := by omega
    rcases this with (h | h) <;> 
      try { 
        simp [h] at h14 <;> omega 
      }
  have h18 : h % 2 = 1 := by 
    have h16 : (d * h) % 2 = (d % 2 * (h % 2)) % 2 := by 
      simp [Int.mul_emod]
    rw [h16] at h14
    rw [h15] at h14
    omega
  have h17 : j % 2 = 0 := by 
    omega
  have h19 : a % 2 = 0 := by 
    omega
  constructor
  · -- Show that d is odd.
    exact ⟨d / 2, by omega⟩
  constructor
  · -- Show that h is odd.
    exact ⟨h / 2, by omega⟩
  constructor
  · -- Show that j is even.
    exact ⟨j / 2, by omega⟩
  · -- Show that a is even.
    exact ⟨a / 2, by omega⟩