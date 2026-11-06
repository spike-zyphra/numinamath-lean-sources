import Mathlib

theorem algebra_4076 (k : ℤ) :
    (∃! x : ℤ, x^2 + k * x + k + 1 = 0 ∧ x^2 + 6 * x + k + 3 = 0) ↔ k = 5 := by
  constructor
  · -- Assume there exists a unique integer root common to both equations, prove k = 5.
    intro h
    rcases h with ⟨x, ⟨h₁, h₂⟩, h₃⟩
    have h4 : (k - 6) * x = 2 := by
      nlinarith
    have h5 : x ∣ 2 := by 
      use k - 6
      all_goals linarith
    have h6 : x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 := by
      have h8 : x ∣ 2 := h5
      have h9 : x ≤ 2 := by
        apply Int.le_of_dvd (by norm_num) h8
      have h10 : x ≥ -2 := by
        have : -x ∣ 2 := by 
          exact Int.neg_dvd.2 h8
        have : -x ≤ 2 := by 
          apply Int.le_of_dvd (by norm_num) this
        omega
      interval_cases x <;> tauto
    rcases h6 with (h7 | h7 | h7 | h7)
    · -- Case x = 1
      rw [h7] at h4 h₁ h₂
      have h8 : k = 8 := by linarith
      rw [h8] at h₁
      norm_num at h₁ 
    · -- Case x = -1
      rw [h7] at h4 h₁ h₂
      have h8 : k = 4 := by
        nlinarith
      rw [h8] at h₁
      norm_num at h₁ 
    · -- Case x = 2
      rw [h7] at h4 h₁ h₂
      have h8 : k = 7 := by
        nlinarith
      rw [h8] at h₁
      norm_num at h₁ 
    · -- Case x = -2
      rw [h7] at h4 h₁ h₂
      have h8 : k = 5 := by
        nlinarith
      linarith 
  · -- Assume k = 5, prove there exists a unique integer root.
    intro h
    rw [h]
    use -2
    constructor 
    · -- Show that -2 is a root of both equations.
      constructor 
      · -- First equation 
        norm_num 
      · -- Second equation 
        norm_num 
    · -- Show that -2 is the unique root.
      intro y hy
      rcases hy with ⟨h₁, h₂⟩
      have h4 : y = -2 := by 
        nlinarith
      linarith