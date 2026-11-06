import Mathlib

theorem number_theory_101902 (a : ℤ) :
    ∃ k : ℤ, 2 * a^2 = 7 * k + 2 ↔ ∃ l : ℤ, a = 7 * l + 1 ∨ a = 7 * l - 1 := by
  use (2 * a^2 - 2) / 7
  constructor
  · -- Forward direction: assuming 2a^2 = 7k + 2, proving a = 7l ± 1
    intro h
    have h2 : (a ^ 2) % 7 = 1 := by
      have h3 : (2 * a^2) % 7 = 2 := by 
        omega
      omega
    have h3 : a % 7 = 1 ∨ a % 7 = 6 := by
      have h4 : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
        omega
      rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4)
      · -- a % 7 = 0 
        have h5 : (a ^ 2) % 7 = 0 := by 
          simp [pow_two, Int.mul_emod, h4]
        rw [h5] at h2
        all_goals omega
      · -- a % 7 = 1 
        exact Or.inl h4
      · -- a % 7 = 2
        have h5 : (a ^ 2) % 7 = 4 := by 
          simp [pow_two, Int.mul_emod, h4]
        rw [h5] at h2
        all_goals omega
      · -- a % 7 = 3
        have h5 : (a ^ 2) % 7 = 2 := by 
          simp [pow_two, Int.mul_emod, h4]
        rw [h5] at h2
        all_goals omega
      · -- a % 7 = 4
        have h5 : (a ^ 2) % 7 = 2 := by 
          simp [pow_two, Int.mul_emod, h4]
        rw [h5] at h2
        all_goals omega
      · -- a % 7 = 5
        have h5 : (a ^ 2) % 7 = 4 := by 
          simp [pow_two, Int.mul_emod, h4]
        rw [h5] at h2
        all_goals omega
      · -- a % 7 = 6
        exact Or.inr h4
    rcases h3 with (h3 | h3)
    · -- a ≡ 1 (mod 7)
      use (a - 1) / 7
      left
      omega
    · -- a ≡ 6 (mod 7)
      use (a + 1) / 7
      right
      omega
  · -- Backward direction: assuming a = 7l ± 1, proving 2a^2 = 7k + 2
    rintro ⟨l, h⟩
    rcases h with (h | h)
    · -- a = 7l + 1
      rw [h]
      -- algebra to compute 2*(7l+1)^2 = 2*(49l^2 + 14l + 1) = 98l^2 + 28l + 2
      -- Then (2*(7l+1)^2 - 2)/7 = (98l^2 + 28l)/7 = 14l^2 + 4l
      ring_nf
      <;> omega
    · -- a = 7l - 1
      rw [h]
      -- similar algebra as above
      ring_nf
      <;> omega