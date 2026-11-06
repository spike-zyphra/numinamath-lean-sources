import Mathlib

theorem algebra_257185 (x : ℤ) : 6 ∣ x^2 + 5 * x - 12 ↔ ∃ t, x = 3 * t ∨ x = 3 * t + 1 := by
  constructor
  · -- Assume 6 ∣ x^2 + 5 * x - 12, prove ∃ t, x = 3 * t ∨ x = 3 * t + 1
    rintro h
    have h1 : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1)
    · -- x % 6 = 0
      have h2 : x % 6 = 0 := h1
      have h3 : x % 3 = 0 := by 
        omega
      refine ⟨x / 3, Or.inl ?_⟩
      omega
    · -- x % 6 = 1
      have h2 : x % 6 = 1 := h1
      have h3 : x % 3 = 1 := by 
        omega
      refine ⟨(x - 1) / 3, Or.inr ?_⟩
      omega
    · -- x % 6 = 2
      have h2 : x % 6 = 2 := h1
      have h3 : (x ^ 2 + 5 * x - 12) % 6 = 0 := by
        omega
      have h4 : (x ^ 2 + 5 * x - 12) % 6 = 2 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h2]
      omega -- contradiction
    · -- x % 6 = 3
      have h2 : x % 6 = 3 := h1
      have h3 : x % 3 = 0 := by 
        omega
      refine ⟨x / 3, Or.inl ?_⟩
      omega
    · -- x % 6 = 4
      have h2 : x % 6 = 4 := h1
      have h3 : x % 3 = 1 := by 
        omega
      refine ⟨(x - 1) / 3, Or.inr ?_⟩
      omega
    · -- x % 6 = 5
      have h2 : x % 6 = 5 := h1
      have h3 : (x ^ 2 + 5 * x - 12) % 6 = 0 := by 
        omega
      have h4 : (x ^ 2 + 5 * x - 12) % 6 = 2 := by 
        simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h2]
      omega -- contradiction
  · -- Assume ∃ t, x = 3 * t ∨ x = 3 * t + 1, prove 6 ∣ x^2 + 5 * x - 12
    rintro ⟨t, h⟩
    rcases h with (h | h)
    · -- Case x = 3 * t
      rw [h]
      have h1 : (3 * t) ^ 2 + 5 * (3 * t) - 12 = 3 * (3 * t ^ 2 + 5 * t - 4) := by 
        ring
      rw [h1]
      have h2 : (3 * t ^ 2 + 5 * t - 4) % 2 = 0 := by 
        have h3 : t % 2 = 0 ∨ t % 2 = 1 := by 
          omega
        rcases h3 with (h3 | h3)
        all_goals
          simp [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, h3]
      have h3 : (3 * t ^ 2 + 5 * t - 4) % 2 = 0 := h2
      omega
    · -- Case x = 3 * t + 1
      rw [h]
      have h1 : (3 * t + 1) ^ 2 + 5 * (3 * t + 1) - 12 = 3 * (3 * t ^ 2 + 7 * t - 2) := by 
        ring
      rw [h1]
      have h2 : (3 * t ^ 2 + 7 * t - 2) % 2 = 0 := by 
        have h3 : t % 2 = 0 ∨ t % 2 = 1 := by 
          omega
        rcases h3 with (h3 | h3)
        all_goals
          simp [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, h3]
      have h3 : (3 * t ^ 2 + 7 * t - 2) % 2 = 0 := h2
      omega