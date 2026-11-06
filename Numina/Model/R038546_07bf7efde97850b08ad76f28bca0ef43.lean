import Mathlib

theorem algebra_10238 : IsGreatest { z | ∃ f g h j : ℤ, Multiset.ofList [f, g, h, j] = Multiset.ofList [5, 6, 7, 8] ∧ z = f * g + g * h + h * j + f * j } 169 := by
  constructor
  · -- Show that 169 is indeed achievable
    use 5, 7, 8, 6
    native_decide
  · -- Show that no larger value is achievable
    rintro z ⟨f, g, h, j, h1, h2⟩
    have h3 : f = 5 ∨ f = 6 ∨ f = 7 ∨ f = 8 := by
      have h4 : f ∈ (Multiset.ofList [f, g, h, j] : Multiset ℤ) := by
        simp
      rw [h1] at h4
      simp at h4
      omega
    -- g is among 5,6,7,8
    have h4 : g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 8 := by
      have h5 : g ∈ (Multiset.ofList [f, g, h, j] : Multiset ℤ) := by
        simp
      rw [h1] at h5
      simp at h5
      omega
    -- h is among 5,6,7,8
    have h5 : h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 := by
      have h6 : h ∈ (Multiset.ofList [f, g, h, j] : Multiset ℤ) := by
        simp
      rw [h1] at h6
      simp at h6
      omega
    -- j is among 5,6,7,8
    have h6 : j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by
      have h7 : j ∈ (Multiset.ofList [f, g, h, j] : Multiset ℤ) := by
        simp
      rw [h1] at h7
      simp at h7
      omega
    rcases h3 with (rfl | rfl | rfl | rfl) <;> rcases h4 with (rfl | rfl | rfl | rfl) <;> rcases h5 with (rfl | rfl | rfl | rfl) <;> rcases h6 with (rfl | rfl | rfl | rfl) <;> try { 
      norm_num [h2] at *
      <;> try { tauto }
      <;> omega
    }