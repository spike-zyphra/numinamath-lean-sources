import Mathlib

theorem number_theory_14226 : IsLeast {n | ∀ m, Even m → n ≠ m % 10} 1 := by
  constructor
  · -- Show 1 is in the set.
    show ∀ m, Even m → 1 ≠ m % 10
    intro m hm
    have h1 : m % 2 = 0 := by
      obtain ⟨k, hk⟩ := hm
      omega
    by_contra h
    have h2 : m % 10 = 1 := by
      omega
    have h3 : m % 2 = 1 := by
      omega
    omega
  · -- Show that 1 is the smallest element in the set.
    show ∀ n, (∀ m, Even m → n ≠ m % 10) → 1 ≤ n
    intro n hn
    by_contra h
    push_neg at h
    have h0 : n = 0 := by 
      omega
    -- Show that n = 0, which contradicts hn.
    have h1 := hn 0 (by simp)
    simp [h0] at h1
    all_goals omega