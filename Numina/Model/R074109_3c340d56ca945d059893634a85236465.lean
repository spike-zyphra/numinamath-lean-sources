import Mathlib

theorem number_theory_110947 :
    {(n, m) : ℕ × ℕ | n * 42 + m * 20 = 482}.encard = 2 := by 
  have h1 : {(n, m) : ℕ × ℕ | n * 42 + m * 20 = 482} = {(1, 22), (11, 1)} := by
    ext ⟨n, m⟩
    simp 
    constructor
    · -- Assume n * 42 + m * 20 = 482, show (n, m) ∈ {(1, 22), (11, 1)}
      rintro H
      have eq1 : n * 42 + m * 20 = 482 := H
      have h2 : n ≤ 11 := by
        omega 
      have h3 : m ≤ 24 := by
        omega 
      interval_cases n <;> omega 
    · -- Show that if (n, m) ∈ {(1, 22), (11, 1)}, then n * 42 + m * 20 = 482
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Case (1, 22)
        norm_num 
      · -- Case (11, 1)
        norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_pair]
  <;> rfl