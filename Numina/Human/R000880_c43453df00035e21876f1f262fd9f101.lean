import Mathlib

/-The Newport Crab Company marks the location of its crab pots with colored balloons. They mark every fourth pot with a red balloon, every sixth pot with a blue balloon, and every tenth pot with a yellow balloon. After placing 600 crab pots in the bay, how many pots have three different colored balloons attached?-/
theorem algebra_18795 (n : ℕ) (hn : n = 600) :
    {x | x ∈ Finset.Icc 1 n ∧ (x % 4 = 0 ∧ x % 6 = 0 ∧ x % 10 = 0)}.ncard = 10 := by 
  rw [hn]
  simp
  have : {x | (1 ≤ x ∧ x ≤ 600) ∧ x % 4 = 0 ∧ x % 6 = 0 ∧ x % 10 = 0} = 
         {x | ∃k, 0 < k ∧ k ≤ 10 ∧ x = 60 * k} := by
    ext m
    simp
    constructor
    · -- If (1 ≤ m ∧ m ≤ 600) ∧ m % 4 = 0 ∧ m % 6 = 0 ∧ m % 10 = 0
      -- Then m is the multiple of 60
      rintro ⟨⟨hm₁, hm₂⟩, hm_dvd3, hm_dvd4, hm_dvd10⟩
      obtain ⟨k, hk⟩ := show 60 ∣ m by omega
      use k
      omega
    · -- If m is the multiple of 60
      -- Then (1 ≤ m ∧ m ≤ 600) ∧ m % 4 = 0 ∧ m % 6 = 0 ∧ m % 10 = 0
      rintro ⟨k, hk₁, hk₂, hk₃⟩
      omega
  rw [this]
  apply Set.ncard_eq_of_bijective
  case f => exact λn _ ↦ 60 * (n + 1)
  
  -- ∀ x ∈ {x | ∃ q, 0 < q ∧ q ≤ 10 ∧ x = 60 * q}, ∃ i, ∃ (_ : i < 10), 60 * (i + 1) = x
  simp
  intro x a ha₁ ha₂ hx
  use a - 1
  omega

  -- ∀ i < 10, 60 * (i + 1) ∈ {x | ∃ k, 0 < k ∧ k ≤ 10 ∧ x = 60 * k}
  simp
  omega

  -- ∀ (i j : ℕ), i < 10 → j < 10 → 60 * (i + 1) = 60 * (j + 1) → i = j
  simp