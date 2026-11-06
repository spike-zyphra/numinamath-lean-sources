import Mathlib

open Real Set

theorem algebra_323995 :
    {m : ℝ | ∃ A B : Set ℝ , A = {x | -2 ≤ x ∧ x ≤ 5} ∧ B = {x | m + 1 ≤ x ∧ x ≤ 2 * m - 1} ∧ A ∩ B = B } = {m : ℝ | m ≤ 3 } := by
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume ∃ A B : Set ℝ, A = {x | -2 ≤ x ∧ x ≤ 5} ∧ B = {x | m + 1 ≤ x ∧ x ≤ 2 * m - 1} ∧ A ∩ B = B, prove m ≤ 3
    rintro ⟨A, B, hA, hB, h_eq⟩
    have h1 : B ⊆ A := by 
      rw [Set.inter_eq_right] at h_eq 
      exact h_eq
    by_contra h
    push_neg at h
    -- We will show that there's an element in B which is not in A, contradiction.
    -- Let's take x = 2m - 1.
    have h2 : m > 3 := h
    -- We will show that there's an element in B which is not in A, contradiction.
    -- Let's take x = 2m - 1.
    have h3 : 2 * m - 1 > 5 := by linarith
    have h4 : m + 1 ≤ 2 * m - 1 := by linarith
    have h5 : (2 * m - 1 : ℝ) ∈ B := by 
      rw [hB]
      exact ⟨by linarith, by linarith⟩
    have h6 : (2 * m - 1 : ℝ) ∈ A := h1 h5
    rw [hA] at h6
    have h7 : -2 ≤ (2 * m - 1 : ℝ) ∧ (2 * m - 1 : ℝ) ≤ 5 := by
      simpa using h6
    linarith
  · -- Assume m ≤ 3, prove ∃ A B : Set ℝ, A = {x | -2 ≤ x ∧ x ≤ 5} ∧ B = {x | m + 1 ≤ x ∧ x ≤ 2 * m - 1} ∧ A ∩ B = B
    intro hm
    use {x | -2 ≤ x ∧ x ≤ 5}, {x | m + 1 ≤ x ∧ x ≤ 2 * m - 1}
    constructor
    · -- A = {x | -2 ≤ x ∧ x ≤ 5}
      rfl
    constructor
    · -- B = {x | m + 1 ≤ x ∧ x ≤ 2 * m - 1}
      rfl
    · -- A ∩ B = B
      have h1 : m ≤ 3 := hm
      ext x
      constructor
      · -- Assume x ∈ A ∩ B, prove x ∈ B
        rintro ⟨⟨hx1, hx2⟩, ⟨hx3, hx4⟩⟩
        exact ⟨hx3, hx4⟩
      · -- Assume x ∈ B, prove x ∈ A ∩ B
        intro h
        have h11 : m + 1 ≤ x := by
          have h3 : x ∈ {x | m + 1 ≤ x ∧ x ≤ 2 * m - 1} := h
          simpa using h.1
        have h22 : x ≤ 2 * m - 1 := by
          have h4 : x ∈ {x | m + 1 ≤ x ∧ x ≤ 2 * m - 1} := h
          simpa using h.2
        have h17 : m ≥ 2 := by
          nlinarith
        have h13 : -2 ≤ x := by
          nlinarith
        have h133 : x ≤ 5 := by
          nlinarith
        constructor
        · -- Show x ∈ A
          exact ⟨h13, h133⟩
        · -- Show x ∈ B
          exact h