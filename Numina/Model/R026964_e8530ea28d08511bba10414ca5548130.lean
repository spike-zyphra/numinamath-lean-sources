import Mathlib

theorem number_theory_7084 (s : Finset ℤ) (h : s = {-10, -6, -1, 2, 10, 12, 14}) :
    ∀ x, ∃! y ∈ s, x ≡ y [ZMOD 7] := by
  intro x 
  use if x % 7 = 0 then 14 else
      if x % 7 = 1 then -6 else
          if x % 7 = 2 then 2 else
              if x % 7 = 3 then 10 else
                  if x % 7 = 4 then -10 else
                      if x % 7 = 5 then 12 else -1 
  have h2 : (if x % 7 = 0 then 14 else
      if x % 7 = 1 then -6 else
          if x % 7 = 2 then 2 else
              if x % 7 = 3 then 10 else
                  if x % 7 = 4 then -10 else
                      if x % 7 = 5 then 12 else -1) ∈ s := by 
    rw [h]
    simp
    <;> omega 
  have h3 : x ≡ (if x % 7 = 0 then 14 else
      if x % 7 = 1 then -6 else
          if x % 7 = 2 then 2 else
              if x % 7 = 3 then 10 else
                  if x % 7 = 4 then -10 else
                      if x % 7 = 5 then 12 else -1) [ZMOD 7] := by 
    have h4 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by 
      omega 
    rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4)
    all_goals
      simp [Int.ModEq, h4]
      all_goals omega 
  constructor 
  · -- Show existence 
    tauto 
  · -- Show uniqueness 
    intro z hz 
    rcases hz with ⟨hz1, hz2⟩ 
    have h4 : z = -10 ∨ z = -6 ∨ z = -1 ∨ z = 2 ∨ z = 10 ∨ z = 12 ∨ z = 14 := by
      have h5 : z ∈ s := hz1
      rw [h] at h5 
      simp at h5 ⊢ 
      tauto 
    have h5 : x % 7 = z % 7 := by 
      norm_num [Int.ModEq] at hz2 
      omega 
    rcases h4 with (r | r | r | r | r | r | r)
    all_goals
      rw [r] at h5 
      have h7 : z = (if x % 7 = 0 then 14 else
          if x % 7 = 1 then -6 else
              if x % 7 = 2 then 2 else
                  if x % 7 = 3 then 10 else
                      if x % 7 = 4 then -10 else
                          if x % 7 = 5 then 12 else -1) := by 
        have h8 : z % 7 = (if x % 7 = 0 then 14 else
            if x % 7 = 1 then -6 else
                if x % 7 = 2 then 2 else
                    if x % 7 = 3 then 10 else
                        if x % 7 = 4 then -10 else
                            if x % 7 = 5 then 12 else -1) % 7 := by
          omega 
        have h5' : (if x % 7 = 0 then 14 else
            if x % 7 = 1 then -6 else
                if x % 7 = 2 then 2 else
                    if x % 7 = 3 then 10 else
                        if x % 7 = 4 then -10 else
                            if x % 7 = 5 then 12 else -1) ∈ s := h2 
        rw [h] at h5' 
        simp at h5' 
        omega 
      tauto