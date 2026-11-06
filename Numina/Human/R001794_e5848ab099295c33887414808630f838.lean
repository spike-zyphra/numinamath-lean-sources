import Mathlib

/-How many pairs of integers (x,y) are there such that 2x+5y=xy-1 ?-/
theorem algebra_35621 :
    {(x, y) : ℤ × ℤ | 2 * x + 5 * y = x * y - 1}.encard = 4 := by
    
    -- we directly compute the set
  have h : {(x, y) : ℤ × ℤ | 2 * x + 5 * y = x * y - 1} = {(4, -9), (6, 13), (-6, 1), (16, 3)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume (x, y) satisfies 2x + 5y = xy - 1
      rintro h
      have h2 : (x - 5) * (y - 2) = 11 := by linarith
      have h3 : x - 5 = 1 ∨ x - 5 = -1 ∨ x - 5 = 11 ∨ x - 5 = -11 := by
        have h5 : (x - 5) ≠ 0 := by
          by_contra h6
          rw [h6] at h2
          have : (y - 2) = 0 := by linarith
          have h7 : 11 = 0 := by linarith
          linarith       
        have h7 : (x - 5) ∣ 11 := by  -- this gives the bound 
            use (y - 2)
            linarith       
        have h10 : (x - 5) ≤ 11 := by
              by_cases h11 : x - 5 ≤ 0
              · nlinarith
              · -- x - 5 > 0
                have h12 : (x - 5) ∣ 11 := h7
                have h13 : (x - 5) ≤ 11 := by
                  exact Int.le_of_dvd (by norm_num) h12
                linarith
        have h11 : (x - 5) ≥ -11 := by
              by_cases h12 : x - 5 ≥ 0
              · nlinarith
              · -- x - 5 < 0
                have h13 : (x - 5) ∣ 11 := h7
                have h14 : (x - 5) ≥ -11 := by
                  by_contra h15
                  push_neg at h15
                  have h16 : (x - 5) ≤ -12 := by linarith
                  have h17 : (x - 5) ∣ 11 := h7
                  have h18 : ∃ k : ℤ, 11 = (x - 5) * k := h17
                  rcases h18 with ⟨k, hk⟩
                  have h19 : k ≥ 0 := by nlinarith
                  have h20 : k ≤ 0 := by nlinarith
                  have h21 : k = 0 := by linarith
                  rw [h21] at hk
                  linarith
                linarith
        interval_cases (x - 5) <;> tauto
      -- now we check them all
      rcases h3 with (h4 | h5 | h6 | h7)
      · -- Case x - 5 = 1, so x = 6
        have hx : x = 6 := by linarith
        have hy : y = 13 := by
          have h8 : (x - 5) * (y - 2) = 11 := h2
          rw [hx] at h8
          linarith
        right
        left
        exact ⟨hx, hy⟩
      · -- Case x - 5 = -1, so x = 4
        have hx : x = 4 := by linarith
        have hy : y = -9 := by
          have h8 : (x - 5) * (y - 2) = 11 := h2
          rw [hx] at h8
          linarith
        left
        exact ⟨hx, hy⟩
      · -- Case x - 5 = 11, so x = 16
        have hx : x = 16 := by linarith
        have hy : y = 3 := by
          have h8 : (x - 5) * (y - 2) = 11 := h2
          rw [hx] at h8
          linarith
        right
        right
        right
        exact ⟨hx, hy⟩
      · -- Case x - 5 = -11, so x = -6
        have hx : x = -6 := by linarith
        have hy : y = 1 := by
          have h8 : (x - 5) * (y - 2) = 11 := h2
          rw [hx] at h8
          linarith
        right
        right
        left
        exact ⟨hx, hy⟩
    · -- Show that each of the four pairs satisfies the equation
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h]
  rw [Set.encard]
  simp [Set.ncard]