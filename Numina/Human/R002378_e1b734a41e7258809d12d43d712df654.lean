import Mathlib

/-How many ordered triples of integers (a,b,c) satisfy the following system?
ab+c=17,a+bc=19-/
theorem algebra_90086 : {(a, b, c) : ℤ × ℤ × ℤ | a * b + c = 17 ∧ a + b * c = 19}.ncard = 3 := by
-- we directly compute the set --
  have h1: {(a, b, c) : ℤ × ℤ × ℤ | a * b + c = 17 ∧ a + b * c = 19} = {(19, 0, 17), (5, 2, 7), (4, 3, 5)} := by
    ext ⟨a, b, c⟩
    simp
    constructor
    -- the forward direction --
    · rintro ⟨h1, h2⟩
      -- simplify the equations --
      have h3 : (1 - b) * (a - c) = 2 := by
        nlinarith
      have h4 : (1 - b) ≠ 0 := by
        by_contra h
        have : (a - c) = 0 := by nlinarith
        nlinarith
      -- we compute all cases for b --
      have h5 : (1 - b) = 1 ∨ (1 - b) = -1 ∨ (1 - b) = 2 ∨ (1 - b) = -2 := by
        have h6 : (1 - b) * (a - c) = 2 := h3
        have h7 : (1 - b) ≠ 0 := h4
        have h8 : (1 - b) ∣ 2 := by
          use (a - c)
          nlinarith
        have h9 : (1 - b) ≤ 2 := by
          by_cases h10 : 1 - b > 0
          · have h11 : (1 - b) ≤ 2 := by
              by_contra h12
              push_neg at h12
              have h13 : (1 - b) * (a - c) ≥ 3 := by nlinarith [show (a - c) ≥ 1 by nlinarith [show (a - c) > 0 by nlinarith [h6, h10]]]
              linarith
            linarith
          · have h10 : (1 - b) ≤ 0 := by omega
            have h11 : (1 - b) ≤ 2 := by nlinarith
            linarith
        have h10 : (1 - b) ≥ -2 := by
          by_cases h11 : 1 - b < 0
          · have h12 : (1 - b) ≥ -2 := by
              by_contra h13
              push_neg at h13
              have h14 : (1 - b) * (a - c) ≤ -3 := by nlinarith [show (a - c) ≤ -1 by nlinarith [show (a - c) < 0 by nlinarith [h6, h11]]]
              linarith
            linarith
          · have h11 : (1 - b) ≥ 0 := by omega
            linarith
        have : (1 - b) = 1 ∨ (1 - b) = -1 ∨ (1 - b) = 2 ∨ (1 - b) = -2 := by
          interval_cases (1 - b) <;> tauto
        assumption
      -- discuss all cases for b --
      rcases h5 with (h5 | h5 | h5 | h5)
      · -- Case 1 - b = 1
        have hb : b = 0 := by linarith
        have hac : a - c = 2 := by
          rw [h5] at h3
          linarith
        have hc : c = 17 := by
          have h1' : a * b + c = 17 := h1
          rw [hb] at h1'
          simp at h1'
          linarith
        have ha : a = 19 := by
          linarith [hac, hc]
        exact Or.inl ⟨ha, hb, hc⟩
      · -- Case 2 - b = -1
        have hb : b = 2 := by linarith
        have hac : a - c = -2 := by
          rw [h5] at h3
          linarith
        have hc : c = 7 := by
          have h2' : a + b * c = 19 := h2
          rw [hb] at h2'
          have ha_eq : a = c - 2 := by linarith [hac]
          rw [ha_eq] at h2'
          nlinarith
        have ha : a = 5 := by
          linarith [hac, hc]
        exact Or.inr (Or.inl ⟨ha, hb, hc⟩)
      · -- Case 3 - b = 2
        have hb : b = -1 := by linarith
        have hac : a - c = 1 := by
          rw [h5] at h3
          linarith
        have h2' : a + b * c = 19 := h2
        rw [hb] at h2'
        have h4 : a + (-1) * c = 19 := h2'
        have h5 : a - c = 1 := by linarith
        omega
      · -- Case 4 - b = -2
        have hb : b = 3 := by linarith
        have hac : a - c = -1 := by
          rw [h5] at h3
          linarith
        have hc : c = 5 := by
          have h2' : a + b * c = 19 := h2
          rw [hb] at h2'
          have ha_eq : a = c - 1 := by linarith [hac]
          rw [ha_eq] at h2'
          nlinarith
        have ha : a = 4 := by
          linarith [hac, hc]
        exact Or.inr (Or.inr ⟨ha, hb, hc⟩)
    -- the backward direction --
    · rintro (h | h | h)
      · -- (19, 0, 17)
        rcases h with ⟨ha, hb, hc⟩
        constructor <;> nlinarith
      · -- (5, 2, 7)
        rcases h with ⟨ha, hb, hc⟩
        constructor <;> nlinarith
      · -- (4, 3, 5)
        rcases h with ⟨ha, hb, hc⟩
        constructor <;> nlinarith
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
