import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_10190 :
  IsLeast {x | ∃ a b c : ℝ, a ∈ Ioc 0 2 ∧ b ∈ Ioc 0 2 ∧ c ∈ Ioc 0 2 ∧ (b ≥ 3 * a ∨ a + b ≤ 4 / 3) ∧ x = max (max (b - a) (c - b)) (4 - 2 * c)} (2 / 3) := by
  constructor
  · -- Show that 2/3 is achievable, with a = 1/3, b = 1, c = 5/3
    use 1 / 3, 1, 5 / 3
    norm_num [mem_Ioc]
  · -- Show that 2/3 is minimal in the set.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h₁, hx⟩
    rcases ha with ⟨ha0, ha1⟩
    rcases hb with ⟨hb0, hb1⟩
    rcases hc with ⟨hc0, hc1⟩
    by_contra h
    push_neg at h
    rw [hx] at h
    by_cases h2 : b ≥ 3 * a
    · -- Case where b ≥ 3a is true
      have h11 : max (max (b - a) (c - b)) (4 - 2 * c) < 2 / 3 := by
        linarith
      have h12 : b - a < 2 / 3 := by
        have h12 : b - a ≤ max (max (b - a) (c - b)) (4 - 2 * c) := by 
          simp
        linarith [h11, h12]
      have h13 : c - b < 2 / 3 := by
        have h13 : c - b ≤ max (max (b - a) (c - b)) (4 - 2 * c) := by 
          simp
        linarith [h11, h13]
      have h14 : 4 - 2 * c < 2 / 3 := by
        have h14 : 4 - 2 * c ≤ max (max (b - a) (c - b)) (4 - 2 * c) := by 
          simp
        linarith [h11, h14]
      have hc1' : c > 5 / 3 := by
        linarith
      nlinarith
    · -- Case where a + b ≤ 4/3 is true
      have h6 : a + b ≤ 4 / 3 := by
        tauto
      have h11 : max (max (b - a) (c - b)) (4 - 2 * c) < 2 / 3 := by
        linarith
      have h12 : b - a < 2 / 3 := by
        have h12 : b - a ≤ max (max (b - a) (c - b)) (4 - 2 * c) := by 
          simp
        linarith [h11, h12]
      have h13 : c - b < 2 / 3 := by
        have h13 : c - b ≤ max (max (b - a) (c - b)) (4 - 2 * c) := by 
          simp
        linarith [h11, h13]
      have h14 : 4 - 2 * c < 2 / 3 := by
        have h14 : 4 - 2 * c ≤ max (max (b - a) (c - b)) (4 - 2 * c) := by 
          simp
        linarith [h11, h14]
      have hc1' : c > 5 / 3 := by
        linarith
      nlinarith