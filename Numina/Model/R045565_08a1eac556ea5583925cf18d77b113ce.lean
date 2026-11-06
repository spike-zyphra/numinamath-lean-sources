import Mathlib

open BigOperators Real Set
open scoped BigOperators

theorem algebra_13650 {f : ℝ → ℝ → ℝ}
    (hf : f = fun k x => (2 * x + 3) / (k * x - 2)) :
    {k : ℝ | ∀ x, k * x - 2 ≠ 0 → f k (f k x) = x} = Iio (-4 / 3 : ℝ) ∪ Ioi (-4 / 3 : ℝ) := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · -- Assume k ∈ {k | ∀ x, k * x - 2 ≠ 0 → f k (f k x) = x}, prove k ∈ Iio (-4/3) ∪ Ioi (-4/3)
    intro hk
    have hk1 : k ≠ -4 / 3 := by
      by_contra h
      rw [h] at hk
      have h1 := hk 1 (by
        norm_num
      )
      norm_num [hf] at h1
    by_contra h
    push_neg at h
    have hk3 : k = -4 / 3 := by linarith
    contradiction
  · -- Assume k ∈ Iio (-4/3) ∪ Ioi (-4/3), prove k ∈ {k | ...}
    rintro (h | h)
    · -- Assume k < -4/3
      intro x hx
      have hk1 : k < -4 / 3 := h
      have h4 : k ≠ -4 / 3 := by
        linarith
      have eq1 : f k (f k x) = x := by
        have h1 : f k x = (2 * x + 3) / (k * x - 2) := by
          simp [hf]
        have h2 : f k (f k x) = (2 * ((2 * x + 3) / (k * x - 2)) + 3) / (k * ((2 * x + 3) / (k * x - 2)) - 2) := by
          rw [h1]
          all_goals
            simp [hf]
        rw [h2]
        have h4 : k * x - 2 ≠ 0 := hx
        have hk2 : 3 * k + 4 ≠ 0 := by
          intro h0
          have h1 : k = -4 / 3 := by
            nlinarith
          nlinarith
        have hk8 : (3 * k + 4) ≠ 0 := hk2
        have h7 : (2 * ((2 * x + 3) / (k * x - 2)) + 3) / (k * ((2 * x + 3) / (k * x - 2)) - 2) = x := by
          have eq4 : (2 * ((2 * x + 3) / (k * x - 2)) + 3) = x * (3 * k + 4) / (k * x - 2) := by
            have h5 : k * x - 2 ≠ 0 := hx
            field_simp [h5]
            ring
          have eq5 : (k * ((2 * x + 3) / (k * x - 2)) - 2) = (3 * k + 4) / (k * x - 2) := by
            have h5 : k * x - 2 ≠ 0 := hx
            field_simp [h5]
            ring
          rw [eq4, eq5]
          have eq7 : (x * (3 * k + 4) / (k * x - 2)) / ((3 * k + 4) / (k * x - 2)) = x := by
            have hk15 : k * x - 2 ≠ 0 := hx
            have hk16 : 3 * k + 4 ≠ 0 := hk2
            field_simp [hk15, hk16]
            <;> ring
          exact eq7
        linarith
      exact eq1
    · -- Assume k > -4/3
      intro x hx
      have hk1 : k > -4 / 3 := h
      have h4 : k ≠ -4 / 3 := by
        linarith
      have eq1 : f k (f k x) = x := by
        have h1 : f k x = (2 * x + 3) / (k * x - 2) := by
          simp [hf]
        have h2 : f k (f k x) = (2 * ((2 * x + 3) / (k * x - 2)) + 3) / (k * ((2 * x + 3) / (k * x - 2)) - 2) := by
          rw [h1]
          all_goals
            simp [hf]
        rw [h2]
        have h4 : k * x - 2 ≠ 0 := hx
        have hk2 : 3 * k + 4 ≠ 0 := by
          intro h0
          have h1 : k = -4 / 3 := by
            nlinarith
          nlinarith
        have hk8 : (3 * k + 4) ≠ 0 := hk2
        have h7 : (2 * ((2 * x + 3) / (k * x - 2)) + 3) / (k * ((2 * x + 3) / (k * x - 2)) - 2) = x := by
          have eq4 : (2 * ((2 * x + 3) / (k * x - 2)) + 3) = x * (3 * k + 4) / (k * x - 2) := by
            have h5 : k * x - 2 ≠ 0 := hx
            field_simp [h5]
            ring
          have eq5 : (k * ((2 * x + 3) / (k * x - 2)) - 2) = (3 * k + 4) / (k * x - 2) := by
            have h5 : k * x - 2 ≠ 0 := hx
            field_simp [h5]
            ring
          rw [eq4, eq5]
          have eq7 : (x * (3 * k + 4) / (k * x - 2)) / ((3 * k + 4) / (k * x - 2)) = x := by
            have hk15 : k * x - 2 ≠ 0 := hx
            have hk16 : 3 * k + 4 ≠ 0 := hk2
            field_simp [hk15, hk16]
            <;> ring
          exact eq7
        linarith
      exact eq1