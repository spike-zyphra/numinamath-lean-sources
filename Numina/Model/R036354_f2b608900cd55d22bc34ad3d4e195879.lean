import Mathlib

theorem algebra_21708 (capacity : ℕ) (current_enrollment : ℕ) (growth_rate : ℝ)
    (h₀ : capacity = 1100) (h₁ : current_enrollment = 980) (h₂ : growth_rate = 0.05) :
    IsLeast {n | current_enrollment * (1 + growth_rate) ^ n > capacity} 3 := by
  rw [IsLeast]
  constructor
  · -- Show 3 is in the set.
    rw [Set.mem_setOf_eq]
    rw [h₁, h₂, h₀]
    norm_num
  · -- Show no smaller integer is in the set.
    intro n hn
    rw [Set.mem_setOf_eq] at hn
    rw [h₁, h₂, h₀] at hn
    by_contra h
    push_neg at h
    have h3 : n < 3 := h
    have h4 : (980 : ℝ) * (1 + (0.05 : ℝ)) ^ n ≤ (1100 : ℝ) := by
      interval_cases n <;> norm_num
    linarith