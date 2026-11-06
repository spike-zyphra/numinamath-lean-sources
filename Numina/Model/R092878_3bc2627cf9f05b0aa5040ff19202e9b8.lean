import Mathlib

theorem number_theory_5799 : IsGreatest {x | x ∣ (∑ i ∈ Finset.range 20, 7 ^ i) ∧ x ∣ (∑ i ∈ Finset.range 5, 7 ^ i)} 2801 := by
  constructor
  · -- Show that 2801 divides both sums
    constructor
    · -- Compute sum of 7^i for i in [0, 20) and show divisibility
      native_decide
    · -- Compute sum of 7^i for i in [0, 5) and show divisibility
      native_decide
  · -- Show that 2801 is the greatest divisor
    intro x hx
    rcases hx with ⟨hx₁, hx₂⟩
    have h₁ : x ∣ (∑ i ∈ Finset.range 20, 7 ^ i) := hx₁
    have h₂ : x ∣ (∑ i ∈ Finset.range 5, 7 ^ i) := hx₂
    have : ∑ i ∈ Finset.range 5, 7 ^ i = 2801 := by
      norm_num [Finset.sum_range_succ]
    have h₃ : x ∣ 2801 := by
      rw [this] at h₂
      exact h₂
    have : x ≤ 2801 := by
      exact Nat.le_of_dvd (by norm_num) h₃
    linarith