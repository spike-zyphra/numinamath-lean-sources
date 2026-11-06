import Mathlib

theorem algebra_9110 (f : ℕ → ℕ) (hf : f = fun x => x ^ 3 + 4 * x ^ 2 + 2 * x - 4) :
    IsLeast {x | 0 < x ∧ 13 ∣ f x} 3 ∧
    IsLeast {x | 3 < x ∧ 13 ∣ f x} 8 ∧
    IsLeast {x | 8 < x ∧ 13 ∣ f x} 11 := by
  constructor
  · -- 3 is the smallest positive integer such that 13 divides f(x)
    constructor
    · -- Show 3 is in the set
      refine ⟨by norm_num, ?_⟩
      rw [hf]
      norm_num
    · -- Show that for all x in the set, 3 ≤ x
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      by_contra h
      push_neg at h
      have h1 : x ≤ 2 := by omega
      interval_cases x <;> simp [hf] at hx2 <;> omega
  constructor
  · -- 8 is the smallest integer greater than 3 such that 13 divides f(x)
    constructor
    · -- Show 8 is in the set
      refine ⟨by norm_num, ?_⟩
      rw [hf]
      norm_num
    · -- Show that for all x in the set, 8 ≤ x
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      by_contra h
      push_neg at h
      have h1 : x ≤ 7 := by omega
      interval_cases x <;> simp [hf] at hx2 <;> omega
  · -- 11 is the smallest integer greater than 8 such that 13 divides f(x)
    constructor
    · -- Show 11 is in the set
      refine ⟨by norm_num, ?_⟩
      rw [hf]
      norm_num
    · -- Show that for all x in the set, 11 ≤ x
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      by_contra h
      push_neg at h
      have h1 : x ≤ 10 := by omega
      interval_cases x <;> simp [hf] at hx2 <;> omega