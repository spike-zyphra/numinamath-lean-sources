import Mathlib

theorem number_theory_290228 (a : ℕ → ℕ) (ha : a 0 = 1) (ha' : a 1 = 2)
    (h : ∀ m n, a m + a n ∉ Set.range a) (k : ℕ) :
    {i | a i < k}.ncard ≤ k / 3 + 2 := by
  have h00 : a 0 + a 0 ∉ Set.range a := h 0 0
  have h1 : a 0 + a 0 ∈ Set.range a := by 
    rw [ha]
    use 1
    all_goals simp [ha']
  contradiction