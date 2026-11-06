import Mathlib

theorem number_theory_297944 (a b : ℝ) (ha : a < b) (f : ℝ → ℝ) (hf : f = fun x => abs (x - a) - abs (x - b)) :
    Set.range f = {x | x ∈ Set.Icc (-abs (b - a)) (abs (b - a))} := by
  have h1 : ∀ x : ℝ, f x = abs (x - a) - abs (x - b) := by 
    intro x
    rw [hf]
  have h2 : abs (b - a) = b - a := by
    rw [abs_of_pos]
    linarith
  ext y
  simp only [Set.mem_range, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- First, show that if $y \in range\ f$, then $y \in [-|b-a|, |b-a|]$.
    rintro ⟨x, hx⟩
    rw [h1 x] at hx
    have hy : y ∈ Set.Icc (-abs (b - a)) (abs (b - a)) := by
      by_cases h3 : x ≥ b
      · -- Case 1: x ≥ b
        rw [abs_of_nonneg (show x - a ≥ 0 by linarith), abs_of_nonneg (show x - b ≥ 0 by linarith)] at hx
        constructor
        · -- Show that -abs (b - a) ≤ (x - a) - (x - b)
          rw [h2]
          nlinarith
        · -- Show that (x - a) - (x - b) ≤ abs (b - a)
          rw [h2]
          nlinarith
      by_cases h4 : x ≤ a
      · -- Case 2: x ≤ a
        rw [abs_of_nonpos (show x - a ≤ 0 by linarith), abs_of_nonpos (show x - b ≤ 0 by linarith)] at hx
        constructor
        · -- Show that -abs (b - a) ≤ (a - x) - (b - x)
          rw [h2]
          nlinarith
        · -- Show that (a - x) - (b - x) ≤ abs (b - a)
          rw [h2]
          nlinarith
      · -- Case 3: a < x < b
        rw [abs_of_nonneg (show x - a ≥ 0 by linarith), abs_of_nonpos (show x - b ≤ 0 by linarith)] at hx
        constructor
        · -- Show that -abs (b - a) ≤ (x - a) - (b - x)
          rw [h2]
          nlinarith
        · -- Show that (x - a) - (b - x) ≤ abs (b - a)
          rw [h2]
          nlinarith
    simpa using hy
  · -- Now, show the converse: if $y \in [-|b-a|, |b-a|]$, then $y \in range\ f$.
    intro h
    rcases h with ⟨h3, h4⟩
    rw [h2] at h3 h4
    use (y + a + b) / 2
    rw [h1]
    have hx1 : (y + a + b) / 2 ≥ a := by
      linarith
    have hx2 : (y + a + b) / 2 ≤ b := by
      linarith
    rw [abs_of_nonneg (show (y + a + b) / 2 - a ≥ 0 by linarith), abs_of_nonpos (show (y + a + b) / 2 - b ≤ 0 by linarith)]
    all_goals nlinarith