import Mathlib

theorem algebra_166296 (l : ℕ → ℝ) 
    (hl : ∀ n, l n = (200000 - 50 * (n : ℝ)) * (5 + 0.05 * (n : ℝ))) : 
    IsGreatest {x | ∃ n, x = l n} (l 1950) := by
  constructor
  · -- Show that l 1950 is in the set.
    use 1950
  · -- Show that for any x in the set, x ≤ l 1950.
    intro x hx
    rcases hx with ⟨n, hn⟩
    rw [hn]
    have eq1 : l n = (200000 - 50 * (n : ℝ)) * (5 + 0.05 * (n : ℝ)) := hl n
    have eq2 : l 1950 = (200000 - 50 * (1950 : ℝ)) * (5 + 0.05 * (1950 : ℝ)) := hl 1950
    rw [eq1, eq2]
    have h1 : (200000 - 50 * (n : ℝ)) * (5 + 0.05 * (n : ℝ)) ≤ (200000 - 50 * (1950 : ℝ)) * (5 + 0.05 * (1950 : ℝ)) := by
      nlinarith [sq_nonneg ((n : ℝ) - (1950 : ℝ)), sq_nonneg ((n : ℝ) - (1950 : ℝ)), sq_nonneg ((n : ℝ) - (1950 : ℝ)), sq_nonneg ((n : ℝ) - (1950 : ℝ))]
    linarith