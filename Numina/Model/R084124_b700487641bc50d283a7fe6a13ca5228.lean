import Mathlib

theorem inequalities_47230 (s : Finset ℝ) (h₀ : s.card = 1400) :
    ∃ x ∈ s, ∃ y ∈ s, ∃ z ∈ s, |(x - y) * (y - z) * (z - x) / (x ^ 4 + y ^ 4 + z ^ 4 + 1)| < 0.009 := by
  have h1 : s.Nonempty := by 
    apply Finset.nonempty_iff_ne_empty.mpr
    by_contra h
    rw [h] at h₀
    simp at h₀
  rcases h1 with ⟨x, hx⟩
  use x, by simpa using hx
  use x, by simpa using hx
  use x, by simpa using hx
  norm_num
  <;> simp
  <;> norm_num