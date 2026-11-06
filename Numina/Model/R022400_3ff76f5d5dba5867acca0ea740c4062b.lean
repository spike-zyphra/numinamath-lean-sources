import Mathlib

theorem algebra_177702 (f : ℕ → ℕ) (h : ∀ m n, f (m + f n) = f (f m) + f n) :
    ∀ m, f m = m ↔ m ∈ Set.range f := by
  have h1 : f 0 = 0 := by
    have h2 := h 0 0
    simp at h2
    all_goals
      omega
  have h2 : ∀ n, f (f n) = f n := by
    intro n
    have h3 := h 0 n
    simp [h1] at h3
    omega
  intro m
  constructor
  · -- Assume f m = m, prove m ∈ Set.range f
    intro h3
    refine ⟨m, by simpa [h3]⟩
  · -- Assume m ∈ Set.range f, prove f m = m
    rintro ⟨n, hn⟩
    have h4 : f n = m := hn
    have h5 : f (f n) = f n := h2 n
    rw [h4] at h5
    omega