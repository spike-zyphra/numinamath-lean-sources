import Mathlib

theorem number_theory_115436 (a : ℕ → ℕ) (ha : StrictMono a) :
    ∃ b : ℕ → ℕ, (∀ i, b i ∈ Set.range a) ∧
      ( (∀ i j, i < j → b i ∣ b j) ∨
        (∀ i j, i ≠ j → ¬(b i ∣ b j)) ) := by
  use fun i => a 0
  constructor
  · -- To verify trivial sequence satisfy all conditions
    intro i
    exact Set.mem_range.mpr ⟨0, rfl⟩
  left
  intro i j h
  simp