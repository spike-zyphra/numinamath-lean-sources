import Mathlib

theorem algebra_99136 (x : ℕ) (A B : Finset ℕ)
    (hA : A = {x - 1, 2 * x - 3, 3 * x + 1, 4 * x - 1})
    (hB : B = {4 * x - 2, 3 * x + 2, 3 * x - 6, 2 * x - 4}) :
    x = 3 ↔ A = B := by
  constructor
  · -- Forward: x = 3 implies A = B
    intro h_eq3
    rw [hA, hB, h_eq3]
    native_decide
  · -- Reverse: A = B implies x = 3
    intro h_eq
    rw [hA, hB] at h_eq
    have eq1 : x = 3 := by
      have h1 : ({x - 1, 2 * x - 3, 3 * x + 1, 4 * x - 1} : Finset ℕ) = ({4 * x - 2, 3 * x + 2, 3 * x - 6, 2 * x - 4} : Finset ℕ) := by
        simpa [hA, hB] using h_eq
      have h2 : (3 * x + 1) ∈ ( {4 * x - 2, 3 * x + 2, 3 * x - 6, 2 * x - 4} : Finset ℕ) := by
        have h2 : (3 * x + 1) ∈ ( {x - 1, 2 * x - 3, 3 * x + 1, 4 * x - 1} : Finset ℕ) := by 
          simp [Finset.mem_insert, Finset.mem_singleton]
        have h3 : ( {x - 1, 2 * x - 3, 3 * x + 1, 4 * x - 1} : Finset ℕ) = ( {4 * x - 2, 3 * x + 2, 3 * x - 6, 2 * x - 4} : Finset ℕ) := h1
        rw [h3] at h2 
        exact h2 
      simp [Finset.mem_insert, Finset.mem_singleton] at h2
      all_goals omega 
    exact_mod_cast eq1