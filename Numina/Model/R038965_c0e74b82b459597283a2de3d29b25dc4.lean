import Mathlib

theorem algebra_14668 {a b : ℝ} :
    (∀ k, (a, b) ∈ {p : (ℝ × ℝ) | p.2 = 7 * p.1 ^ 2 + k * p.1 - 4 * k}) ↔ (a, b) = (4, 112) := by
  constructor
  · -- Forward direction: if (a, b) is in the set for all k, then (a, b) = (4, 112).
    intro h
    have h1 : ∀ k : ℝ, b = 7 * a ^ 2 + k * a - 4 * k := by
      intro k
      specialize h k
      simp at h
      linarith
    have eq1 := h1 0
    have eq2 := h1 1
    have ha : a = 4 := by
      nlinarith [eq1, eq2]
    have hb : b = 112 := by
      rw [ha] at eq1
      nlinarith
    simp [ha, hb]
  · -- Backward direction: (4, 112) is in the set for all k.
    rintro ⟨rfl, rfl⟩
    intro k
    simp
    <;> ring