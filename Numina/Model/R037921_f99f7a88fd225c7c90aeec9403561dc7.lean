import Mathlib

theorem algebra_22401 : {a : ℝ | ∃ f : ℝ → ℝ, ∀ x y, f (x * y) = f x * f y ∧ f 1 = a} = {0, 1} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume that there exists a function f such that for all x, y, f(x*y) = f(x)*f(y) and f(1) = a.
    rintro ⟨f, hf⟩
    have h1 := hf 1 1
    rcases h1 with ⟨h2, h3⟩
    have h4 : f 1 = f 1 * f 1 := by
      simpa using h2
    have h6 : f 1 = a := by linarith
    rw [h6] at h4
    -- Now $a = a * a$.
    have h5 : a = 0 ∨ a = 1 := by
      have h7 : a * (a - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- Case $a = 0$:
        left
        linarith
      · -- Case $a - 1 = 0$ (so $a = 1$):
        right
        linarith
    tauto
  · -- Now prove the reverse direction. If $a \in \{0, 1\}$ then there exists a function with $f(1)=a$.
    rintro (ha | ha)
    · -- Case $a = 0$.
      use fun x => (0 : ℝ)
      intro x y
      constructor
      · -- Show that $f(x \cdot y) = f(x) \cdot f(y)$.
        simp
      · -- Show that $f(1) = a$.
        simp [ha]
    · -- Case $a = 1$.
      use fun x => (1 : ℝ)
      intro x y
      constructor
      · -- Show that $f(x \cdot y) = f(x) \cdot f(y)$.
        simp
      · -- Show that $f(1) = a$.
        simp [ha]