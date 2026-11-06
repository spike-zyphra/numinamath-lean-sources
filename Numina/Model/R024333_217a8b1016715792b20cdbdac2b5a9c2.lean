import Mathlib

theorem algebra_200894 {f : ℕ → ℤ} (h : ∀ x, 0 < x → f x = f (x - 1) + f (x + 1)) (hf : f 0 = 1992) :
    f 1992 = 1992 := by

  have h1 : ∀ (x : ℕ), f (x + 6) = f x := by
    intro x

    have eq1 : f (x + 1) = f x + f (x + 2) := by
      specialize h (x + 1) (by linarith)
      simpa using h

    have eq2 : f (x + 2) = f (x + 1) + f (x + 3) := by
      specialize h (x + 2) (by linarith)
      simpa using h

    have eq3 : f (x + 3) = f (x + 2) + f (x + 4) := by
      specialize h (x + 3) (by linarith)
      simpa using h

    have eq4 : f (x + 4) = f (x + 3) + f (x + 5) := by
      specialize h (x + 4) (by linarith)
      simpa using h

    have eq5 : f (x + 5) = f (x + 4) + f (x + 6) := by
      specialize h (x + 5) (by linarith)
      simpa using h

    linarith [eq1, eq2, eq3, eq4, eq5]

  have h2 : ∀ (k : ℕ), f (6 * k) = f 0 := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      calc
        f (6 * (k + 1)) = f (6 * k + 6) := by
          ring_nf
        _ = f (6 * k) := by
          rw [show 6 * k + 6 = (6 * k) + 6 by ring]
          rw [h1]
        _ = f 0 := by
          rw [ih]

  have h3 : (1992 : ℕ) = 6 * (332 : ℕ) := by
    omega

  calc
    f 1992 = f (6 * 332) := by
      rw [h3]
    _ = f 0 := by
      rw [h2 332]
    _ = 1992 := by
      rw [hf]