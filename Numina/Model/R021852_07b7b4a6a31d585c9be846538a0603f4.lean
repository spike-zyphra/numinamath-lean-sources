import Mathlib

theorem algebra_294796 (f : ℕ → ℤ) (h : ∀ x, f (x + 1) = f x ^ 2 - 2 * f x + 1)
    (hf : f 0 = 2) : f 2019 = 1 := by
  have h1 : f 1 = 1 := by
    specialize h 0
    rw [hf] at h
    norm_num at h
    linarith
  have h2 : ∀ (n : ℕ), f (2 * n + 1) = 1 := by
    intro n
    induction n with
    | zero =>
      norm_num [h1]
    | succ n ih =>
      have eq1 : f (2 * n + 2) = 0 := by
        have eq2 : f (2 * n + 2) = f (2 * n + 1) ^ 2 - 2 * f (2 * n + 1) + 1 := by
          specialize h (2 * n + 1)
          simpa using h
        rw [eq2, ih]
        all_goals norm_num
      have eq3 : f (2 * (n + 1) + 1) = f (2 * n + 2) ^ 2 - 2 * f (2 * n + 2) + 1 := by
        specialize h (2 * n + 2)
        simpa using h
      rw [eq3, eq1]
      all_goals norm_num
  have eq1 : 2019 = 2 * 1009 + 1 := by 
    omega
  rw [eq1]
  apply h2