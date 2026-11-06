import Mathlib

/- Let x_n be a sequence of real numbers defined recursively by
$x_0$ and $x_1$ being arbitrary positive real numbers,
and $x_{n+2} = \frac{1 + x_{n+1}}{x_n}$ for $n = 0, 1, 2, \ldots$. Determine the value of $x_{1998}$. -/

theorem algebra_612964 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℕ → ℝ)
    (h0 : x 0 = a) (h1 : x 1 = b)
    (h : ∀ n, x (n + 2) = (1 + x (n + 1)) / x n) :
    x 1998 = (a + b + 1) / (a * b) := by

  -- we first compute the first few terms
  have h2: x 2 = (1 + b) / a := by
    specialize h 0
    norm_num at h
    simp [h0, h1] at h
    rw [h]
  have h3: x 3 = (a + b + 1) / (a * b) := by
    specialize h 1
    norm_num at h
    simp [h0, h1, h2] at h
    rw [h]
    field_simp
    ring
  have h4: x 4 = (a + 1) / b := by
    specialize h 2
    norm_num at h
    simp [h0, h1, h2, h3] at h
    rw [h]
    field_simp
    ring
  have h5: x 5 = a := by
    specialize h 3
    norm_num at h
    simp [h0, h1, h2, h3, h4] at h
    rw [h]
    field_simp
    ring
  have h6: x 6 = b := by
    specialize h 4
    norm_num at h
    simp [h0, h1, h2, h3, h4, h5] at h
    rw [h]
    field_simp
    ring

  -- then we show that x n is periodic with period 5 by induction
  have f: ∀ n, x (n + 5) = x n := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    by_cases ln: n = 0
    .   -- base case: n = 0

        simp [ln]
        simp [h5,h0]
    .
        by_cases l: n = 1
        .   -- base case: n = 1

            simp [l]
            simp [h6,h1]

        .    -- inductive case: 2 ≤ n

          replace l: 2 ≤ n := by omega
          have f1:= ih (n - 1)
          have o: n - 1 < n := by omega
          simp [o] at f1
          clear o ln
          rw [show n - 1 + 5 = n + 4 by omega] at f1
          have f2:= ih (n - 2)
          have o: n - 2 < n := by omega
          simp [o] at f2
          clear o
          rw [show n - 2 + 5 = n + 3 by omega] at f2
          have h':= h
          specialize h (n + 3)
          rw [show n + 3 + 2 = n + 5 by omega] at h
          rw [show n + 3 + 1 = n + 4 by omega] at h
          rw [h]
          simp [f1,f2]
          specialize h' (n - 2)
          rw [show n - 2 + 2 = n by omega] at h'
          rw [show n - 2 + 1 = n - 1 by omega] at h'
          symm at h'
          exact h'

  -- then we can show that x (5 * k + 3) = x 3 for all k
  have g: ∀ k, x (5 * k + 3) = x 3 := by
    intro k
    induction' k with k ih
    .   -- base case: k = 0

        simp
    .
        -- inductive case: k > 0

        rw [show 5 * (k + 1) + 3 = 5 * k + 3 + 5 by omega]
        specialize f (5 * k + 3)
        rw [f]
        exact ih

  -- finally, we compute x 1998
  specialize g 399
  norm_num at g
  simp [h3] at g
  exact g
