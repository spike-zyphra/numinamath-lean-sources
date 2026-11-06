import Mathlib

theorem algebra_288531 (t k : ℝ) (ht : t ≠ 0) (hk : k ≠ 0)
    (h1 : (k + 4) * (5 + 7) = -1) (h2 : (k - 11) * (k - 15) = -1) :
    k = 5 := by

  -- First equation `h1` expands to: ` (k + 4) * 12 = -1 `.

  -- Expanding:
  -- `12k + 48 = -1`.

  -- Rearranged:
  -- `12k = -1 - 48`.
  -- `12k = -49`.
  -- `k = -49/12`.

  -- Now the second equation: ` (k - 11) * (k - 15) = -1 `.

  -- Expanding: ` k^2 - 26k + 165 = -1 `.

  -- Rearranged: ` k^2 - 26 k + 166 = 0 `.

  -- We need to solve them together. But they are a system of inconsistent equations.
  -- Therefore, without any solution, the statement is inconsistent, so anything is a consequence (ex falso quodlibet)

  -- We can thus use Lean's non linear solver to handle inconsistency

  have eq1 : 12 * k + 48 = -1 := by
    nlinarith

  have h3 : 12 * k = -49 := by
    linarith

  have hk1 : k = -49 / 12 := by
    linarith

  rw [hk1] at h2

  nlinarith