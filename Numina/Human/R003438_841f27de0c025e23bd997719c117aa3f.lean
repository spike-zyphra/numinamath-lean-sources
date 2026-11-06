import Mathlib

/- The real numbers $p, q, r$ are pairwise distinct, and they satisfy


$$

q=p(4-p), \quad r=q(4-q), \quad p=r(4-r) .

$$


What can be the value of $p+q+r$? -/
theorem algebra_182203 {p q r : ℝ} (hqr : q ≠ r) (hpr : p ≠ r) (hqr' : q ≠ p)
    (h1 : q = p * (4 - p)) (h2 : r = q * (4 - q)) (h3 : p = r * (4 - r)) :
    p + q + r = 6 ∨ p + q + r = 7 := by
  -- Define x, y, and z
  let x := q - 2
  let y := p - 2
  let z := r - 2
  -- Translate h1, h2, and h3 into x, y, z
  have h1' : x = 2 - y ^ 2 := by unfold x y; linarith
  have h2' : y = 2 - z ^ 2 := by unfold y z; linarith
  have h3' : z = 2 - x ^ 2 := by unfold z x; linarith
  -- Show that x is not equal to 1 or -2
  have hx : x ≠ 1 ∧ x ≠ -2 := by
    constructor <;>
    · -- Use contradiction
      by_contra hx
      rw [hx] at h3'
      -- It would imply that x = z which contradicts hqr
      have : x = z := by linarith
      unfold x z at this
      simp at this
      exact hqr this
  rw [h2', h3'] at h1'
  -- Factor h1'
  have h : (x - 1) * (x + 2) * (x ^ 3 - 3 * x - 1) * (x ^ 3 - x ^ 2 - 2 * x + 1) = 0 := by linarith
  repeat rw [mul_eq_zero] at h
  -- Casework on h
  rcases h with h | h
  · rcases h with h | h
    · rcases h with h | h
      · -- Case when x - 1 = 0 is impossible by hx
        exfalso
        exact hx.1 (show x = 1 by linarith)
      -- Case when x + 2 = 0 is impossible by hx
      exfalso
      exact hx.2 (show x = -2 by linarith)
    -- Case when x ^ 3 - x ^ 2 - 2 * x + 1 = 0
    -- In this case, p + q + r = 6
    left
    calc
      p + q + r = x + y + z + 6 := by unfold x y z; linarith
      _ = -1 * x * (x ^ 3 - 3 * x - 1) + 6 := by rw [h2', h3']; linarith
      _ = 6 := by rw [h]; linarith
  -- Case when x ^ 3 - x ^ 2 - 2 * x + 1 = 0
  -- In this case, p + q + r = 7
  right
  calc
    p + q + r = x + y + z + 6 := by unfold x y z; linarith
    _ = -1 * (x + 1) * (x ^ 3 - x ^ 2 - 2 * x + 1) + 7 := by rw [h2', h3']; linarith
    _ = 7 := by rw [h]; linarith