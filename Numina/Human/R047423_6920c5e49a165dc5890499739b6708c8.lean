import Mathlib
/-$\begin{array}{l}\text { Given } \frac{x}{y+z}=\frac{y}{z+x}=\frac{z}{x+y} \\ =k \text {. Find the value of } k \text { . }\end{array}$
-/
theorem algebra_308562 (x y z k : ℝ)
  (hx : x / (y + z) = k)(hyz : y + z ≠ 0)
  (hy : y / (z + x) = k)(hzx : z + x ≠ 0)
  (hz : z / (x + y) = k)(hxy : x + y ≠ 0) :
  (x + y + z ≠ 0 → k = 1 / 2) ∧ (x + y + z = 0 → k = -1) := by
  -- Step 1: Get linear equations from the proportion relations
  have eq1 : x = k * (y + z) := by 
    rw [← hx]
    field_simp [hyz]
  have eq2 : y = k * (z + x) := by 
    rw [← hy]
    field_simp [hzx]
  have eq3 : z = k * (x + y) := by 
    rw [← hz]
    field_simp [hxy]

  -- Step 2: Add the three equations to get an equation about k
  have sum_eq : x + y + z = k * 2 * (x + y + z) := by
    have h1 : x + y + z = k * (y + z) + k * (z + x) + k * (x + y) := by
      linarith [eq1, eq2, eq3]
    have h2 : k * (y + z) + k * (z + x) + k * (x + y) = 2 * k * (x + y + z) := by
      ring
    linarith [h1, h2]
    

  -- Case analysis
  constructor
  · intro hne
    -- When x + y + z ≠ 0, divide both sides by 2 * (x + y + z) to get 1 = 2 * k
    have h₁ : k * 2 = 1 := by
      apply mul_left_cancel₀ hne
      linarith
    linarith

  · intro heq
    -- When x + y + z = 0, y + z = -x, substitute into the equation to get k = x/(-x) = -1
    have h : x = -(y + z) := by linarith
    rw [h] at hx
    rw [← hx]
    field_simp
