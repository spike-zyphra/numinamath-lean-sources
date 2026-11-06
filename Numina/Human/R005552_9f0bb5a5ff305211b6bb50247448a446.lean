import Mathlib

/- A function $f(x, y, z)$ is linear in $x, y$, and $z$ such that $f(x, y, z)=\frac{1}{x y z}$ for $x, y, z \in\{3,4\}$. What is $f(5,5,5)$ ?-/
theorem algebra_608785 (f : ℝ × ℝ × ℝ → ℝ) (hf1 :IsLinearMap ℝ f)
  (hf2 : ∀ x y z ,x ∈ [3,4] → y ∈ [3,4] → z ∈ [3,4] → f (x, y, z) = 1 / (x * y * z)) :
  f (5, 5, 5) = 1 / 216 := by
  -- Notice that $f(x, y, 5)=2 f(x, y, 4)-$ $f(x, y, 3)$.
  have : ((5,5,5) : ℝ × ℝ × ℝ) = (2 : ℝ) • (5,5,4) + (-1 : ℝ) • (5,5,3) := by norm_num
  rw [this,hf1.map_add,hf1.map_smul,hf1.map_smul]
  -- Notice that $f(x, 5, z)=2 f(x, 4, z)-$ $f(x, 3, z)$.
  have : ((5,5,4) : ℝ × ℝ × ℝ) = (2 : ℝ) • (5,4,4) + (-1 : ℝ) • (5,3,4) := by norm_num
  rw [this,hf1.map_add,hf1.map_smul,hf1.map_smul]
  -- Notice that $f(5, y, z)=2 f(4, y, z)-$ $f(3, y, z)$.
  have : ((5,4,4) : ℝ × ℝ × ℝ) = (2 : ℝ) • (4,4,4) + (-1 : ℝ) • (3,4,4) := by norm_num
  rw [this,hf1.map_add,hf1.map_smul,hf1.map_smul]
  -- Similar to the above, we can get the following.
  have : ((5,3,4) : ℝ × ℝ × ℝ) = (2 : ℝ) • (4,3,4) + (-1 : ℝ) • (3,3,4) := by norm_num
  rw [this,hf1.map_add,hf1.map_smul,hf1.map_smul]
  have : ((5,5,3) : ℝ × ℝ × ℝ) = (2 : ℝ) • (5,4,3) + (-1 : ℝ) • (5,3,3) := by norm_num
  rw [this,hf1.map_add,hf1.map_smul,hf1.map_smul]
  have : ((5,4,3) : ℝ × ℝ × ℝ) = (2 : ℝ) • (4,4,3) + (-1 : ℝ) • (3,4,3) := by norm_num
  rw [this,hf1.map_add,hf1.map_smul,hf1.map_smul]
  have : ((5,3,3) : ℝ × ℝ × ℝ) = (2 : ℝ) • (4,3,3) + (-1 : ℝ) • (3,3,3) := by norm_num
  rw [this,hf1.map_add,hf1.map_smul,hf1.map_smul]
  -- We can get the values from the given condition.
  simp [hf2] ;norm_num