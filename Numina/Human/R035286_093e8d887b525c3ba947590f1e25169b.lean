import Mathlib
open Real
/- Let $a > 0$. If the system $$\begin{cases} a^x + a^y + a^z = 14 - a \\ x + y + z = 1 \end{cases}$$ has a solution in real numbers, prove that $a \le 8$. -/
theorem inequalities_61617 (a : ℝ) (ha : 0 < a) (h : ∃ x y z : ℝ, a ^ x + a ^ y + a ^ z = 14 - a ∧ x + y + z = 1) : a ≤ 8 := by
  -- Extract the solution values from the existence hypothesis
  rcases h with ⟨x, y, z, ⟨h, h2⟩⟩
  -- Prove a key inequality: for positive real numbers, x³ + y³ + z³ - 3xyz ≥ 0
  have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
    intro x y z hx hy hz
    -- Use the identity: x³ + y³ + z³ - 3xyz = (1/2)(x+y+z)((x-y)² + (y-z)² + (z-x)²)
    have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
    rw [h1]
    positivity
  -- Transform the inequality using cube roots to get a new inequality
  replace h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
    intro x y z hx hy hz
    -- Apply the previous inequality to cube roots of x, y, z
    specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
    -- Simplify the expressions using power rules
    rw [show (x ^ ((1 : ℝ) / 3)) ^ 3 = (x ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
    rw [show (y ^ ((1 : ℝ) / 3)) ^ 3 = (y ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
    rw [show (z ^ ((1 : ℝ) / 3)) ^ 3 = (z ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
    rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
    rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
    rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
    rw [show (1 : ℝ) / 3 * 3 = 1 by ring_nf] at h1
    rw [Eq.symm (Real.mul_rpow (by linarith) (by linarith))] at h1
    rw [Eq.symm (Real.mul_rpow (by positivity) (by linarith))] at h1
    simp at h1
    simp
    linarith
  -- Apply the inequality to a^x, a^y, a^z
  specialize h1 (a ^ x) (a ^ y) (a ^ z) (by positivity) (by positivity) (by positivity)
  -- Use power rules to combine exponents
  rw [Eq.symm (Real.rpow_add (by positivity) x y)] at h1
  rw [Eq.symm (Real.rpow_add (by positivity) (x + y) z)] at h1
  -- Substitute the given equations
  rw [h, h2] at h1
  rw [show a ^ (1 : ℝ) = a by simp] at h1
  -- Define t as the cube root of a
  set t:= a ^ ((1 : ℝ) / 3) with ht
  clear_value t
  -- Prove that a = t³
  have ht1 : a = t ^ 3:= by
    rw [show t ^ 3 = t ^ (3 : ℝ) by norm_cast]
    subst t
    rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))]
    simp
  -- Show that t is positive
  replace ha : t > 0:= by subst t ; positivity
  subst a
  clear h ht
  -- Prove that 2 - t ≥ 0
  have h : 2 - t ≥ 0:= by
    have g1 : (t + 1) ^ 2 + 6 > 0:= by positivity
    replace h1 : ((t + 1) ^ 2 + 6) * (2 - t) ≥ 0:= by linarith
    exact nonneg_of_mul_nonneg_right h1 g1
  -- Final step to prove t ≤ 2, which implies a ≤ 8
  replace h : ((t + 1) ^ 2 + 3) * (2 - t) ≥ 0:= by positivity
  linarith
