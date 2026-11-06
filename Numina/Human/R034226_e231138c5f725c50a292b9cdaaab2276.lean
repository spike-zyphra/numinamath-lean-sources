import Mathlib
set_option maxHeartbeats 800000
/- 11.1. Find all solutions of the system of equations in real numbers:

$$
\left\{\begin{array}{c}
x y+z+t=1 \\
y z+t+x=3 \\
z t+x+y=-1 \\
t x+y+z=1
\end{array}\right.
$$ -/
theorem algebra_253784 (x y z t : ℝ)
    (h₀ : x * y + z + t = 1) (h₁ : y * z + t + x = 3) (h₂ : z * t + x + y = -1)
    (h₃ : t * x + y + z = 1) :
    (x, y, z, t) = (1, 0, -1, 2) := by
  -- First, we derive that (x-1)*(t-y) = 0, which gives us two cases to consider
  have eq1 : (x - 1) * (t - y) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq1) with hx1 hty
  · -- Case 1: x = 1
    have hx : x = 1 := by linarith
    -- Substitute x = 1 into the original equations to simplify them
    have h0' : y + z + t = 1 := by
      rw [hx] at h₀
      nlinarith
    have h1' : y * z + t = 2 := by
      rw [hx] at h₁
      nlinarith
    have h2' : z * t + y = -2 := by
      rw [hx] at h₂
      nlinarith
    -- Express t in terms of y and z
    have ht : t = 1 - y - z := by linarith
    rw [ht] at h2'
    -- Prove that z = -1
    have hz : z = -1 := by
      -- Derive several equations that will help us determine z
      have eq2 : y * (z - 1) = z + 1 := by
        nlinarith
      have eq3 : -y * z + y - z^2 + z = -2 := by
        nlinarith
      have eq4 : -y * z + y = -z - 1 := by
        nlinarith
      -- Show that z² = 1, which means z = 1 or z = -1
      have hz2 : z^2 = 1 := by
        nlinarith [eq3, eq4]
      have h1 : z = 1 ∨ z = -1 := by
        have hz2 : z^2 = 1 := by nlinarith
        have : z = 1 ∨ z = -1 := by
          rw [sq_eq_one_iff] at hz2
          exact hz2
        exact this
      cases' h1 with hz1 hz2
      · -- Show that z = 1 leads to a contradiction
        have hz1 : z = 1 := by assumption
        rw [hz1] at eq2
        nlinarith
      · -- Therefore, z = -1 is the only solution
        exact hz2
    -- Prove that y = 0
    have hy : y = 0 := by
      rw [hz] at h1'
      nlinarith
    -- Prove that t = 2
    have ht2 : t = 2 := by
      rw [hz, hy] at h0'
      linarith
    -- Combine all results to show that (x,y,z,t) = (1,0,-1,2)
    exact Prod.ext hx (Prod.ext hy (Prod.ext hz ht2))
  · -- Case 2: t = y
    have ht_eq_y : t = y := by linarith
    -- Substitute t = y into the original equations
    have h1 := h₁
    have h2 := h₂
    rw [ht_eq_y] at h₁ h₂
    simp
    -- Prove that the solution is still (1,0,-1,2) using perfect square inequalities
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 0), sq_nonneg (z + 1), sq_nonneg (t - 2)]
