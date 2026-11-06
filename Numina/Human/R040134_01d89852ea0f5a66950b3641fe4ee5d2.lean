import Mathlib

/-Find the largest value of $\frac{y}{x}$ for pairs of real numbers $(x,y)$ that satisfy
\[(x - 3)^2 + (y - 3)^2 = 6.\]-/
theorem algebra_18767 : IsGreatest {(k : ℝ) | ∃ x y : ℝ, y = k * x ∧ (x - 3)^2 + (y - 3)^2 = 6} (3 + 2 * √2) := by
  constructor
  · -- when x = 2 - √2, y = 2 + √2, k = 3 + 2 * √2.
    simp
    use 2 - √2
    ring_nf
    have h1 : √2 ^ 3 = √2 * 2 := by
      rw [show 3 = 2 + 1 by ring, pow_add]
      simp
      ring
    have h2 : √2 ^ 4 = 4 := by
      rw [show 4 = 2 + 2 by ring, pow_add, Real.sq_sqrt (by simp)]
      ring
    rw [h1, h2, Real.sq_sqrt (by simp), mul_assoc]
    norm_num
  · -- Let $k = \frac{y}{x}.$  Then $y = kx,$ so
    -- \[(x - 3)^2 + (kx - 3)^2 = 6.\]Expressing this as a quadratic in $x,$ we get
    -- \[(k^2 + 1) x^2 - (6k + 6) k + 12 = 0.\]
    intro k h
    simp at h
    obtain ⟨x, hx⟩ := h
    have h1 : (k^2 + 1) * (x * x) + -(6 * k + 6) * x + 12 = 0 := by
      nlinarith
    -- This quadratic has real roots when its discriminant is nonnegative:
    -- \[(6k + 6)^2 - 4(k^2 + 1)(12) \ge 0.\]This simplifies to $k^2 - 6k + 1 \le 0.$
    have := discrim_eq_sq_of_quadratic_eq_zero h1
    have : 0 ≤  discrim (k ^ 2 + 1) (-(6 * k + 6)) 12 := this ▸ (by positivity)
    simp [discrim] at this
    -- The roots of the corresponding equation $k^2 - 6k + 1 = 0$ are
    -- \[3 \pm 2 \sqrt{2},\]so the solution to $k^2 - 6k + 1 \le 0$ is $3 - 2 \sqrt{2} \le k \le 3 + 2 \sqrt{2}.$

    have h2 : k^2 - 6 * k + 1 ≤ 0 := by nlinarith
    let f : ℝ → ℝ := fun x => x^2 - 6*x + 1
    have hf (x y : ℝ) : f x ≤ f y → (x - 3)^2 ≤ (y - 3)^2 := by
      intro hxy
      dsimp [f] at hxy
      nlinarith
    have aux : f k ≤ f (3 + 2 * √2) := by
      have : f (3 + 2 * √2) = 0 := by
        simp [f]
        ring_nf
        simp
        ring
      rw [this]
      dsimp [f]
      norm_num [h2]
    -- Therefore, the largest possible value of $k = \frac{y}{x}$ is $\boxed{3 + 2 \sqrt{2}}.$
    have := hf k (3 + 2 * √2) aux
    contrapose! this
    apply pow_lt_pow_left₀ <;> try nlinarith
    norm_num
