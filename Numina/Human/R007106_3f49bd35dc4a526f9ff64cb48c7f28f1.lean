import Mathlib

/-Let $a, b, c$ be non-negative real numbers such that $a b+b c+c a=3$. Suppose that

$$
a^{3} b+b^{3} c+c^{3} a+2 a b c(a+b+c)=\frac{9}{2}
$$

What is the minimum possible value of $a b^{3}+b c^{3}+c a^{3}$ ?-/
theorem algebra_609698 :
    IsLeast {k : ℝ | ∃a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a * b + b * c + c * a = 3 ∧
    a ^ 3 * b + b ^ 3 * c + c ^ 3 * a + 2 * a * b * c * (a + b + c) = 9 / 2 ∧
    k = a * b ^ 3 + b * c ^ 3 + c * a ^ 3} 18 := by
  -- simplify the conclusion
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩ -- divide the conclusion into two parts
  . -- show that the minimum possible value of a * b ^ 3 + b * c ^ 3 + c * a ^ 3 is 18
    use (√6 / 2) -- let a = √6 / 2
    simp [show 0 ≤ √6 / 2 by apply div_nonneg; apply Real.sqrt_nonneg; norm_num]
    use √6 -- let b = √6
    simp
    use 0 -- let c = 0
    norm_num
    ring_nf
    -- simplify the equation by √6 ^ 2 = 6 and √6 ^ 4 = 36
    simp [show √6 ^ 2 = 6 by norm_num]
    norm_num
    -- show that √6 ^ 4 = 36
    have h : √6 ^ 4 = 36 := by
      calc
        √6 ^ 4 = (√6 ^ 2) ^ 2 := by ring_nf
        _ = 36 := by norm_num
    simp [h]
    norm_num
  . -- show that 18 ≤ k
    intro k a ha b hb c hc hs2 eq hk
    -- show that 0 ≤ ∑ ab(b + c - 2a) ^ 2
    have ineq : 0 ≤ a * b * (b + c - 2 * a) ^ 2 + b * c * (c + a - 2 * b) ^ 2 + c * a * (a + b - 2 * c) ^ 2 := by
      positivity

    -- suppose s2 s31 s22 s13 s111
    set s2 : ℝ := a * b + b * c + c * a
    set s31 : ℝ := a ^ 3 * b + b ^ 3 * c + c ^ 3 * a with hs31
    set s13 : ℝ := a * b ^ 3 + b * c ^ 3 + c * a ^ 3 with hs13
    set s111 : ℝ := a * b * c * (a + b + c) with hs111
    set s22 : ℝ := a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 with hs22
    -- expand ineq
    replace ineq : 0 ≤ s13 + 4 * s31 - 4 * s22 - s111 := by
      rw [hs13, hs31, hs22, hs111]
      ring_nf at ineq ⊢
      exact ineq

    -- calculate that s13 - 4 * s2 ^ 2 ≥ -18
    replace ineq : s13 - 4 * s2 ^ 2 ≥ -18 := by
      calc
        s13 - 4 * s2 ^ 2 = s13 - 4 * s22 - 8 * s111 := by ring_nf
        -- exactly 0 ≤ s111
        _ ≥ s13 - 4 * s22 - 9 * s111 := by linarith only [show 0 ≤ s111 by positivity]
        _ ≥ -4 * (s31 + 2 * s111) := by linarith only [ineq]
        _ = -4 * (9 / 2) := by linarith
        _ = -18 := by norm_num
    rw [hs2, <-hk] at ineq
    linarith only [ineq]