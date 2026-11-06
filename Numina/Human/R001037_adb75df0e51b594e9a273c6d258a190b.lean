import Mathlib

/- If $n$ is a constant and if there exists a unique value of $m$ for which the quadratic equation $x^2 + mx + (m+n) = 0$ has one real solution, then find $n$. -/
theorem algebra_20054 {n : ℝ} (hn : ∃! m : ℝ, ∃! x : ℝ, x^2 + m * x + (m + n) = 0) : n = -1 := by
  rcases hn with ⟨m, ⟨hmeq, hmu⟩⟩
  -- For any $k$, if quadratic equation $x ^ 2 + k * x + (k + n) = 0$ has one real solution, then $k ^ 2 - 4 * (k + n) = 0$
  have discrimeq : ∀ k : ℝ, (∃! x : ℝ, x ^ 2 + k * x + (k + n) = 0) → k ^ 2 - 4 * (k + n) = 0 := by
    intro k hk
    rcases hk with ⟨x, hxeq, hxu⟩
    -- Let $x$ be a solution of $x ^ 2 + k * x + (k + n) = 0$
    have hxeq1 := hxeq
    rw [add_assoc] at hxeq
    apply eq_sub_of_add_eq at hxeq
    -- Then $-k - x$ is another solution of $x ^ 2 + k * x + (k + n) = 0$
    have eq : (-k - x) ^ 2 + k * (-k - x) + (k + n) = 0 := by
      ring_nf 
      rw [hxeq]
      ring_nf
    -- So $-k - x = x$
    have mid := hxu (-k - x) eq
    apply eq_add_of_sub_eq at mid
    apply congrArg (fun a ↦ a / 2) at mid
    ring_nf at mid
    -- rewrite $x ^ 2 + k * x + (k + n) = 0$ with $x = -k / 2$
    rw [← mid] at hxeq1
    apply congrArg (fun a ↦ a * 4) at hxeq1
    ring_nf at hxeq1
    rw [sub_add] at hxeq1
    apply eq_add_of_sub_eq at hxeq1
    rw [mul_comm, add_mul, hxeq1]
    ring_nf
  -- $m ^ 2 - 4 * (m + n) = 0$
  have eqmn := discrimeq m hmeq
  -- There is a unique $m$ such that $m ^ 2 - 4 * (m + n) = 0$
  have equmn : ∃! l : ℝ, l ^ 2 - 4 * (l + n) = 0 := by
    use m
    constructor
    exact eqmn
    intro y hy
    -- If the discriminant $y ^ 2 - 4 * (y  + n) = 0$, then $x ^ 2 + y * x + (y + n) = 0$ has one real solution
    have usol : ∃! x, x ^ 2 + y * x + (y + n) = 0 := by
      -- $-y / 2$ is a solution
      use -y / 2
      constructor
      apply eq_add_of_sub_eq at hy
      field_simp
      rw [← pow_two, hy]
      ring_nf
      -- If $z$ is a solution then $z = -y / 2$
      intro z hz
      apply congrArg (fun a ↦ 4 * a) at hz
      apply eq_of_sub_eq_zero at hy
      rw [mul_add, ← hy] at hz
      have mid : 4 * (z ^ 2 + y * z) + y ^ 2 = (2 * z + y) ^ 2 := by
        ring_nf
      rw [mid] at hz
      simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at hz
      linarith
    -- So $y = m$
    exact hmu y usol
  -- The discriminant of $m ^ 2 - 4 * (m + n) = 0$ is zero, so $n = -1$
  rcases equmn with ⟨l, hleq, hlu⟩
  have eq : (4 - l) ^ 2 - 4 * ((4 - l) + n) = 0 := by
    ring_nf
    apply eq_add_of_sub_eq at hleq
    rw [hleq]
    ring_nf
  have eq2 := hlu (4 - l) eq
  have leq : l = 2 := by
    linarith
  rw [leq] at hleq
  linarith