import Mathlib

/-For which values of $k$ does the quadratic $kx^2 - 3kx + 4k + 7 = 0$ have real roots?-/
theorem algebra_18932 (k : ℝ) (hk : k ≠ 0):
  (∃ x : ℝ, k * x ^ 2 - 3 * k * x + 4 * k + 7 = 0) ↔ k ≥ -4 ∧ k < 0 := by
    constructor
    · -- if the quadratic $kx^2 - 3kx + 4k + 7 = 0$ have real roots,
      -- its discriminant must be nonnegative.
      -- \[(-3k)^2 - 4(k)(4k + 7) \ge 0.\]This expands as $-7k^2 - 28k \ge 0.$  This is equivalent to $k^2 + 4k \le 0,$ which factors as $k(k + 4) \le 0.$  The solution to this inequality is $-4 \le k \le 0.$  However, if $k = 0,$ then the given equation is not quadratic, so the set of $k$ which works is $\boxed{[-4,0)}.$
      intro ⟨x, hx⟩
      replace hx : k * (x * x) + (-3*k) * x + (4 * k + 7) = 0 := by nlinarith
      have := (quadratic_eq_zero_iff_discrim_eq_sq hk x).1 hx
      have : 0 ≤ discrim k (-3*k) (4*k + 7) := by nlinarith
      simp [discrim] at this
      have : k * (k + 4) ≤ 0 := by nlinarith
      simp [mul_nonpos_iff] at this
      rcases this with h | h
      · have ⟨_, _⟩ := h
        linarith
      · exact ⟨by linarith, lt_of_le_of_ne h.1 hk⟩
    · -- Check that if k ≥ -4 ∧ k < 0, the quadratic actually has real roots.
      intro ⟨h1, h2⟩
      suffices ∃ x, k * (x * x) + (-3*k) * x + (4 * k + 7) = 0 by
        obtain ⟨x, hx⟩ := this
        use x
        nlinarith
      apply exists_quadratic_eq_zero hk
      simp [discrim]
      use Real.sqrt ((3 * k) ^ 2 - 4 * k * (4 * k + 7))
      have : 0 ≤ (3 * k) ^ 2 - 4 * k * (4 * k + 7) := by nlinarith
      simp [←pow_two, Real.sq_sqrt this]
