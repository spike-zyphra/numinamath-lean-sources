import Mathlib

open Real

/- ## Task Condition

Find the derivative.
$$
y=\left(3 x^{2}-4 x+2\right) \sqrt{9 x^{2}-12 x+3}+(3 x-2)^{4} \cdot \arcsin \frac{1}{3 x-2}, 3 x-2>0
$$
 -/
theorem calculus_124492 {f f' : ℝ → ℝ}
    (hf : ∀ x, f x = (3 * x ^ 2 - 4 * x + 2) * sqrt (9 * x ^ 2 - 12 * x + 3) + (3 * x - 2) ^ 4 * arcsin (1 / (3 * x - 2)))
    (hf' : ∀ x, f' x = 12 * (3 * x - 2) ^ 3 * arcsin (1 / (3 * x - 2))) :
    ∀ x, x > 1 → HasDerivAt f (f' x) x := by
  intro x hx
  -- Define g n x = (3 * x - 2)^n.
  set g : ℕ → ℝ → ℝ := fun n x => (3 * x - 2)^n
  -- Show that the derivative of g n x is 3 * n * g (n - 1) x.
  have hdg n x : HasDerivAt (g n) (3 * n * g (n - 1) x) x := by
    rw [show 3 * n * g (n - 1) x = n * g (n - 1) x * (3 * 1) by ring]
    apply HasDerivAt.pow
    apply HasDerivAt.sub_const
    apply HasDerivAt.const_mul
    exact hasDerivAt_id' x
  -- x > 1 implies that 0 < g 1 x, 0 < g 2 x - 1, and 1 / g 1 x ≠ ±1.
  have hineq0 : 0 < g 1 x := by dsimp [g]; linarith
  have hineq1 : g 1 x ≠ 0 := by linarith
  have hineq2 : 0 < g 2 x - 1 := by dsimp [g]; nlinarith
  have hineq3 : g 2 x - 1 ≠ 0 := by linarith
  have hineq4 : 1 / g 1 x ≠ -1 := by field_simp; simp [g, pow_one]; linarith
  have hineq5 : 1 / g 1 x ≠ 1 := by field_simp; simp [g, pow_one]; linarith
  -- We can write
  -- f x = (1 / 3) * ((g 2 x + 2) * √(g 2 x - 1)) + g 4 x * arcsin (1 / g 1 x).
  have hf_eq x : f x = (1 / 3) * ((g 2 x + 2) * √(g 2 x - 1)) + g 4 x * arcsin (1 / g 1 x) := by
    simp [g, hf]
    ring_nf
  -- It is enough to show that
  -- f' x = (1 / 3) * (3 * 2 * g 1 x * √(g 2 x - 1) + (g 2 x + 2) * (3 * 2 * g 1 x / (2 * √(g 2 x - 1))))
  --        + (3 * 4 * g 3 x * arcsin (1 / g 1 x) + g 4 x * ((1 / √(1 - (1 / g 1 x)^2)) * (-3 / g 1 x ^ 2))).
  suffices f' x = (1 / 3) * (3 * 2 * g 1 x * √(g 2 x - 1) + (g 2 x + 2) * (3 * 2 * g 1 x / (2 * √(g 2 x - 1))))
              + (3 * 4 * g 3 x * arcsin (1 / g 1 x) + g 4 x * ((1 / √(1 - (1 / g 1 x)^2)) * (-3 / g 1 x ^ 2))) by
    -- Show that the derivative of f is f' x by using properties of derivatives.
    rw [this, show f = fun x => (1 / 3) * ((g 2 x + 2) * √(g 2 x - 1)) + g 4 x * arcsin (1 / g 1 x) by ext x; simp [hf_eq]]
    apply HasDerivAt.add
    · apply HasDerivAt.const_mul
      apply HasDerivAt.mul
      · apply HasDerivAt.add_const
        exact hdg 2 x
      · apply HasDerivAt.sqrt
        · apply HasDerivAt.sub_const
          exact hdg 2 x
        · exact hineq3
    · apply HasDerivAt.mul
      · exact hdg 4 x
      · apply @HasDerivAt.comp (h₂ := arcsin) (h := fun x => 1 / g 1 x)
        · apply hasDerivAt_arcsin hineq4 hineq5
        · simp_rw [one_div]
          apply HasDerivAt.inv _ hineq1
          have := hdg 1 x
          simp [g] at this ⊢
          exact this
  symm
  calc
    -- Show that
    -- (1 / 3) * (3 * 2 * g 1 x * √(g 2 x - 1) + (g 2 x + 2) * (3 * 2 * g 1 x / (2 * √(g 2 x - 1))))
    --     = (2 * g 1 x * √(g 2 x - 1) ^ 2 + (g 2 x + 2) * g 1 x) / √(g 2 x - 1),
    -- 3 * 4 * g 3 x * arcsin (1 / g 1 x) = f' x, and
    -- g 4 x * ((1 / √(1 - (1 / g 1 x)^2)) * (-3 / g 1 x ^ 2))
    --     = (-3) * g 3 x / √(g 1 x ^ 2 * (1 - (1 / g 1 x ^ 2))).
    _ = (2 * g 1 x * √(g 2 x - 1) ^ 2 + (g 2 x + 2) * g 1 x) / √(g 2 x - 1) + (f' x + (-3) * g 3 x / √(g 1 x ^ 2 * (1 - (1 / g 1 x ^ 2)))) := by
      congrm ?_ + (?_ + ?_)
      · field_simp
        ring_nf
        rw [show 3 - x * 12 + x ^ 2 * 9 = g 2 x - 1 by ring]
        suffices √(g 2 x - 1) ^ 3 = (g 2 x - 1) * √(g 2 x - 1) by rw [this]; ring
        rw [show 3 = 2 + 1 by norm_num, pow_add, sq_sqrt (by linarith), pow_one]
      · simp [g, hf']
        norm_num
      · rw [sqrt_mul (by positivity)]
        rw [sqrt_sq (by positivity)]
        rw [show ∀ a b c : ℝ, a * (b * (-3 / c)) = -3 * (a / c) * b by intros; ring]
        rw [show ∀ a b c : ℝ, -3 * a / (b * c) = -3 * (a / b) * (1 / c) by intros; ring]
        rw [div_pow, show (1 : ℝ) ^ 2 = 1 by norm_num]
        congrm -3 * ?_ * _
        field_simp
        ring
    -- Show that
    -- √(g 2 x - 1) ^ 2 = g 2 x - 1 and g 1 x ^ 2 * (1 - 1 / g 1 x ^ 2) = g 2 x - 1.
    _ = (2 * g 1 x * (g 2 x - 1) + (g 2 x + 2) * g 1 x) / √(g 2 x - 1) + (f' x + -3 * g 3 x / √(g 2 x - 1)) := by
      rw [sq_sqrt (by linarith)]
      congr
      field_simp
      ring
    -- We get the following expression:
    -- (2 * g 1 x * (g 2 x - 1) + (g 2 x + 2) * g 1 x - 3 * g 3 x) / √(g 2 x - 1) + f' x.
    _ = (2 * g 1 x * (g 2 x - 1) + (g 2 x + 2) * g 1 x - 3 * g 3 x) / √(g 2 x - 1) + f' x := by
      ring
    -- It is easy to show that
    -- 2 * g 1 x * (g 2 x - 1) + (g 2 x + 2) * g 1 x - 3 * g 3 x = 0.
    _ = f' x := by
      ring