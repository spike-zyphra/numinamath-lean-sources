import Mathlib

open Real

/- Let $x_{0}=10^{9}, x_{n}=\frac{x_{n-1}^{2}+2}{2 x_{n-1}}$. Prove that $0 < x_{36}-\sqrt{2} < 10^{-9}$. -/
theorem algebra_227390 (x : ℕ → ℝ) (hx0 : x 0 = 10 ^ 9)
    (hxn : ∀ n, x (n + 1) = (x n ^ 2 + 2) / (2 * x n)) :
    0 < x 36 - sqrt 2 ∧ x 36 - sqrt 2 < 10 ^ (-9 : ℤ) := by
  -- Show that 0 < x n for all n.
  have h_pos n : 0 < x n := by
    -- Proof by induction.
    induction n with
    -- 0 < x 0 = 10^9.
    | zero => simp [hx0]
    | succ n ih =>
      -- x (n + 1) = (x n ^ 2 + 2) / (2 * x n) and x n > 0 imply that x (n + 1) > 0.
      rw [hxn]
      positivity
  -- Show that x (n + 1) - √2 = (1 / 2) * (x n - √2)^2 / x n for all n.
  have h_eq n : x (n + 1) - √2 = (1 / 2) * (x n - √2)^2 / x n := by
    rw [hxn]
    have := h_pos n
    field_simp
    -- Simplify the expression x(n + 1) - √2 and get the following goal
    --x n ^ 2 - 2 * x n * √2 + 2 = (x n - √2) ^ 2.
    ring_nf
    simp
    ring
  -- Show that 0 < x n - √2 for all n
  have h0 n : 0 < x n - √2 := by
    -- Proof by induction.
    induction n with
    -- √2 < 10^9 = x 0.
    | zero =>
      simp [hx0]
      rw [← sq_lt_sq₀ (by positivity) (by positivity)]
      norm_num
    | succ n ih =>
      -- We have x (n + 1) - √2 = (1 / 2) * (x n - √2)^2 / x n > 0
      -- (because x n - √2 > 0 by the induction hypothesis and x n > 0).
      rw [h_eq]
      have := h_pos n
      positivity
  -- Show taht x (n + 1) - √2 < (1 / 2) * (x n - √2) for all n.
  have h1 n : x (n + 1) - √2 < (1 / 2) * (x n - √2) := by
    rw [← mul_one (1 / 2 * _)]
    -- We have x (n + 1) - √2 = (1 / 2) * (x n - √2) * ((x n - √2) / x n).
    rw [h_eq, show 1 / 2 * (x n - √2)^2 / x n = (1 / 2) * (x n - √2) * ((x n - √2) / x n) by ring]
    -- It is enough to show that (x n - √2) / x n < 1 for all n.
    gcongr
    · have := h0 n
      positivity
    rw [div_lt_one (h_pos n)]
    -- x n - √2 < x n.
    linarith [show 0 < √2 by positivity]
  -- Show that x n - √2 < (1 / 2)^n * x 0 for all n.
  have h2 n : x n - √2 < (1 / 2)^n * x 0 := by
    -- Proof by induction.
    induction n with
    -- x 0 - √2 < x 0.
    | zero => simp
    | succ n ih =>
      -- x (n + 1) - √2 < (1 / 2) * (x n - √2) < (1 / 2) * (1 / 2)^n * x 0.
      calc
        x (n + 1) - √2 < (1 / 2) * (x n - √2) := h1 n
        _ < (1 / 2) * ((1 / 2)^n * x 0) := by linarith
        _ = (1 / 2)^(n + 1) * x 0 := by ring
  -- Show that x (n + 1) - √2 < (1 / 2) * (x n - √2)^2 for all n.
  have h3 n : x (n + 1) - √2 < (1 / 2) * (x n - √2)^2 := by
    rw [show 1 / 2 * (x n - √2)^2 = 1 / 2 * (x n - √2)^2 / 1 by rw [div_one], h_eq]
    have := h0 n
    -- We have x (n + 1) - √2 = (1 / 2) * (x n - √2)^2 / x n.
    -- So it is enough to show that 1 < x n for all n.
    gcongr
    -- 1 < x n because √2 < x n.
    suffices √1 < √2 by linarith [sqrt_one]
    apply sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- 0 < x 36 - √2 follows from h0.
  refine ⟨h0 36, ?_⟩
  calc
    -- We have x 36 - √2 < 1 / 2 * (x 35 - √2)^2.
    -- Apply this inequality recursively to x 35 - √2, ..., x 31 - √2.
    x 36 - √2 < 1 / 2 * (x 35 - √2)^2 := h3 35
    _ < 1 / 2 * (1 / 2 * (x 34 - √2)^2)^2 := by
      have := h0 35
      have := h3 34
      gcongr
    _ < 1 / 2 * (1 / 2 * (1 / 2 * (x 33 - √2)^2)^2)^2 := by
      have := h0 34
      have := h3 33
      gcongr
    _ < 1 / 2 * (1 / 2 * (1 / 2 * (1 / 2 * (x 32 - √2)^2)^2)^2)^2 := by
      have := h0 33
      have := h3 32
      gcongr
    _ < 1 / 2 * (1 / 2 * (1 / 2 * (1 / 2 * (1 / 2 * (x 31 - √2)^2)^2)^2)^2)^2 := by
      have := h0 32
      have := h3 31
      gcongr
    _ < 1 / 2 * (1 / 2 * (1 / 2 * (1 / 2 * (1 / 2 * (1 / 2 * (x 30 - √2)^2)^2)^2)^2)^2)^2 := by
      have := h0 31
      have := h3 30
      gcongr
    -- Show that x 30 - √2 < 1.
    _ < 1 / 2 * (1 / 2 * (1 / 2 * (1 / 2 * (1 / 2 * (1 / 2 * 1^2)^2)^2)^2)^2)^2 := by
      have := h0 30
      gcongr
      -- We have x 30 - √2 < (1 / 2)^30 * x 0 = (1 / 2)^30 * 10^9 < 1.
      apply lt_trans (h2 30)
      norm_num [hx0]
    -- We get x 36 - √2 < (1 / 2)^63 < 10^-9.
    _ = (1 / 2)^63 := by ring
    _ < 10^(-9 : ℤ) := by
      norm_num