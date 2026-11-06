import Mathlib

open Real Set

/- II. (16 points) Let $x, y \in \mathbf{R}$, and $x^{2}+y^{2}=2$, $|x| \neq|y|$. Find the minimum value of $\frac{1}{(x+y)^{2}}+\frac{1}{(x-y)^{2}}$. -/
theorem algebra_129152:
IsLeast { fxy | ∃ x y : ℝ, x^2 + y^2 = 2 ∧ abs x ≠ abs y ∧ fxy = 1 / (x + y)^2 + 1 / (x - y)^2 } 1 := by
  constructor
  -- existence is easy
  · simp
    use sqrt 2, 0
    norm_num
  unfold lowerBounds
  simp only [mem_setOf_eq, forall_exists_index, and_imp]
  intro lim x y hxy habs hlim; rw [hlim]; clear hlim
  -- now we can start working
  -- first we show that (x+y)^2+(x-y)^2=4
  have h0:=
    calc (x+y)^2+(x-y)^2
    _ = 2*(x^2+y^2) := by ring_nf
    _ = 4 := by rw [hxy]; norm_num
  -- two more mini lemmas to simplify for later
  have h1:(x+y)^2≠0 := by simp; intro h; have h':x=-y:=(by linarith);rw [h'] at habs; simp at habs
  have h2:(x-y)^2≠0 := by simp; intro h; have h':x=y:=(by linarith);rw [h'] at habs; simp at habs
  -- now we calculate
  calc 1 / (x + y) ^ 2 + 1 / (x - y) ^ 2
  _ = (4/4) * (1/ (x + y) ^ 2 + 1 / (x - y) ^ 2) := by norm_num
  _ = 1 / 4 * ((x+y)^2 + (x-y)^2) * (1/(x + y)^2 + 1/(x - y)^2) := by
    conv_lhs => lhs; lhs; rw [← h0]
    ring_nf
  _ = 1/4 * ((x+y)^2/(x+y)^2 + (x+y)^2/(x-y)^2 + (x-y)^2/(x+y)^2 + (x-y)^2/(x-y)^2) := by ring_nf
  _ = 1/4 * (1 + (x+y)^2/(x-y)^2 + (x-y)^2/(x+y)^2 + 1) := by rw [div_self h1, div_self h2]
  _ = 1/4 * (2 + (x+y)^2/(x-y)^2 + (x-y)^2/(x+y)^2) := by ring_nf
  _ ≥ 1/4 * (2+2) := by
    simp; norm_num
    suffices 2 ≤ (x + y) ^ 2 / (x - y) ^ 2 + (x - y) ^ 2 / (x + y) ^ 2 by linarith
    suffices ∀a:ℝ, a > 0 → 2≤ 1 / a + a by
      specialize this ((x - y) ^ 2 / (x + y) ^ 2) (by simp; apply div_pos; apply sq_pos_iff.mpr; intro h; have h':x=y:=(by linarith);rw [h'] at habs; simp at habs; apply sq_pos_iff.mpr; intro h; have h':x=-y:=(by linarith);rw [h'] at habs; simp at habs)
      simp at this; assumption
    intro a ha
    suffices 0 ≤ a - 2 + 1/a by linarith
    conv_rhs =>
      calc _
      _ = (√a - 1/√a)^2 := by
        ring_nf
        apply Eq.symm
        calc -(√a * (√a)⁻¹ * 2) + √a ^ 2 + (√a)⁻¹ ^ 2
        _ = -(1 * 2) + √a ^ 2 + (√a)⁻¹ ^ 2 := by rw [mul_inv_cancel₀ (by exact sqrt_ne_zero'.mpr ha)];
        _ = -2 + a + (√a)⁻¹ ^ 2 := by norm_num; rw [Real.sq_sqrt (by linarith)];
        _ = -2 + a + a⁻¹ := by simp; rw [Real.sq_sqrt (by linarith)];
    exact sq_nonneg (sqrt a - 1/sqrt a)
  _ = 1 := by norm_num