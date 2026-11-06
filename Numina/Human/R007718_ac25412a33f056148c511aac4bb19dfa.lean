import Mathlib

open scoped BigOperators

/- Let $c>0$ be a positive real number. We define the sequence $\left(x_{n}\right)$ by $x_{0}=0$ and


$$

x_{n+1}=x_{n}^{2}+c

$$


for each $n \geq 0$. For which values of $c$ is it true that $\left|x_{n}\right|<2016$ for all $n$ ? -/
theorem algebra_254040 (c : ℝ) (hc : c > 0)
  (x : ℕ → ℝ) (hx0 : x 0 = 0)
  (hxn : ∀ n, x (n + 1) = (x n)^2 + c) :
  (∀ n, |x n| < 2016) ↔ c ≤ 1 / 4 := by
  -- let's first get rid of the absolute value
  have hnn: ∀ n, 0 ≤ x n := by
    intro n
    induction n with
    | zero => rw [hx0]
    | succ m' ih =>
      rw [hxn]
      nlinarith
  conv_lhs =>
    intro n
    lhs; rw [abs_of_nonneg (hnn n)]
  constructor
  contrapose
  rotate_left
  · intro h
    -- we show a stronger statement by induction
    suffices ∀ n, x n ≤ 1/2 by
      intro n; specialize this n; linarith
    -- this is easy induction
    intro n
    induction n with
    | zero => rw [hx0]; norm_num
    | succ m' ih =>
      rw [hxn, (by norm_num:(1/2:ℝ) = (1/4:ℝ) + (1/4:ℝ))]
      gcongr
      refine (Real.le_sqrt (hnn m') ?_).mp ?_
      norm_num
      rw [(by norm_num:(4:ℝ)=2^2)]
      simp; linarith
  -- now for the other direction
  intro hc; simp only [not_le] at hc
  -- let d = c-1/4 > 0 and show that the sequence always grows by at least d
  let q:∃ d:ℝ, d = c-1/4 := by
    use c-1/4
  obtain ⟨d, ddef⟩ := q
  have hq: d > 0 := by linarith
  -- if we do that the proof is quite simple
  suffices ∀ n, x (n + 1) ≥ x n + d by
    simp
    have h1:∀m, x m ≥ m*d := by
      intro m
      induction m with
      | zero => rw [hx0]; norm_num
      | succ m' ih =>
        specialize this m'
        simp at ih this ⊢
        calc (↑m' + 1) * d
        _ = m' * d + d := by ring_nf
        _ ≤ x m' + d := by linarith
        _ ≤ x (m' + 1) := by linarith
    let q:∃ N:ℕ, N ≥ 1/d := by
      use Nat.ceil (1/d)
      exact Nat.le_ceil (1 / d)
    obtain ⟨N, Ndef⟩ := q
    use 2016*N
    specialize h1 (2016*N); simp at h1
    apply le_trans' h1
    conv_lhs =>
      calc _
      _ = 2016 * (1:ℝ) := by norm_num
    rw [mul_assoc]
    gcongr
    conv_lhs =>
      calc _
      _ = 1/d * d := by rw [mul_comm, mul_one_div, div_self (by apply ne_of_gt; linarith)]
    gcongr
  -- just a simple complete the square
  intro n
  rw [hxn, ddef]
  ring_nf
  simp
  suffices 0≤x n ^2 - x n + 1/4 by linarith
  suffices 0≤(x n- 1/2)^2 by linarith
  exact sq_nonneg _