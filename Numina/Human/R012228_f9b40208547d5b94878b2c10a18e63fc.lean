import Mathlib

/- 3. Let the sequence $\left\{x_{n}\right\}$ satisfy the condition $x_{0}=5, x_{n+1}=x_{n}+\frac{1}{x_{n}}(n=0,1, \cdots)$. Prove: $45<x_{1000}<45.1$. -/
theorem algebra_192354 (x : ℕ → ℝ) (hx0 : x 0 = 5) (hxn : ∀ n, x (n + 1) = x n + 1 / x n) :
    45 < x 1000 ∧ x 1000 < 45.1 := by
  -- an easy induction shows all the x n are positive
  have pos : ∀ n, x n > 0
  · intro n; induction n with
    | zero => simp [hx0]
    | succ n ih => rw [hxn n]; positivity
  -- another easy induction shows x is strictly increasing
  have mono : StrictMono x
  · apply strictMono_of_lt_add_one
    intro n hn; induction n with
    | zero => rw [hxn 0, hx0]; norm_num
    | succ n ih => rw [hxn (n + 1)]; simp [pos (n + 1)]
  -- useful to show sum telescopes
  have sq : ∀ n, x (n + 1)^2 - (x n)^2 = 1 / (x n)^2 + 2
  · intro n
    rw [hxn n]
    ring_nf
    field_simp [pos n]
    rw [mul_comm]
    exact mul_div_cancel_right₀ 2 (pos n).ne.symm
  -- prove an alternate form for the square of x n
  have eq_sq : ∀ n, x (n + 1)^2 = 25 + 2 * (n + 1) + ∑ k ∈ Finset.range (n + 1), (1 / (x k)^2)
  · intro n; calc
      x (n + 1)^2 = (x 0)^2 + ∑ k ∈ Finset.range (n + 1), (x (k + 1)^2 - (x k)^2) := by rw [Finset.sum_range_sub (fun k => (x k)^2)]; ring
      _ = (x 0)^2 + ∑ k ∈ Finset.range (n + 1), (1 / (x k)^2 + 2) := by rw [Finset.sum_congr rfl (fun n _ => sq n)]
      _ = 25 + 2 * (n + 1) + ∑ k ∈ Finset.range (n + 1), (1 / (x k)^2) := by rw [hx0, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, add_comm _ (_ * 2), mul_comm, add_assoc]; norm_num
  -- this allows us to bound x n from below
  have lower : ∀ n, x (n + 1)^2 > 25 + 2 * (n + 1)
  · intro n
    rw [eq_sq n]
    simp
    apply Finset.sum_pos _ (by simp)
    intro i hi
    have posi := pos i
    positivity
  constructor
  -- this lower bound at n = 1000 is what is required
  · have this := (lower 999).lt
    conv_lhs at this => norm_num; rw [show (2025 : ℝ) = 45^2 by norm_num]
    conv_rhs at this => norm_num
    rw [←Real.sqrt_sq (show 0 ≤ 45 by norm_num), ←Real.sqrt_sq (pos 1000).le]
    exact Real.sqrt_lt_sqrt (show 0 ≤ 45^2 by norm_num) this
  -- for the upper bound, we find similar bounds for two halves of the sum in the equality
  have lt1 : ∑ i ∈ Finset.range 100, (1 / (x i)^2) ≤ ∑ i ∈ Finset.range 100, 1/25
  · apply Finset.sum_le_sum
    intro i hi
    simp at hi
    have := mono.monotone (Nat.zero_le i)
    rw [hx0] at this
    rw [one_div]
    apply inv_le_of_inv_le₀ (by norm_num)
    nlinarith [this]
  conv_rhs at lt1 => simp; norm_num
  have lt2 : ∑ i ∈ Finset.Ico 100 1000, (1 / (x i)^2) ≤ ∑ i ∈ Finset.Ico 100 1000, 1/225
  · apply Finset.sum_le_sum
    intro i hi
    simp at hi
    have := mono.monotone hi.1
    rw [one_div, one_div]
    apply inv_le_of_inv_le₀ (by norm_num)
    rw [inv_inv]
    trans (x 100)^2
    convert (lower 99).le
    norm_num
    nlinarith [this, pos 100]
  conv_rhs at lt2 => simp; norm_num
  rw [←Real.sqrt_sq (show 0 ≤ 45.1 by norm_num), ←Real.sqrt_sq (pos 1000).le, Real.sqrt_lt_sqrt_iff (by positivity)]
  -- show we can decompose the sum as over [0, 100) and [100, 1000)
  have disj : Disjoint (Finset.range 100) (Finset.Ico 100 1000)
  · rw [@Finset.disjoint_left]
    intro x hx hx'
    simp at hx hx' ⊢
    linarith
  have range_decomp : Finset.range 1000 = Finset.disjUnion (Finset.range 100) (Finset.Ico 100 1000) disj
  · ext x
    constructor
    intro hx
    simp at hx ⊢
    rcases lt_or_ge x 100 with hx' | hx'
    left; exact hx'
    right; exact ⟨hx', hx⟩
    intro hx
    simp at hx ⊢
    rcases hx with hx' | hx'
    linarith
    exact hx'.2
  -- apply our upper bounds to conclude
  calc
    x 1000^2 = 2025 + ∑ k ∈ Finset.range 1000, 1 / x k^2 := by convert eq_sq 999; norm_num
    _ = 2025 + (∑ k ∈ Finset.range 100, 1 / x k^2 + ∑ k ∈ Finset.Ico 100 1000, 1 / x k^2) := by rw [range_decomp, Finset.sum_disjUnion]
    _ ≤ 2025 + 4 + 4 := by linarith [lt1, lt2]
    _ < 45.1^2 := by norm_num