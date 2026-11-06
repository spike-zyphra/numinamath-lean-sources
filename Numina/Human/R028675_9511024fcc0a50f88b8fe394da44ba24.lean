import Mathlib

open Real

/- 49. (SWE 2) Let $n$ and $k$ be positive integers such that $1 \leq n \leq N+1$, $1 \leq k \leq N+1$. Show that  $$ \min _{n \neq k}|\sin n-\sin k|<\frac{2}{N} $$ -/
theorem number_theory_24718 {N : ℕ} (hN : 0 < N):
  ∃ n k : ℕ, 1 ≤ n ∧ n ≤ N + 1 ∧ 1 ≤ k ∧ k ≤ N + 1 ∧ n ≠ k ∧ |sin n - sin k| < (2: ℝ) / (N:ℝ) := by

  -- This is an application of the pigeonhole principle.

  -- The pigeons are $\sin n$ with $1 ≤ n ≤ N+1$.
  -- The pigeonholes are the segment $[-1,1)$ divided equally into $N$ parts.
  have ho : ∀ n: ℕ, ∃j : Fin N, - 1 + 2 * j / N  ≤ sin n ∧ sin n < - 1 + 2 * j / N  + 2 / N := by
    intro n
    -- Using the fact that $\pi$ is irrational, we can show that $\sin(n) \in [-1,1)$.
    let r := 1 + sin n
    have hr : 0 ≤ r ∧ r < 2 := by
      simp [r]
      constructor
      · linarith [neg_one_le_sin (n:ℝ)]
      · by_contra _
        have : sin n = 1 := by linarith [sin_le_one n]
        obtain ⟨k,hk⟩ := sin_eq_one_iff.mp this 
        absurd irrational_pi
        use 2 * n / (1 + 4 * k)
        rify
        rw [← hk]
        have : 2 * (π / 2 + k * (2 * π)) = π * (1 + 4 * k) := by ring
        rw [this]
        rw [mul_div_cancel_right₀]
        norm_cast
        omega
    have hp : 0 ≤  N * r / 2 := by
      repeat apply mul_nonneg
      simp only [Nat.cast_nonneg]
      exact hr.left
      norm_num
    let j := Nat.floor (N * r / 2)
    have hj : j < N := by
      simp [j]
      rw [Nat.floor_lt hp]
      rw [div_lt_iff₀ (by norm_num)]
      rw [mul_lt_mul_iff_of_pos_left]
      exact hr.right
      norm_cast
    use ⟨j,hj⟩
    have : sin n = r - 1 := by
      simp [r]
    simp [this,j]
    constructor
    · rw [div_le_iff₀]
      linarith [Nat.floor_le hp]
      norm_cast
    · have : (-1:ℝ) + 2 * ⌊N * r / 2⌋₊ / N + 2 / N = -1 + 2 * (⌊N * r / 2⌋₊ + 1) / ↑N := by
        rw [mul_add 2 _ 1, add_div, add_assoc]
        simp
      rw [this]
      suffices r < 2 * (Nat.floor (N * r / 2) + 1) / N by linarith
      rw [lt_div_iff₀']
      rw [← div_lt_iff₀']
      apply Nat.lt_floor_add_one
      norm_num
      norm_cast

  obtain ⟨f,hf⟩ := Classical.skolem.mp ho

  suffices ∃ x ∈ Finset.Icc 1 (N+1), ∃ y ∈ Finset.Icc 1 (N+1), x ≠ y ∧ f x = f y by
    obtain ⟨x,hx,y,hy,h₁,h₂⟩ := this
    use x
    use y
    simp at hx hy
    constructor
    exact hx.left
    constructor
    exact hx.right
    constructor
    exact hy.left
    constructor
    exact hy.right
    constructor
    exact h₁
    rw [abs_lt]
    constructor
    repeat linarith [hf x, h₂ ▸ hf y]

  apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to
  show Finset.card Finset.univ < _
  · simp
  · simp only [Finset.mem_univ, implies_true]