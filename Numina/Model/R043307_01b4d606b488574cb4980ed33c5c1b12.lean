import Mathlib

theorem algebra_173800 (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h : ∃ d, ∀ n, a n = a 0 + d * n ∧ √(∑ i in Finset.range n, a i) = √(∑ i in Finset.range 0, a i) + d * n) :
    ∀ n, ∑ i in Finset.range n, a i = n ^ 2 / 4 := by
  rcases h with ⟨d, hd⟩
  have h7 : ∑ i in Finset.range 0, a i = 0 := by
    simp
  have h8 : ∑ i in Finset.range 1, a i = a 0 := by
    simp [Finset.sum_range_succ]
    <;> linarith
  have h9 : √(∑ i in Finset.range 1, a i) = √(∑ i in Finset.range 0, a i) + d * (1 : ℕ) := by
    specialize hd 1
    exact hd.2
  rw [h8, h7] at h9
  have h10 : √(a 0) = d := by
    norm_num at h9 ⊢
    linarith [h9]
  have h11 : a 0 = d ^ 2 := by
    calc
      a 0 = (√(a 0)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith [ha 0]
      _ = d ^ 2 := by
        rw [h10]
  -- For n = 2
  have h12 : ∑ i in Finset.range 2, a i = a 0 + a 1 := by
    simp [Finset.sum_range_succ]
    <;> ring
  have h13 : √(∑ i in Finset.range 2, a i) = √(∑ i in Finset.range 0, a i) + d * (2 : ℕ) := by
    specialize hd 2
    exact hd.2
  rw [h12, h7] at h13
  have h14 : √(a 0 + a 1) = 2 * d := by
    norm_num at h13 ⊢
    nlinarith
  have h15 : a 0 + a 1 = 4 * d ^ 2 := by
    calc
      a 0 + a 1 = (√(a 0 + a 1)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith [ha 0, ha 1, show 0 < a 0 + a 1 by linarith [ha 0, ha 1]]
      _ = (2 * d) ^ 2 := by
        rw [h14]
      _ = 4 * d ^ 2 := by
        ring
  -- From the arithmetic sequence
  have h16 : a 1 = a 0 + d := by
    specialize hd 1
    norm_num at hd
    linarith
  rw [h16] at h15
  rw [h11] at h15
  -- Now, solving the equation
  have h17 : d * (1 - 2 * d) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp h17) with h18 h19
  · -- Case $d = 0$ 
    have h20 : d = 0 := by
      linarith
    have h21 : √(a 0) = 0 := by
      linarith [h20, h10]
    have h22 : a 0 = 0 := by
      calc
        a 0 = (√(a 0)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith [ha 0]
        _ = 0 ^ 2 := by
          rw [h21]
        _ = (0 : ℝ) := by
          norm_num
    linarith [ha 0, h22]
  · -- Case $d = 1/2$ 
    have h23 : d = 1 / 2 := by
      linarith
    have h24 : a 0 = 1 / 4 := by
      rw [h11, h23]
      norm_num
    have h25 : ∀ n : ℕ, a n = 1 / 4 + (n : ℝ) / 2 := by
      intro n
      have h26 := (hd n).1
      simp [h23, h24] at h26 ⊢
      linarith
    intro n
    have h27 : ∀ n : ℕ, ∑ i in Finset.range n, a i = (n : ℝ) ^ 2 / 4 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp [h25 n]
        <;> field_simp at *
        <;> ring_nf
        <;> field_simp at *
        <;> ring
    exact h27 n