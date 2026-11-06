import Mathlib

open Real

/- 3・78 Let $a_{n}=\frac{n^{2}+1}{\sqrt{n^{4}+4}}, n=1,2,3, \cdots, b_{n}=a_{1} a_{2} \cdots a_{n}$, prove that $\frac{b_{n}}{\sqrt{2}}=\frac{\sqrt{n^{2}+1}}{\sqrt{n^{2}+2 n+2}}$. And prove: $\frac{1}{(n+1)^{3}}<\frac{b_{n}}{\sqrt{2}}-\frac{n}{n+1}<\frac{1}{n^{3}}$ for all positive integers $n$. -/
theorem algebra_247104 {a b : ℕ → ℝ}
    (ha : ∀ n, a n = (n ^ 2 + 1) / sqrt (n ^ 4 + 4))
    (hb : ∀ n, b n = ∏ i ∈ Finset.Icc 1 n, a i) :
    (∀ n, b n / sqrt 2 = sqrt (n ^ 2 + 1) / sqrt (n ^ 2 + 2 * n + 2)) ∧
    (∀ n, 0 < n → 1 / (n + 1) ^ 3 < b n / sqrt 2 - n / (n + 1) ∧
      b n / sqrt 2 - n / (n + 1) < 1 / n ^ 3) := by
  -- since we'll use recursion, we need a recursive definition for b
  have hb': ∀ n > 0, b n = a n * b (n - 1) := by
    intro n hn
    rw [hb, show n=(n-1)+1 by omega, Finset.prod_Icc_succ_top (by omega), ← hb (n-1)]; simp; ring_nf
  -- for first statement we go by induction
  have h1: ∀ (n : ℕ), b n / √2 = √(↑n ^ 2 + 1) / √(↑n ^ 2 + 2 * ↑n + 2) := by
    intro n
    induction n with
    | zero => simp [hb 0]
    | succ n ih =>
      rw [hb' (n+1) (by linarith), show n+1-1=n by simp, ← mul_div, ih, ha (n+1)]
      -- we just have to simplify
      field_simp
      rw [← sqrt_mul (by positivity), ← sqrt_mul (by positivity), mul_assoc, ← sqrt_mul (by positivity), show ((↑n + 1) ^ 2 + 1) = √(((↑n + 1) ^ 2 + 1)^2) by rw [sqrt_sq (by positivity)], ← sqrt_mul (by positivity), sqrt_sq (by positivity)]
      ring_nf
  constructor
  assumption
  intro n hn
  constructor
  -- we just substite our obtained b n / sqrt 2, square to get rid of the sqrt and simplify
  · suffices 1/((n:ℝ)+1)^3 + (n:ℝ)/((n:ℝ)+1) < b n / √2 by linarith
    rw [h1]
    field_simp
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rw [← Real.sqrt_div (by positivity), Real.sq_sqrt (by positivity)]
    refine (lt_div_iff₀ ?_).mpr ?_
    positivity; field_simp
    refine (div_lt_iff₀ ?_).mpr ?_
    positivity
    ring_nf; norm_num
    suffices 0 < 1 + (n:ℝ) * 8 + ↑n ^ 2 * 29 + ↑n ^ 3 * 64 + ↑n ^ 4 * 98 + ↑n ^ 5 * 112 + ↑n ^ 6 * 98 - (2 + ↑n * 10 + ↑n ^ 2 * 29 + ↑n ^ 3 * 60 + ↑n ^ 4 * 92 + ↑n ^ 5 * 108 + ↑n ^ 6 * 97) by linarith
    ring_nf
    -- easiest way to go is to let m=n-1
    let q:∃ m:ℕ, m = n-1 := by
      simp only [exists_eq]
    obtain ⟨m, mdef⟩ := q
    have hnm: n = m+1 := by omega
    rw [hnm]; ring_nf; norm_num; ring_nf
    positivity
  -- similar proof again
  · suffices b n / √2 < 1 / n ^ 3 + n / (n + 1) by linarith
    rw [h1]
    field_simp
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rw [← Real.sqrt_div (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
    refine (lt_div_iff₀ ?_).mpr ?_
    positivity
    rw [mul_comm, mul_div]
    refine (div_lt_iff₀ ?_).mpr ?_
    positivity
    ring_nf; norm_num
    suffices 0 < 2 + (n:ℝ) * 6 + ↑n ^ 2 * 7 + ↑n ^ 3 * 4 + ↑n ^ 4 * 5 + ↑n ^ 5 * 8 + ↑n ^ 6 * 6 - n^6 by linarith
    ring_nf
    positivity