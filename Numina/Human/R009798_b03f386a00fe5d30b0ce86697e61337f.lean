import Mathlib

/- What is the value of the sum $\frac{2}{3}+\frac{2^2}{3^2}+\frac{2^3}{3^3}+ \ldots +\frac{2^{10}}{3^{10}}$? Express your answer as a common fraction. -/
theorem algebra_10677 : ∑ i ∈ Finset.range 10, (2^(i+1) : ℚ) / 3^(i+1) = 116050 / 59049 := by
  -- it is a geometric series sum, and we will use geometric summation equation.
  -- r+r^2+r^3+...+r^n = r * (1-r^n)/(1-r)
  have lemma_geosum(n:ℕ)(r:ℚ)(hr: 1-r ≠ 0):
    ∑ i ∈ Finset.range n, r^(i+1) = r * (1-r^n) / (1-r) := by
    induction' n with d hd
    · simp
    · rw [Finset.sum_range_succ, hd]
      have h1: r^(d+1) = r^(d+1)/(1-r) - r * r^(d+1)/(1-r) := by
        field_simp [hr]; ring
      nth_rw 1 [h1]
      ring
  -- 2^i/3^i = (2/3)^i
  have h1: ∑ i ∈ Finset.range 10, (2^(i+1) : ℚ) / 3^(i+1) =
    ∑ i ∈ Finset.range 10, (2/3:ℚ)^(i+1) := by
    have ht1: ∀n:ℕ, (2^(n+1):ℚ)/(3^(n+1)) = (2/3:ℚ)^(n+1) := by
      intro n; field_simp
    apply Finset.sum_congr
    · simp
    · intro n hn; apply ht1 n
  -- use lemma_geosum, and we can get the result
  rw [h1, lemma_geosum 10 (2/3) (by norm_num)]
  -- simplify 2/3 * (1-(2/3)^10)/(1-2/3)
  have h2: (2/3:ℚ) * (1-(2/3)^10)/(1-2/3) = ((2/3)/(1-2/3)) * (1-(2/3)^10)
    := by ring
  have h3: ((2/3:ℚ)/(1-2/3)) = 2 := by norm_num
  -- (2/3)^10 = 2^10/3^10. 2^2=4, 4^2=16, 2^10 = 2^2 x 2^8 = 4 x 4^4 = 4 x 16^2 = 4 x 256 = 1024
  -- 3^2=9, 9^2=81, 9^3 = 729. 3^10 = 3^2 x 3^8 = 3^2 x 3^2 x (3^2)^3 = 9 x 9 x 729 = 81 x 729 = (maybe we need a calculator here) = 59049
  have h4: (2/3:ℚ)^10 = 1024/59049 := by norm_num
  -- 1-1024/59049 = 59049/59049-1024/59049 = 58025/59049
  have h5: 1-(2/3:ℚ)^10 = 58025/59049 := by
    have: (1:ℚ) = 59049/59049 := by simp
    rw [h4, this]; ring
  -- put them together
  rw [h2,h3,h5]
  -- 2 x 58025 / 59049 = 116050 / 59049
  norm_num