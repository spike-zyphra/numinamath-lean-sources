import Mathlib

open Finset Complex Polynomial

/- Let $(a_n)$ and $(b_n)$ be the sequences of real numbers such that

$$
 (2 + i)^n = a_n + b_ni
$$
for all integers $n\geq 0$, where $i = \sqrt{-1}$. What is
$$
\sum_{n=0}^\infty\frac{a_nb_n}{7^n}\,?
$$

$\textbf{(A) }\frac 38\qquad\textbf{(B) }\frac7{16}\qquad\textbf{(C) }\frac12\qquad\textbf{(D) }\frac9{16}\qquad\textbf{(E) }\frac47$ -/
theorem algebra_93574 {a b : ℕ → ℝ} (ha : ∀ n, (2 + I)^n = a n + b n * I) : ∑' n, a n * b n / 7^n = 7 / 16 := by
  -- square (2 + i)^n to get (3+4i)^n = (a(n)^2 - b(n)^2) + 2 a(n) b(n) i, hence 2 * a (n) * b (n) = ((3+4i)^n).im
  have (n : ℕ) : (3 + 4 * I) ^ n = ((a n)^2 - (b n)^2) + 2 * (a n) * (b n) * I := by calc
    (3 + 4 * I)^n = ((2 + I)^2)^n := by
      congr; ring_nf; simp; ring
    _ = ((2 + I)^n)^2 := by exact pow_right_comm (2 + I) 2 n
    _ = _ := by
      rw [ha]
      ring_nf; simp; ring
  have (n : ℕ) : ((3 + 4 * I) ^n).im = 2 * (a n) * (b n) := by
    rw [this]
    simp; norm_cast; simp
  -- so target sum is ∑' ((3 + 4i)/7)^n / 2
  have : ∑' n, a n * b n / 7 ^ n = ∑' n, ((3 + 4 * I) ^n).im / 2 / 7 ^ n := by
    apply tsum_congr
    rintro n
    rw [this]
    ring
  rw [this]
  -- the sum is geometric sum, due to norm of (3+4i)/7 being less than 1
  have h_norm_lt_1 : ‖(3:ℝ)/ 7 + (4:ℝ)/7 * I‖ < 1 := by
    simp [Complex.abs, Complex.normSq]
    norm_num
    convert_to √(5^2)/√(7^2) < 1
    . norm_num
    . simp
      norm_num
  have (n : ℕ) : ((3 + 4 * I)^n).im / 2 / 7^n = (((3:ℝ)/ 7 + (4:ℝ)/7 * I)^n).im / 2 := by
    calc
      ((3 + 4 * I)^n).im / 2 / 7^n = ((3 + 4 * I)^n).im / 7 ^n / 2 := by ring
      _ = ((3 + 4 * I)^n / 7 ^ n).im / 2 := by
        congr
        exact_mod_cast (div_ofReal_im ((3 + 4 * I)^n) (7^n)).symm
      _ = (((3 + 4 * I) / 7)^n).im / 2 := by
        congr
        exact Eq.symm (div_pow (3 + 4 * I) 7 n)
      _ = _ := by
        congr
        push_cast
        ring
  -- just calculate the geometric sum to get result
  calc
    ∑' (n : ℕ), ((3 + 4 * I) ^ n).im / 2 / 7 ^ n  = ∑' n, (((3:ℝ)/ 7 + (4:ℝ)/7 * I)^n).im / 2 := by
      apply tsum_congr; exact this
    _ = 1/2 * ∑' n, (((3:ℝ)/ 7 + (4:ℝ)/7 * I)^n).im := by
      rw [← tsum_mul_left]
      apply tsum_congr; rintro _; ring
    _ = 1 / 2 * (∑' n, ((3:ℝ)/ 7 + (4:ℝ)/7 * I)^n).im := by
      congr
      refine (im_tsum ?_).symm
      exact HasSummableGeomSeries.summable_geometric_of_norm_lt_one _ h_norm_lt_1
    _ = 7 / 16 := by
      rw [geom_series_eq_inverse _ h_norm_lt_1]
      simp [normSq]
      norm_num