import Mathlib
open Real
open scoped BigOperators

/- Given the line $kx+\left(k+1\right)y-1=0$ (where $k$ is a positive integer) and the right-angled triangle formed with the coordinate axes has an area of $S_{k}\left(k=1,2,3,\cdots ,2006\right)$, then $S_{1}+S_{2}+S_{3}+\cdot \cdot \cdot +S_{2006}=$ ___            ___. -/
theorem algebra_8121 {S : ℕ → ℝ}
  (hS : ∀ k, S k = (1/2) * (1/k) * (1/(k+1))) :
  ∑ i in Finset.Icc 1 2006, S i = 1003/2007 := by

  rw [Finset.sum_congr rfl (fun i hi => hS i)]
  have h1 : ∀ k : ℕ, k ≥ 1 → (1 / 2 : ℝ) * (1 / k) * (1 / (k + 1)) =
    (1 / 2 : ℝ) * (1 / k - 1 / (k + 1 : ℝ)) := by
    intro k hk
    field_simp at *
    <;> ring

  have h2 : ∀ (n : ℕ), ∑ i ∈ Finset.Icc 1 n, (1 / 2 : ℝ) * (1 / i) * (1 / (i + 1)) =
      (1 / 2 : ℝ) * (1 - 1 / (n + 1 : ℝ)) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [h1 (n + 1) (by linarith)]
      rw [ih]
      field_simp at *
      ring

  specialize h2 2006
  rw [h2]
  norm_num