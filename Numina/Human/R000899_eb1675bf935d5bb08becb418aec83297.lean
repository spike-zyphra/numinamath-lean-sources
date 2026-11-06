import Mathlib

open Finset

/- A sequence $(S_n)$ is defined as follows: $S_1 = 1,$ $S_2 = 1,$
\[S_n = \frac{S_{n - 2} \cdot S_{n - 1}}{S_{n - 2} + S_{n - 1}}\]for $n > 2.$  Compute $S_{12}.$ -/
theorem algebra_18940 {S : ℕ → ℝ}
    (hS1 : S 1 = 1) (hS2 : S 2 = 1)
    (hSn : ∀ n > 2, S n = (S (n - 2) * S (n - 1)) / (S (n - 2) + S (n - 1))) :
    S 12 = 1 / 144 := by
  -- notice that Sn = 1/S(n-1) + 1/S(n-2). so we consider their reciprocal.
  let T: ℕ → ℝ := fun n => 1 / (S n)
  have T_def(n:ℕ): T n = 1 / (S n) := rfl
  -- we can prove all terms of S are positive
  have spos(n:ℕ)(posn: 0 < n): 0 < S n := by
    induction' n using Nat.strong_induction_on with d hd
    by_cases hd1: d = 1
    · rw [hd1, hS1]; simp
    · by_cases hd2: d = 2
      · rw [hd2, hS2]; simp
      · have dgt2: d > 2 := by omega
        rw [hSn d dgt2]
        have hh1: 0 < S (d-2) := by
          apply hd _ (by omega) (by omega)
        have hh2: 0 < S (d-1) := by
          apply hd _ (by omega) (by omega)
        apply div_pos
        · apply mul_pos hh1 hh2
        · linarith [hh1, hh2]
  -- and T n = T n-1 + T n-2
  have hT(n:ℕ)(posn: 0 < n): T (n+2) = T (n+1) + T n := by
    rw [T_def (n+2), T_def (n+1), T_def n]
    rw [hSn (n+2) (by linarith [posn])]
    have hh1: 0 < S (n+1) := by
      apply spos _ (by omega)
    have hh2: 0 < S n := by
      apply spos _ posn
    field_simp [hh1, hh2]
    left; ring
  -- we can find general formula of Tn, it's a fibonacci series. however, it's quite complicated.
  -- so here we just calculate T 12, and give S 12
  have hT12: T 12 = 144 := by
    have hT1: T 1 = 1 := by
      rw [T_def, hS1]; simp
    have hT2: T 2 = 1 := by
      rw [T_def, hS2]; simp
    rw [hT, hT, hT, hT, hT, hT, hT, hT, hT, hT]
    any_goals norm_num
    rw [hT1, hT2]; ring
  -- T12=144=1/S12, so S12 = 1/144
  rw [← hT12, T_def]; simp