import Mathlib

open Real


theorem calculus_268354 {l : ℝ} {V : ℝ → ℝ} (hl : l > 0)
  (hV : V = fun x ↦ π / 12 * (x / 2)^2 * (3 * l - x)) :
  IsMaxOn V (Set.Icc 0 l) l := by
  rw [isMaxOn_iff]
  intro x hx
  have h1 : 0 ≤ x := by
    have h := hx.1
    linarith
  have h2 : x ≤ l := by
    have h := hx.2
    linarith
  have h3 : V x ≤ V l := by
    simp [hV]
    have h4 : (x)^2 * (3 * l - x) ≤ 2 * l^3 := by
      nlinarith [sq_nonneg (x - l), sq_nonneg (x), sq_nonneg (l - x), 
        mul_nonneg (show 0 ≤ l by linarith) (show 0 ≤ l - x by nlinarith), 
        mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ l - x by nlinarith)
        ]
    nlinarith [pi_pos, mul_nonneg (show 0 ≤ l by linarith) (show 0 ≤ l by linarith)]
  exact h3