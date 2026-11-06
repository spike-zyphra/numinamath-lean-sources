import Mathlib

/- Suppose $m$ is a two-digit positive integer such that $6^{-1}\pmod m$ exists and $6^{-1}\equiv 6^2\pmod m$. What is $m$? -/
theorem number_theory_19354 {m : ℕ} (hm : m ∈ Finset.Icc 10 99) (h : 6 * (6 ^ 2) ≡ 1 [MOD m]) :
    m = 43 := by 
  norm_num [Nat.ModEq] at h
  revert m hm
  decide