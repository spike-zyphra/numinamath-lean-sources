import Mathlib

theorem number_theory_147208 (n : ℕ) :
    1947 ∣ 46^(2*n+1) + 296 * 13^(2*n+1) := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    have h1 : 46 ^ (2 * (n + 1) + 1) + 296 * 13 ^ (2 * (n + 1) + 1) =
        46^2 * (46 ^ (2 * n + 1)) + 296 * 13^2 * (13 ^ (2 * n + 1)) := by
      ring_nf
    rw [h1]
    norm_num at ih ⊢
    <;> omega