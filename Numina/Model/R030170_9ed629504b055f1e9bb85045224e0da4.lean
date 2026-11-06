import Mathlib
open Real

theorem algebra_94831 {f g : ℝ → ℝ} {h : ℕ → ℝ → ℝ} 
    (hf : ∀ x, f x = 10^(10*x)) (hg : ∀ x, g x = logb 10 (x/10))
    (h1 : ∀ x, h 1 x = g (f x)) (hn : ∀ n ≥ 2, ∀ x, h n x = h 1 (h (n-1) x)) :
    (Nat.digits 10 (Nat.floor (h 2011 1))).sum = 16089 := by
  have h1' : ∀ x, h 1 x = 10 * x - 1 := by
    intro x
    rw [h1 x, hg (f x), hf x]
    have : logb (10 : ℝ) (10 ^ (10 * x) / 10) = 10 * x - 1 := by
      rw [logb_div (by positivity) (by positivity)]
      have h3 : logb (10 : ℝ) (10 ^ (10 * x)) = 10 * x := by
        rw [logb_rpow]
        all_goals norm_num 
      have h4 : logb (10 : ℝ) (10 : ℝ) = 1 := by 
        norm_num [logb_self_eq_one]
      linarith
    norm_num at this ⊢
    linarith

  have h20111 : h 2011 1 = (8 * 10 ^ 2011 + 1) / 9 := by
    have eq1 : ∀ (n : ℕ), h (n + 1) 1 = (8 * 10 ^ (n + 1) + 1) / 9 := by
      intro n
      induction n with
      | zero =>
        norm_num [h1']
      | succ n ih =>
        have eq2 : h ((n + 1) + 1) 1 = h 1 (h (n + 1) 1) := by
          specialize hn ((n + 1 + 1)) (by omega) 1
          simpa using hn
        rw [eq2, h1', ih]
        field_simp
        ring_nf
    specialize eq1 2010
    norm_num at eq1 ⊢
    linarith

  have h5 : Nat.floor (h 2011 1) = (8 * 10 ^ 2011 + 1) / 9 := by
    rw [h20111]
    norm_num [Nat.floor_eq_iff]

  rw [h5]
  native_decide