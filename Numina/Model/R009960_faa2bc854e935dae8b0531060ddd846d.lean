import Mathlib

theorem algebra_21591 (j s : ℕ) (hj : j = 450) (hs : s = 600)
    (h : 5 * j * x = 1500) :
    s * x = 400 := by 
  subst hj
  subst hs
  -- Now we have `5 * 450 * x = 1500` as hypothesis and need to prove `600 * x = 400`
  -- Compute 5 * 450 = 2250
  -- So the hypothesis is `2250 * x = 1500`
  -- Then x = 1500 / 2250 = 2/3
  -- Then the goal is `600 * (2/3) = 400`
  -- Lean can compute with natural numbers to prove `600 * x = 400` from `2250 * x = 1500`
  -- Lean can solve this with omega and ring_nf
  ring_nf at h ⊢
  omega