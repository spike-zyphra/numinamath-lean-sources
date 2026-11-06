import Mathlib

/- Paula the painter and her two helpers each paint at constant, but different, rates. They always start at 8:00 AM, and all three always take the same amount of time to eat lunch. On Monday the three of them painted 50% of a house, quitting at 4:00 PM. On Tuesday, when Paula wasn't there, the two helpers painted only 24% of the house and quit at 2:12 PM. On Wednesday Paula worked by herself and finished the house by working until 7:12 P.M. How long, in minutes, was each day's lunch break?
(A) 30
(B) 36
(C) 42
(D) 48
(E) 60
 -/
theorem algebra_93536 (P H L : ℝ) (hp : 0 < P) (hh : 0 < H) (hl: 0 < L)
(h₁ : (P + H)*(8 - L) = 50 / 100) (h₂ : (6 + (12:ℝ)/60 - L) * H = 24 / 100) (h₃ : (11 + (12:ℝ)/60 - L) * P = 26 / 100) : L * 60 = 48 := by
  -- P is paula's working rate, H is helpers' total working rate, L is lunch time in hours. first expand all equations
  have h₁: P * 8 + H * 8 - P * L - H * L = 1 / 2 := by
    norm_num at h₁
    rw [← h₁]
    ring
  have h₂ : H * 6.2 - H * L = 6 / 25 := by
    norm_num at h₂
    rw [← h₂]
    ring
  have h₃ : P * 11.2 - P * L = 13 / 50 := by
    norm_num at h₃
    rw [← h₃]
    ring
  -- now canceling H*L and P*L terms, find that H = 16 / 9 * P. plug that inside 2nd equation to get equation of P and L only
  have h₄ :  H = 16 / 9 * P := by linarith
  rw [h₄] at h₂
  -- use 2nd equation and 3rd equation to get P = 5/200. then using that in 3rd equation determine L = 4/5
  have hp' : P = 5 / 200 := by linarith
  rw [hp'] at h₃
  linarith