import Mathlib

/- Let $N = 2 ^ {2 ^ 2}$ and $x$ be a real number such that $N ^ (N ^ N) = 2 ^ {2 ^ x}$. Find x. -/
theorem algebra_609944 {N : ℝ} (hN : N = (2: ℝ)^((2: ℝ)^(2: ℝ))) (x : ℝ)
    (h : (N: ℝ) ^ ((N: ℝ) ^ (N: ℝ)) = (2: ℝ)^((2: ℝ)^(x: ℝ))) :
    x = 66 := by
  -- First, we compute N = 2^2^2, which equals 16.
  norm_num at hN
  nth_rw 1 [hN] at h
  -- Then rewrite N ^ N ^ N into 2 ^ (4 ^ N ^ N).
  rw [show (16: ℝ) = (2: ℝ) ^ (4: ℝ) by norm_num, 
      ← Real.rpow_mul (by simp) 4 (N ^ N)] at h

  -- Since 2 ^ (4 * N ^ N) = 2 ^ (2 ^ x), we have 4 * N ^ N = x.
  have h1 := congr_arg (fun x => Real.logb (2: ℝ) x) h
  simp [Real.logb_rpow (show (2: ℝ) > 0 by simp) (by linarith)] at h1

  -- Similarly, calculate 4 * N ^ N = 2 ^ (2 + 64).
  rw [hN, show (4: ℝ) = (2: ℝ) ^ (2: ℝ) by norm_num,
      show (16: ℝ) ^ (16: ℝ) = (2: ℝ) ^ (64: ℝ) by norm_num,
      ← Real.rpow_add (show (2: ℝ) > (0: ℝ) by simp) (2:ℝ) (64: ℝ)] at h1

  -- Since 2 ^ (2 + 64) = 2 ^ x, we have x = 64 + 2 = 66.
  have h2 := congr_arg (fun x => Real.logb (2: ℝ) x) h1
  simp [Real.logb_rpow (show (2: ℝ) > 0 by simp) (by linarith)] at h2
  norm_num at h2
  exact Eq.symm h2
