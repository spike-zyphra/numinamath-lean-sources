import Mathlib

/--
A chocolate chip cookie recipe calls for 15 cups of flour for 20 dozen cookies.
Let us set $x$ cups of flour are needed for 144 cookies.
That means $x$ cups of flour are needed for (144 / 12) cookies.
-/
theorem algebra_20717 (dozen cup needed : ℝ) (hd : dozen = 12) (h : 20 * dozen = 15 * cup) (h1 : 144 = needed * cup) : needed = 9 := by
  -- Converting 144 to 12 dozen, we see that we are making $\frac{12}{20}=\frac{3}{5}$ as many cookies as the recipe makes.  Therefore, we need $\frac{3}{5}$ as much flour, which is $\frac{3}{5}\cdot15=\boxed{9}$ cups.
  norm_num [hd] at h1 h
  have : cup = 16 := by linarith
  simp [this] at h1
  linarith

