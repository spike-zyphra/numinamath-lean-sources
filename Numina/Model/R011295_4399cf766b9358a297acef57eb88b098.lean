import Mathlib

theorem algebra_106170 (x y b c : ℝ) :
  let isRoot (x : ℝ) := x^2 + b * x + c = 0;
  let D := b^2 - 4*c ;
  D > 0 → isRoot x → isRoot y → x - y = 2 → D = 4 :=
by
  intro isRoot D Dpos xr yr Dxy
  have h1 : x^2 + b * x + c = 0 := by
    simpa [isRoot] using xr
  have h2 : y^2 + b * y + c = 0 := by
    simpa [isRoot] using yr
  have h3 : x^2 + b * x + c - (y^2 + b * y + c) = 0 := by
    nlinarith
  have h4 : (x - y) * (x + y + b) = 0 := by
    nlinarith
  have h5 : x + y + b = 0 := by
    apply (mul_left_inj' (show x - y ≠ 0 by
      by_contra h
      have : x - y = 0 := by linarith
      linarith [show x - y = (2 : ℝ) from by linarith]
    )).mp
    linarith
  have eq1 : x = (2 - b)/2 := by
    nlinarith [show x - y = 2 by linarith, show x + y = -b from by linarith]
  have eq2 : y = (-b - 2)/2 := by
    nlinarith [show x - y = 2 by linarith, show x + y = -b from by linarith]
  have h5 : D = 4 := by
    rw [eq1] at h1
    have h6 : ((2 - b)/2)^2 + b * ((2 - b)/2) + c = 0 := by
      linarith
    ring_nf at h6
    have h7 : D = b ^ 2 - 4 * c := by
      rfl
    nlinarith [h6, h7]
  linarith