import Mathlib

/- Positive numbers x, y, and z satisfy xyz=10^{81} and
(log_{10} x)(log_{10} yz)+(log_{10} y)(log_{10} z)=468. Find
√((log_{10} x)^2+(log_{10} y)^2+(log_{10} z)^2). -/
theorem algebra_94686 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
(hxyz : x * y * z = 10 ^ 81) (hlog : Real.logb 10 x * Real.logb 10 (y * z) +
Real.logb 10 y * Real.logb 10 z = 468) :
Real.sqrt ((Real.logb 10 x) ^ 2 + (Real.logb 10 y) ^ 2 + (Real.logb 10 z) ^ 2) = 75 := by
  -- first we show log_10 x + log_10 y + log_10 z = 81 by taking the log of both sides at hxyz
  apply congr_arg (fun x => Real.logb 10 x) at hxyz
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
  Real.logb_mul (by norm_cast; norm_num; exact ⟨by linarith, by linarith⟩) (by linarith), Real.logb_mul (by linarith) (by linarith)] at hxyz
  -- we unfold the logb in hlog
  rw [Real.logb_mul (by linarith) (by linarith), mul_add] at hlog
  -- now we can calculate
  calc √((Real.logb 10 x) ^ 2 + (Real.logb 10 y) ^ 2 + (Real.logb 10 z) ^ 2)
  _ = √((Real.logb 10 x + Real.logb 10 y + Real.logb 10 z)^2 - 2*(Real.logb 10 x * Real.logb 10 y + Real.logb 10 x * Real.logb 10 z + Real.logb 10 y * Real.logb 10 z)) := by ring_nf
  _ = √(81^2 - 2*468) := by rw [hxyz, hlog]; norm_num
  _ = 75 := by convert_to √(75^2) = 75; norm_num; simp