import Mathlib

/- Calculate $(.\overline{6})(3)$.-/
theorem algebra_20676 :  (∑' n : ℕ, ((0.1 ^ n) : ℝ) * 0.6 )* 3 = 2 := by
  --Let $x=.\overline{6}$. Multiplying both sides by 10, we get $10x=6.\overline{6}$. Subtracting these equations yields $9x=6$, so $x=\frac{6}{9}=\frac{2}{3}$. Substituting this into our original expression, we get \[(.\overline{6})(3)=\left( \frac{2}{3} \right) (3) = \left( \frac{2}{\cancel{3}} \right) (\cancel{3}) = \boxed{2}.\]
  rw [Summable.tsum_mul_right]
  rw [tsum_geometric_of_lt_one]
  ring_nf
  norm_num
  norm_num
  apply NormedRing.summable_geometric_of_norm_lt_one
  norm_num

