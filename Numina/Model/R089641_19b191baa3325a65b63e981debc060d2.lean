import Mathlib

/- Calculate: $\left( 2004\frac{1980}{2005}+2005\frac{1980}{2004} \right)\div \left( \frac{2000}{2005}+\frac{2000}{2004} \right)=$ ___          ___. -/
theorem algebra_7427 {a b c d : ℚ} (ha : a = 2004 + 1980 / 2005) (hb : b = 2005 + 1980 / 2004)
    (hc : c = 2000 / 2005) (hd : d = 2000 / 2004) :
    (a + b) / (c + d) = 2010 := by 
  rw [ha, hb, hc, hd]
  norm_num