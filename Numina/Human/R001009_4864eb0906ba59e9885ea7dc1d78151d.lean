import Mathlib

/- A railroad trestle spans a gorge 80 feet wide and connects two cliffs at heights of 112 and 172 feet above the bottom of the gorge. A train is crossing this gorge from the higher cliff to the lower. When the front of the train has traveled $\frac{3}{4}$ of the trestle's length, how many feet is it above the bottom of the gorge? -/
theorem algebra_19804 (x y z: ℝ) (hx : x = 3 / 4) (hy : y = (172 - 112) * x) (hz : z = 172 - y) :
    z = 127 := by
         -- 使用线性算术求解器证明
        linarith
