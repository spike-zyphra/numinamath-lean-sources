import Mathlib

/- A ball is dropped from $405$ meters and rebounds two-thirds the distance it falls each time it bounces. How many meters will the ball have traveled when it hits the ground the fourth time? -/
theorem algebra_21877 (d d1 d2 : ℝ)
    /- d1 表示球向下落下的总距离:
       - 第一次下落 405米
       - 第二次下落 405*(2/3)米
       - 第三次下落 405*(2/3)²米
       - 第四次下落 405*(2/3)³米 -/
    (h1 : d1 = (1 + (2 / 3) + (2 / 3) ^ 2 + (2 / 3) ^ 3) * 405)
    /- d2 表示球向上弹起的总距离:
       - 第一次弹起 405*(2/3)米
       - 第二次弹起 405*(2/3)²米
       - 第三次弹起 405*(2/3)³米 -/
    (h2 : d2 =  ((2 / 3) + (2 / 3) ^ 2 + (2 / 3) ^ 3) * 405)
    /- d 为总距离，等于下落距离d1加上弹起距离d2 -/
    (h3 : d = d1 + d2) : d = 1545 := by
    linarith  /- 使用线性算术求解器计算最终结果 -/
