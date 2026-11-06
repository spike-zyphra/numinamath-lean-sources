import Mathlib

/-If the second term of a geometric sequence of real numbers is $-2$ and the fifth term is $16,$ then what is the fourteenth term?-/
theorem algebra_19313 {a r : ℝ} (hr : r ≠ 0) (h2 : a * r = -2) (h5 : a * r^4 = 16) :
    a * r^13 = -8192 := by
    -- 第15项 可以看成 ar * (r^3)^4, 即只要知道 r^3的值就推断出第15项
    have h1 : r^3 = -8 := by
    -- 根据第5项和第二项的关系，可以推断出 r^3的值
      let h : -2*r^3 = 16 := by
        calc
        _ = a*r^4 := by rw [←h2];ring
        _ = 16 := by rw [h5]
      calc
      _ = -2*r^3 / (-2) := by ring
      _ = 16 / (-2) := by rw [h]
      _ = -8 := by norm_num
    --计算第15项的值
    calc
    _ = a*r*(r^3)^4 := by ring
    _ = -2*(-8)^4 := by rw [h2, h1]
    _ = -8192 := by norm_num
