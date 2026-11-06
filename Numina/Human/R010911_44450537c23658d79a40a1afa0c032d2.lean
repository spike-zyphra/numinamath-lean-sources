import Mathlib

open Real Set
open scoped Real

/- If $\frac{\sin (2A + B)}{\sin B} = 5,$ then find $\frac{\tan (A + B)}{\tan A}.$ -/
theorem calculus_22045 {A B : ℝ} (hA : cos (A + B) ≠ 0) (hB : sin B ≠ 0) (hC : sin A ≠ 0)
  (h : sin (2 * A + B) / sin B = 5) :
  tan (A + B) / tan A = 3 / 2 := by
    -- 将等式两边同乘 sin B，消去分母
    replace h :  5 * sin B = sin (2 * A + B) := by
      calc _ = (sin (2 * A + B) / sin B) * sin B := by rw[h]
           _ = sin (2 * A + B) := by field_simp

    -- 重写等式，将 2A + B 表示为 (A + B) + A
    replace h : 5 * sin ((A + B) - A) = sin ((A + B) + A) := by
      calc _ = 5 * sin (B) := by ring_nf
           _ = sin (2 * A + B) := by rw[h]
           _ = sin ((A + B) + A) := by ring_nf

    -- 使用三角函数加法公式
    have h1 : sin ((A + B) + A) = sin (A + B) * cos A + cos (A + B) * sin A := sin_add (A + B) A
    have h2 : sin ((A + B) - A) = sin (A + B) * cos A - cos (A + B) * sin A := sin_sub (A + B) A
    rw [h1, h2] at h
    clear h1 h2

    -- 通过线性运算简化等式
    replace h : 3 * sin A * cos (A + B) = sin (A + B) * cos A * 2:= by linarith

    -- 使用正切函数的定义
    have h1 : tan (A + B) = sin (A + B) / cos (A + B) := tan_eq_sin_div_cos (A + B)
    have h2 : tan A = sin A / cos A := tan_eq_sin_div_cos A
    rw [h1, h2]

    -- 通过代数运算化简
    field_simp
    rw [←h]
    linarith
