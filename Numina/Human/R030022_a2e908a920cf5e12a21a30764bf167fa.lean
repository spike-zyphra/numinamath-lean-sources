import Mathlib
/-Let $z$ be a complex number such that
\[z^3 + \frac{1}{z^3} = 52.\]Find all possible values of
\[z + \frac{1}{z}.\]Enter all possible values, separated by commas.-/
theorem algebra_21091 {z : ℂ} (hz : z ≠ 0) (h : z^3 + 1 / z^3 = 52) :
    z + 1 / z = 4 ∨ z + 1 / z = -2 + 3 * .I ∨ z + 1 / z = -2 - 3 * .I := by
    --假设w为z+1/z
    let w := z+ 1/z
    -- 根据z^3 + 1 / z^3 = 52，可以得出w^3 = 52+3w
    have hw₁ : w^3 = 52+3*w := by
      calc
      _ = w^2*w :=by ring
      _ = (z+1/z)^2*(z+1/z) := by ring
      _ = (z^2+2+(1/z)^2)*(z+1/z) := by rw[add_sq,mul_assoc,mul_one_div_cancel hz,mul_one]
      _ = z^3+1/z^3 + 3*(z+1/z):= by
        calc
        _ = (z^3+1/z^3)+(2*z+z^2*1/z)+(z*1/z^2+2*1/z):=by ring
        _ = z^3+1/z^3 + 3*z+3*1/z := by norm_num[pow_two];ring
        _ =  z^3+1/z^3 + 3*(z+1/z) := by ring
      _ = 52+3*w := by rw [h]
    -- 根据w^3 = 52+3w，可以得出w^3-3w-52=0推导出(w-4)*(w^2+4*w+13) = 0
    have hw₂ : (w-4)*(w^2+4*w+13) = 0 := by
      calc
      _ = w^3-52-3*w:= by ring
      _ = 0 := by rw[hw₁];ring
    --分类讨论乘法左边和右边分别为0的情况
    apply Or.elim (zero_eq_mul.mp (hw₂.symm))
    · intro hw
      apply sub_eq_zero.mp at hw
      exact Or.inl hw
    · intro hw
      -- 利用(w^2+4*w+13) = 0 得到(w+2)^2 = -9
      have hw₁: (w+2)^2 = -9:= by
        calc
        _ = w^2+4*w+13-9:= by ring
        _ = -9 :=by rw[hw];ring
      -- (w+2)^2 = -9 将-9转化为(3 * Complex.I) ^ 2 得到 w=-2+3*Complex.I 或者 w=-2-3*Complex.I
      rw [show -9 = (3 * Complex.I) ^ 2 by norm_num [mul_pow, Complex.I_sq]] at hw₁
      apply sq_eq_sq_iff_eq_or_eq_neg.mp at hw₁
      --分别讨论  w=-2+3*Complex.I 或者 w=-2-3*Complex.I 的情况
      apply Or.elim hw₁
      . intro h
        have g : w=-2+3*Complex.I :=by
          calc
          _ =w+2-2 := by ring
          _ = -2+3*Complex.I := by rw [h];ring
        exact Or.inr (Or.inl g)
      . intro h
        have g : w=-2-3*Complex.I :=by
          calc
          _ =w+2-2 := by ring
          _ = -2-3*Complex.I := by rw [h];ring
        exact Or.inr (Or.inr g)
