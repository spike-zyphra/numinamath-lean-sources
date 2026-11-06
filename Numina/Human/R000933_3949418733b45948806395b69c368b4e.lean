import Mathlib

open Real

/-If $\pi=3.1415926...$, what is the exact value of $|\pi-3.14|+|\pi-\frac{22}{7}|$? Express your answer as a common fraction.-/
theorem algebra_19195 : |Real.pi - 3.14| + |Real.pi - 22/7| = 1/350 := by
  -- Since $\pi>3.14$, we know that $\pi-3.14>0$, and so $|\pi-3.14|=\pi-3.14$.
  have : |Real.pi - 3.14| = Real.pi - 3.14 := by
    rw [abs_of_nonneg]
    simp
    apply le_trans
    show (3.14 : ℝ) ≤ 3.141592
    norm_num
    exact Real.pi_gt_3141592.le
  rw [this]
  -- Also, since $\pi<22/7=3.\overline{142857}$, we have $|\pi-\frac{22}{7}|=\frac{22}{7}-\pi$.
  have : |Real.pi - 22/7| = 22/7 - Real.pi := by
    rw [abs_sub_comm, abs_eq_self]
    simp
    apply le_trans
    exact Real.pi_lt_3141593.le
    norm_num
  rw [this]
  -- The exact value of the sum is \begin{align*}
  -- |\pi-3.14|+\left|\pi-\frac{22}{7}\right|&=\pi-3.14+\frac{22}{7}-\pi \\
  -- &=\frac{22}{7}-3.14 \\
  -- &=\frac{22}{7}-\frac{314}{100} \\
  -- &=\frac{2200}{700}-\frac{7(314)}{700} \\
  -- &=\frac{2200-2198}{700}\\
  -- &=\frac{2}{700}\\
  -- &=\boxed{\frac{1}{350}}.
  -- \end{align*}
  norm_num
