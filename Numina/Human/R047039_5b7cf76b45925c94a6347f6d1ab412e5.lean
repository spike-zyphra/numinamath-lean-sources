import Mathlib


/-If $-6\leq a \leq -2$ and $3 \leq b \leq 5$, what is the greatest possible value of $\displaystyle\left(a+\frac{1}{b}\right)\left(\frac{1}{b}-a\right) $?  Express your answer as a common fraction.-/
theorem algebra_20928 :
    IsGreatest { x:ℝ|∃a b :ℝ  , (-6 ≤ a ∧ a ≤ -2 ) ∧ (3 ≤ b ∧ b ≤ 5) ∧ x = (a + 1 / b) * (1 / b - a) } (-35 / 9) := by

    constructor
    dsimp
    use -2 , 3
    norm_num

    dsimp[upperBounds]
    intro x h
    obtain⟨a,b,⟨ ha,hb,hx⟩⟩ := h
    rw[hx]
     --化简为平方差公式
    rw[add_comm,←sq_sub_sq]
    --得到b的最小值和a的最大值
    have min_b: 3 ≤ b:= hb.left
    have max_a: a ≤ -2 := ha.right
    --计算不等式的平方
    have t: 1/(b^2)≤1/(3^2) :=
      one_div_le_one_div_of_le (by linarith) (by rw[pow_two 3,pow_two b];exact mul_le_mul min_b min_b (by norm_num) (by linarith[min_b]))
    have t₂: 2^2≤ (-a)^2 := by
      apply  le_neg.mp at max_a
      rw[pow_two 2,pow_two (-a)]
      exact mul_self_le_mul_self (by norm_num) (max_a)
    -- a有最大值b有最小值，a-b的最大值为a的最大值减去去b的最小值
    calc
    _ = 1/(b^2)-(-a)^2 := by ring_nf
    _ ≤ 1/(3^2)-2^2:= tsub_le_tsub  t t₂
    _ = -35/9 := by norm_num
