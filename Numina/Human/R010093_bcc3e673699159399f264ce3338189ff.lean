import Mathlib

open Real
/-For positive real numbers $a,$ $b,$ $c,$ and $d,$ find the minimum value of
\[\left\lfloor \frac{b + c + d}{a} \right\rfloor + \left\lfloor \frac{a + c + d}{b} \right\rfloor + \left\lfloor \frac{a + b + d}{c} \right\rfloor + \left\lfloor \frac{a + b + c}{d} \right\rfloor.\]-/
theorem algebra_21194 :
    IsLeast {n : ℤ | ∃ a b c d : ℝ, (a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) ∧
      n = ⌊(b + c + d) / a⌋ + ⌊(a + c + d) / b⌋ + ⌊(a + b + d) / c⌋ +
        ⌊(a + b + c) / d⌋} 9 := by
      -- 证明9在集合内
      constructor
      dsimp
      --当a=4,b=c=d=5时，等式成立
      use 4,5,5,5
      norm_num
      -- 证明9是集合中的最小值
      dsimp[lowerBounds]
      intros x h
      --引入假设
      rcases h with ⟨a,b,c,d,⟨hl,hr⟩⟩
      -- 证明对于任何实数R，都有 R-1<⌊R⌋
      have t₁ :((b + c + d) / a)-1<⌊(b + c + d) / a⌋ := Int.sub_one_lt_floor _
      have t₂ :((a + c + d) / b)-1<⌊(a + c + d) / b⌋ := Int.sub_one_lt_floor _
      have t₃ :((a + b + d) / c)-1<⌊(a + b + d) / c⌋ := Int.sub_one_lt_floor _
      have t₄ :((a + b + c) / d)-1<⌊(a + b + c) / d⌋ := Int.sub_one_lt_floor _
      --代数重排
      have add :(b + c + d) / a - 1 + ((a + c + d) / b - 1) + ((a + b + d) / c - 1 + ((a + b + c) / d - 1))
                =(a/b+b/a)+(a/c+c/a)+(a/d+d/a)+(b/c+c/b)+(b/d+d/b)+(c/d+d/c)-4 := by ring

       --证明一个数乘以自身的倒数等于1^2
      have inv_self_eq_one_eq {a b :ℝ} (hna : a≠0) (hnb : b≠0) : a/b * (b/a) = 1^2 := by
        calc
              _ = a/b*b*1/a := by ring
              _ = a*(1/a) := by rw[div_mul_cancel₀ a hnb] ;ring
              _ = 1:= by rw[mul_one_div_cancel hna]
              _ = 1^2 := by norm_num
      -- 根据AM-GM 不等式计算
      have r₁ :a/b * (b/a) = 1^2 := inv_self_eq_one_eq (by linarith) (by linarith)
      have r₂ :a/c * (c/a) = 1^2 := inv_self_eq_one_eq (by linarith) (by linarith)
      have r₃ :a/d * (d/a) = 1^2 := inv_self_eq_one_eq (by linarith) (by linarith)
      have r₄ :b/c * (c/b) = 1^2 := inv_self_eq_one_eq (by linarith) (by linarith)
      have r₅ :b/d * (d/b) = 1^2 := inv_self_eq_one_eq (by linarith) (by linarith)
      have r₆ :c/d * (d/c) = 1^2 := inv_self_eq_one_eq (by linarith) (by linarith)

      -- 引入a,b,c,d 是正数的假设
      rcases hl with ⟨h1,⟨h2,⟨h3,h4 ⟩ ⟩ ⟩
      --证明a,b都大于0， 则a/b大于等于0
      have div_le_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ a / b := by
          apply le_of_lt
          exact div_pos ha hb
      -- 证明2+2=4
      have  two_add_two_eq_four : 2 + 2 = (4 : ℝ) := by
        simp[← one_add_one_eq_two,← three_add_one_eq_four,← two_add_one_eq_three, add_assoc]

      
      -- 利用AM-GM不等式four_mul_le_sq_add 推导出 2 * r ≤ a + b
      have four_mul_le_sq_add (a b : ℝ ) : 4 * a * b ≤ (a + b) ^ 2 := by
        calc 4 * a * b
          _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, two_add_two_eq_four.symm, add_mul, mul_assoc]
          _ ≤ a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
          _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
          _ = (a + b) ^ 2 := (add_sq a b).symm
      have two_mul_le_add_of_sq_eq_mul  {a b r : ℝ}
          (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : r ^ 2 = a * b) : 2 * r ≤ a + b := by
        apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg ha hb)
        conv_rhs => rw [← pow_two]
        convert four_mul_le_sq_add a b using 1
        rw [mul_mul_mul_comm, two_mul, two_add_two_eq_four, ← pow_two, ht, mul_assoc]

      --使用AM-GM 不等式
      have p₁:= two_mul_le_add_of_sq_eq_mul (div_le_zero h1 h2) (div_le_zero h2 h1) (r₁.symm)
      have p₂:= two_mul_le_add_of_sq_eq_mul (div_le_zero h1 h3) (div_le_zero h3 h1) (r₂.symm)
      have p₃:= two_mul_le_add_of_sq_eq_mul (div_le_zero h1 h4) (div_le_zero h4 h1) (r₃.symm)
      have p₄:= two_mul_le_add_of_sq_eq_mul (div_le_zero h2 h3) (div_le_zero h3 h2) (r₄.symm)
      have p₅:= two_mul_le_add_of_sq_eq_mul (div_le_zero h2 h4) (div_le_zero h4 h2) (r₅.symm)
      have p₆:= two_mul_le_add_of_sq_eq_mul (div_le_zero h3 h4) (div_le_zero h4 h3) (r₆.symm)


      rw[mul_one] at p₁ p₂ p₃ p₄ p₅ p₆
      --将多个不等式合并
      have o1 := add_lt_add t₁ t₂
      have o2 := add_lt_add t₃ t₄
      have O := add_lt_add o1 o2

      have g1 := add_le_add_three p₁ p₂ p₃
      have g2 := add_le_add_three p₄ p₅ p₆
      have G := add_le_add g1 g2

      rw [add] at O
      --不等式两边同时减去4
      have hab := sub_le_sub_right G 4
      simp only [←add_assoc] at hab O
      --得到目标不等式
      have temp := lt_of_le_of_lt hab O
      norm_num at temp

      -- 进行类型的提升
      have hrr :(x:ℝ)=↑⌊(b + c + d) / a⌋ + ↑⌊(a + c + d) / b⌋ + ↑⌊(a + b + d) / c⌋ + ↑⌊(a + b + c) / d⌋ := by simp[hr]
      -- 化简temp
      rw[←hrr] at temp
      -- 将实数的不等式 转换为 整数的不等式
      apply Int.cast_lt.mp at temp
      -- 使用add_one_le_iff 证明对于整数不等式 8<x 有9≤x
      have result:=Int.add_one_le_iff.mpr temp
      simp at result
      exact result
