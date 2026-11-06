import Mathlib

/- What is the least common multiple of the first ten positive integers? -/
theorem algebra_19630 : lcm (lcm (lcm (lcm (lcm (lcm (lcm (lcm (lcm 1 2) 3) 4) 5) 6) 7) 8) 9) 10 = 2520 := by
  -- 计算1和2的最小公倍数：2
  rw [show (lcm 1 2 = 2) by decide]
  -- 计算2和3的最小公倍数：6
  rw [show (lcm 2 3= 6) by decide]
  -- 计算6和4的最小公倍数：12
  rw [show (lcm 6 4 = 12) by decide]
  -- 计算12和5的最小公倍数：60
  rw [show (lcm 12 5 = 60) by decide]
  -- 计算60和6的最小公倍数：60（因为60已经是6的倍数）
  rw [show (lcm 60 6 = 60) by decide]
  -- 计算60和7的最小公倍数：420
  rw [show (lcm 60 7 = 420) by decide]
  -- 计算420和8的最小公倍数：840
  rw [show (lcm 420 8 = 840) by decide]
  -- 计算840和9的最小公倍数：2520
  rw [show (lcm 840 9 = 2520) by decide]
  -- 计算2520和10的最小公倍数：2520（因为2520已经是10的倍数）
  rw [show (lcm 2520 10 = 2520) by decide]
