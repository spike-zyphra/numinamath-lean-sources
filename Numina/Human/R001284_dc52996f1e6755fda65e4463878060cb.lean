import Mathlib

/- January 1, 2000 was on a Saturday. On what day of the week was January 1, 1960? -/
theorem number_theory_22809 (n m1 m2: ℤ) (h1 : n % 7 = 6) (h2 : m1 = 40 / 4) (h3 : m2 = 40 - 40 / 4) :
    (n - m1 * 366 - m2 * 365) % 7 = 5 := by
        /- 简化 h2 和 h3 中的表达式 -/
        simp at h2 h3
        /- 将 h2 和 h3 代入主表达式 -/
        rw [h2, h3]
        /- 进一步简化表达式 -/
        simp
        /- 使用环代数规则化简 -/
        ring_nf
        calc (-14610 + n) % 7
             /- 使用整数模运算的加法规则：(a + b) % n = ((a % n) + (b % n)) % n -/
             = ((-14610) % 7 + n % 7) % 7 := Int.add_emod (-14610) n 7
             /- 代入已知条件 n % 7 = 6 -/
             _ = ((-14610) % 7 + 6) % 7 := by rw [h1]
             /- 计算 -14610 % 7 = 6 -/
             _ = (6 + 6) % 7 := by ring_nf
             /- 计算 6 + 6 = 12 -/
             _ = 12 % 7 := by ring_nf
             /- 最终计算 12 % 7 = 5，表示是星期五 -/
             _ = 5 := by ring_nf
