import Mathlib

/- Anna, Bertram, Carli, and David have a competition to see which of them can hold their breath for the longest time period, in minutes. If Bertram, Carli, and David add their times together, the resulting sum is three times the length of time that Anna can hold her breath. Similarly, if Anna, Carli, and David sum their times, the result is four times Bertram's time period, and if Anna, Bertram, and David sum their times, the result is twice Carli's time. Finally, eight times Anna's time plus ten times Bertram's time plus six times Carli's time equals two fifths of an hour. If the length of time that David can hold his breath is expressed in minutes as a simplified fraction, what is the sum of the numerator and the denominator? -/
theorem algebra_21574     (a b c d : ℚ)
    -- h₀: 所有时间都是正数
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    -- h₁: b + c + d = 3a (第一个条件)
    (h₁ : b + c + d = 3 * a)
    -- h₂: a + c + d = 4b (第二个条件)
    (h₂ : a + c + d = 4 * b)
    -- h₃: a + b + d = 2c (第三个条件)
    (h₃ : a + b + d = 2 * c)
    -- h₄: 8a + 10b + 6c = 24分钟 (2/5小时 = 24分钟)
    (h₄ : 8 * a + 10 * b + 6 * c = 2 / 5 * 60) :
    -- 结论：d表示为最简分数时，分子加分母等于28
    d.num + d.den = 28 := by
        -- d = 13/15 (这个结果可以通过解方程得到)
        have h : d = 13 / 15 := by linarith
        subst h
        native_decide
