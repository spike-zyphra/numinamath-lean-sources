import Mathlib

-- 13. (6 points) Mathematician Wiener is the founder of cybernetics. At the ceremony where he was granted his Ph.D. from Harvard University, someone, curious about his youthful appearance, asked him about his age. Wiener's response was quite interesting. He said, “The cube of my age is a four-digit number, and the fourth power of my age is a six-digit number. These two numbers together use all the digits from 0 to 9 exactly once, without repetition or omission.” So, how old was Wiener that year? (Note: The cube of a number \(a\) is \(a \times a \times a\), and the fourth power of a number \(a\) is \(a \times a \times a \times a\))
theorem number_theory_102636 (age : ℕ)
    (h1 : (Nat.digits 10 (age ^ 3)).length = 4)
    (h2 : (Nat.digits 10 (age ^ 4)).length = 6) :
    (h3 : (Nat.digits 10 (age ^ 3)).toFinset ∪ (Nat.digits 10 (age ^ 4)).toFinset = Finset.range 10) →
    (h4 : Disjoint (Nat.digits 10 (age ^ 3)).toFinset (Nat.digits 10 (age ^ 4)).toFinset) →
    age = 18 := by
  set cube := age ^ 3
  set cube_digits := (Nat.digits 10 cube).toFinset
  set fourth := age ^ 4
  set fourth_digits := (Nat.digits 10 fourth).toFinset
  -- 18 【解答】解：先用估值的方法大概确定一下维纳的年龄范围. 根据 $17^{4}=83521,18^{4}=$ $104976,19^{4}=130321$, 根据题意可得: 他的年龄大于或等于 18 岁;再看, $18^{3}=5832,19^{3}=6859,21^{3}=9261,22^{3}=10648$, 说明维纳的年龄小于 22 岁.根据这两个范围可知可能是 $18 、 19 、 20 、 21$ 的一个数. 又因为 $20 、 21$ 无论是三次方还是四次方，它们的尾数分别都是： $0 、 1$, 与 “ 10 个数字全都用上了，不重也不漏”不符，所以不用考虑了. 只剩下 18、19 这两个数了. 一个一个试, $$ \begin{array}{c} 18 \times 18 \times 18=5832, \quad 18 \times 18 \times 18 \times 18=104976 ; \\ 19 \times 19 \times 19=6859, \quad 19 \times 19 \times 19 \times 19=130321 ; \end{array} $$
  have : fourth ≠ 0 := by
    have : Nat.digits 10 fourth ≠ [] := by
      exact List.ne_nil_of_length_eq_add_one h2
    exact Nat.digits_ne_nil_iff_ne_zero.mp this
  /-
  have age_ne_z : age ≠ 0 := by
    exact Nat.ne_zero_of_mul_ne_zero_right this
   -/
  have : fourth ≥ 10 ^ 5 := by
    --rw [show 5 = 6 - 1 by rfl, ←h2]
    have := Nat.base_pow_length_digits_le 10 fourth (by simp) this
    rw [h2] at this
    linarith
  have : cube < 10 ^ 4 := by
    rw [←h1]
    exact Nat.lt_base_pow_length_digits'
  have : age > 17 := by
    have : fourth > 17 ^ 4 := by
      linarith
    unfold fourth at this
    --nlinarith
    have _4_pos : 4 > 0 := by simp
    exact lt_of_pow_lt_pow_left' 4 this
  have : age < 22 := by
    have : cube < 22 ^ 3 := by
      linarith
    have _3_pos : 4 > 0 := by simp
    exact lt_of_pow_lt_pow_left' 3 this
  interval_cases age_eq : age <;>
  . subst age_eq
    native_decide
  -- 符合要求是 18 . 故答案为: 18 .
