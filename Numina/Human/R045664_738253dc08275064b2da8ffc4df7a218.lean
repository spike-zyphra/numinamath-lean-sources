import Mathlib


/-A line segment of length $5$ has one endpoint at $(1, 2)$ and the other endpoint at $(4, b)$. Find all possible values of $b$, separated by commas.-/
theorem algebra_18701 (b : ℝ) (h : Real.sqrt ((4 - 1)^2 + (b - 2)^2) = 5) :
    b = 6 ∨ b = -2 := by
-- 对h两边同时取平方
have t₁ : 0≤ Real.sqrt ((4 - 1)^2 + (b - 2)^2):= Real.sqrt_nonneg ((4 - 1)^2 + (b - 2)^2)
have t₂ : 0≤ (5:ℝ):= by linarith
-- 使用sq_eq_sq 策略  x^2=y^2 ↔ x=y
have p:= sq_eq_sq t₁ t₂
-- 分解p
obtain ⟨_,r⟩ := p
--利用x=y → x^2=y^2，得到两边取平方后相等的条件
apply r at h

have t₃ : 0≤ (4 - 1)^2 + (b - 2)^2 := Left.add_nonneg (sq_nonneg (4-1)) (sq_nonneg (b-2))
-- 去除根号
simp[Real.sq_sqrt t₃] at h

-- 根据代数计算得到 |(b-2)|  = 4
have h₁ : |(b-2)|  = 4:= by
  calc
  _ = √((b-2)^2) := by rw[Real.sqrt_sq_eq_abs]
  _ = √((4-1)^2+(b - 2)^2-(4-1)^2) := by ring_nf
  _ = √(5^2-(4-1)^2) :=by rw[h]
  _ = √(4^2) := by ring_nf
  _ = 4 := Real.sqrt_sq (by linarith)
--分类讨论 |b-2| 的取值情况
have h₂ :|(b-2)| = (b-2) ∨ |(b-2)| = -(b-2) := abs_choice (b-2)
--当（b-2）是正数的时候
apply Or.elim h₂
intro t
rw[t] at h₁
have r:b=6:= by
  calc
  _ = b-2 +2 := by ring
  _ = 4 +2 := by rw[h₁]
  _ = 6 := by ring
exact Or.inl r
--当（b-2）是负数的时候
intro t
rw[t] at h₁
have r:b=-2:= by
  calc
  _ =2-(-(b-2))  := by ring
  _ = 2-4:= by rw[h₁]
  _ = -2 := by ring
exact Or.inr r
