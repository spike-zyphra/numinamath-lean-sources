import Mathlib

/-
* Problem Statement:
Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ satisfying the equation
\[ f(x+f(x+y))+f(x y)=x+f(x+y)+y f(x) \]
for all real numbers $x$ and $y$.
* Solution
Clearly, each of the functions $x \mapsto x$ and $x \mapsto 2-x$ satisfies (1). It suffices now to show that they are the only solutions to the problem.  Suppose that $f$ is any function satisfying (1). Then setting $y=1$ in (1), we obtain  $$ f(x+f(x+1))=x+f(x+1) $$  in other words, $x+f(x+1)$ is a fixed point of $f$ for every $x \in \mathbb{R}$. We distinguish two cases regarding the value of $f(0)$. Case 1. $\quad f(0) \neq 0$. By letting $x=0$ in (1), we have  $$ f(f(y))+f(0)=f(y)+y f(0) $$  So, if $y_{0}$ is a fixed point of $f$, then substituting $y=y_{0}$ in the above equation we get $y_{0}=1$. Thus, it follows from (2) that $x+f(x+1)=1$ for all $x \in \mathbb{R}$. That is, $f(x)=2-x$ for all $x \in \mathbb{R}$. Case 2. $\quad f(0)=0$.  By letting $y=0$ and replacing $x$ by $x+1$ in (1), we obtain  $$ f(x+f(x+1)+1)=x+f(x+1)+1 $$  From (1), the substitution $x=1$ yields  $$ f(1+f(y+1))+f(y)=1+f(y+1)+y f(1) $$  By plugging $x=-1$ into (2), we see that $f(-1)=-1$. We then plug $y=-1$ into (4) and deduce that $f(1)=1$. Hence, (4) reduces to  $$ f(1+f(y+1))+f(y)=1+f(y+1)+y $$  Accordingly, if both $y_{0}$ and $y_{0}+1$ are fixed points of $f$, then so is $y_{0}+2$. Thus, it follows from (2) and (3) that $x+f(x+1)+2$ is a fixed point of $f$ for every $x \in \mathbb{R}$; i.e.,  $$ f(x+f(x+1)+2)=x+f(x+1)+2 $$  Replacing $x$ by $x-2$ simplifies the above equation to  $$ f(x+f(x-1))=x+f(x-1) $$  On the other hand, we set $y=-1$ in (1) and get  $$ f(x+f(x-1))=x+f(x-1)-f(x)-f(-x) $$  Therefore, $f(-x)=-f(x)$ for all $x \in \mathbb{R}$. Finally, we substitute $(x, y)$ by $(-1,-y)$ in (1) and use the fact that $f(-1)=-1$ to get  $$ f(-1+f(-y-1))+f(y)=-1+f(-y-1)+y $$  Since $f$ is an odd function, the above equation becomes  $$ -f(1+f(y+1))+f(y)=-1-f(y+1)+y $$  By adding this equation to (5), we conclude that $f(y)=y$ for all $y \in \mathbb{R}$.
-/
theorem algebra_24562 :
    {f : ℝ → ℝ | ∀ x y, f (x + f (x + y)) + f (x * y) = x + f (x + y) + y * f x} =
    {fun x => x, fun x => 2 - x} := by
  --Suppose that $f$ is any function satisfying (1).
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · --It suffices now to show that they are the only solutions to the problem.
    intro h
    -- Then setting $y=1$ in (1), we obtain  $$ f(x+f(x+1))=x+f(x+1) $$.
    have fixed (x : ℝ) := h x 1
    -- In other words, $x+f(x+1)$ is a fixed point of $f$ for every $x \in \mathbb{R}$.
    simp only [mul_one, one_mul, add_left_inj] at fixed
    -- We distinguish two cases regarding the value of $f(0)$.
    by_cases f0 : f 0 ≠ 0
    · -- Case 1. $\quad f(0) \neq 0$.
      right
      ext x
      -- So, if $y_{0}$ is a fixed point of $f$, then substituting $y=y_{0}$ in the above equation we get $y_{0}=1$.
      have {y} (hy : f y = y) : y = 1 := by
        -- By letting $y=0$ and replacing $x$ by $x+1$ in (1), we obtain  $$ f(x+f(x+1)+1)=x+f(x+1)+1 $$
        have := h 0 y
        simp only [zero_add, hy, zero_mul, add_right_inj] at this
        rwa [right_eq_mul₀ f0] at this
      -- Thus, it follows from (2) that $x+f(x+1)=1$ for all $x \in \mathbb{R}$.
      -- Here we have substituted `x` to `x - 1`.
      have f_eq := this (fixed (x - 1))
      simp only [sub_add_cancel] at f_eq
      -- That is, $f(x)=2-x$ for all $x \in \mathbb{R}$.
      linarith
    · -- Case 2. $\quad f(0)=0$.
      left
      ext x
      simp only [ne_eq, Decidable.not_not] at f0
      -- By letting $y=0$ and replacing $x$ by $x+1$ in (1), we obtain  $$ f(x+f(x+1)+1)=x+f(x+1)+1 $$
      have fixed' (x : ℝ) := h (x + 1) 0
      simp only [add_zero, mul_zero, f0, zero_mul] at fixed'
      -- From (1), the substitution $x=1$ yields  $$ f(1+f(y+1))+f(y)=1+f(y+1)+y f(1) $$
      have eq (y : ℝ) := h 1 y
      simp only [one_mul] at eq
      -- By plugging $x=-1$ into (2), we see that $f(-1)=-1$.
      have f_neg_1 := fixed (-1)
      simp only [neg_add_cancel, f0, add_zero] at f_neg_1
      -- We then plug $y=-1$ into (4) and deduce that $f(1)=1$.
      have f1 := eq (-1)
      simp only [add_neg_cancel, f0, add_zero, f_neg_1, neg_mul, one_mul] at f1
      replace f1 : f 1 = 1 := by linarith
      -- Hence, (4) reduces to  $$ f(1+f(y+1))+f(y)=1+f(y+1)+y $$
      simp only [f1, mul_one] at eq
      -- Accordingly, if both $y_{0}$ and $y_{0}+1$ are fixed points of $f$, then so is $y_{0}+2$.
      have fixed_point_y₀_add_2 {y₀} (hy₀ : f y₀ = y₀) (hy₀' : f (y₀ + 1) = y₀ + 1) :
          f (y₀ + 2) = y₀ + 2 := by
        specialize eq y₀
        rw [add_comm] at hy₀'
        simp only [hy₀', hy₀, add_left_inj] at eq
        convert eq using 1
        · congr 1
          ring
        · ring
      -- Thus, it follows from (2) and (3) that $x+f(x+1)+2$ is a fixed point of $f$ for every $x \in \mathbb{R}$; i.e.,  $$ f(x+f(x+1)+2)=x+f(x+1)+2 $$
      have fixed'' (x : ℝ) :=
        fixed_point_y₀_add_2 (fixed x) (by convert fixed' x using 1 <;> ring_nf)
      -- Replacing $x$ by $x-2$ simplifies the above equation to  $$ f(x+f(x-1))=x+f(x-1) $$
      replace fixed'' (x : ℝ) := fixed'' (x - 2)
      ring_nf at fixed''
      -- Therefore, $f(-x)=-f(x)$ for all $x \in \mathbb{R}$.
      have odd (x : ℝ) : f (-x) = -f x := by
        -- On the other hand, we set $y=-1$ in (1) and get  $$ f(x+f(x-1))=x+f(x-1)-f(x)-f(-x) $$
        have := h x (-1)
        simpa [add_comm x (-1), fixed''] using this
      -- Finally, we substitute $(x, y)$ by $(-1,-y)$ in (1) and use the fact that $f(-1)=-1$ to get  $$ f(-1+f(-y-1))+f(y)=-1+f(-y-1)+y $$
      have (y : ℝ) := h (-1) (-y)
      simp only [mul_neg, neg_mul, one_mul, neg_neg, f_neg_1, mul_one] at this
      -- Since $f$ is an odd function, the above equation becomes  $$ -f(1+f(y+1))+f(y)=-1-f(y+1)+y $$
      simp only [← neg_add, odd] at this
      specialize eq x
      specialize this x
      -- By adding this equation to (5), we conclude that $f(y)=y$ for all $y \in \mathbb{R}$.
      linarith
  · --Clearly, each of the functions $x \mapsto x$ and $x \mapsto 2-x$ satisfies (1).
    rintro (h | h)
    · simp [h, mul_comm]
    · simp only [h]
      ring_nf
      simp
