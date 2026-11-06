import Mathlib


/-Let $p(x)$ be a cubic polynomial such that $p(2) = 0,$ $p(-1) = 0,$ $p(4) = 6,$ and $p(5) = 8.$  Find $p(7).$-/
theorem algebra_18750 {p : ℝ → ℝ}
    (hp : ∃ a b c d : ℝ, p = fun x => a*x^3+b*x^2+c*x+d)
    (h2 : p 2 = 0) (h1 : p (-1) = 0) (h4 : p 4 = 6) (h5 : p 5 = 8) :
    p 7 = 16 / 3 := by
    rcases hp with ⟨a,b,c,d ,hp'⟩
    -- 化简h1 h2 h4 h5
    simp [hp'] at h2 h1 h4 h5
    norm_num at h2 h1 h4 h5
    have eq1 : 8 * a + 4 * b + 2 * c + d = 0 := by
      simp[mul_comm]
      exact h2
    have eq2 : -a + b - c + d = 0 := h1
   -- 由 p(4) = 6 得到第三个方程
    have eq3 : 64 * a + 16 * b + 4 * c + d = 6 := by
      simp[mul_comm]
      exact h4
    -- 由 p(5) = 8 得到第四个方程
    have eq4 : 125 * a + 25 * b + 5 * c + d = 8 := by
      simp[mul_comm]
      exact h5
    -- 消去 d，从 eq1 中表达 d
    have d_expr:d = -(8 * a + 4 * b + 2 * c) := by
      calc
       _ =  8 * a + 4 * b + 2 * c + d - (8 * a + 4 * b + 2 * c) := by ring
       _ = 0-(8 * a + 4 * b + 2 * c) := by rw[eq1]
       _ = -(8 * a + 4 * b + 2 * c) := by ring

    have eq2' : -a + b - c - (8 * a + 4 * b + 2 * c) = 0 := by
      calc
      _ = -a + b - c + d := by rw[d_expr];ring
      _ = 0 := eq2
    have eq2'' : -9 * a - 3 * b - 3 * c = 0 := by
      linarith

     -- 消去 b，得到 b 的表达式
    have b_expr : b = -3 * a - c := by
      calc
      _ = (-9 * a - 3 * b - 3 * c  + 3 * (3*a + c))/(-3) := by ring
      _ = (0+3 * (3*a + c))/(-3) := by rw[eq2''];
      _ = -3 * a - c := by ring

    -- 代入 eq3 中，得到关于 a 和 c 的方程
    have eq3' : 64 * a + 16 * (-3 * a - c) + 4 * c
            - (8 * a + 4 * (-3 * a - c) + 2 * c) = 6 :=  by
            rw[d_expr] at eq3
            rw[b_expr] at eq3
            exact eq3


    have eq3'' : 20 * a - 10 * c = 6 := by
      linarith
    -- 消去 c，得到 c 的表达式
    have c_expr : c = 2 * a - 3 / 5 := by
      linarith

    -- 代入 eq4 中，得到关于 a 的方程
    have eq4' : 125 * a + 25 * (-3 * a - ( 2 * a - 3 / 5 )) + 5 * (2 * a - 3 / 5) -
         (8 * a + 4 * (-3 * a - (2 * a - 3 / 5)) + 2 * (2 * a - 3 / 5)) = 8 := by
         rw[d_expr] at eq4
         rw[b_expr] at eq4
         rw[c_expr] at eq4
         exact eq4

    have eq4'' : 18 * a = -14/5 := by
      linarith
    -- 求得 a 的值
    have a_val : a = -7 / 45 := by
      linarith
    -- 求得 c, b, d 的值
    have c_val : c = 2 * (-7 / 45) - 3 / 5 := by
      rw[a_val] at c_expr
      exact c_expr
    have b_val : b = -3 * (-7 / 45) - (2 * (-7 / 45) - 3 / 5) := by
      rw[a_val ,c_val] at b_expr
      exact b_expr

    have d_val : d = -(8 * (-7 / 45) + 4 * (-3 * (-7 / 45) - (2 * (-7 / 45) - 3 / 5)) + 2 * (2 * (-7 / 45) - 3 / 5)) := by
      rw[a_val ,c_val,b_val] at d_expr
      exact d_expr
    norm_num at a_val b_val c_val d_val

    simp[hp',a_val,b_val,c_val,d_val]
    norm_num
