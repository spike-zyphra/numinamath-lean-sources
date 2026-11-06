import Mathlib

/-
problem

Solve the system of equations $←{}\begin{array}{l}2x-y=5\\7x-3y=20\end{array}\right.$.
-/

/-
solution

To solve the system of equations $←{}\begin{array}{l}2x-y=5 \quad (1)\\7x-3y=20 \quad (2)\end{array}\right.$, we follow these steps:

1. **Multiply equation (1) by 3** to eliminate $y$ when we subtract this result from equation (2). This gives us:
   \[
      3(2x-y) = 3(5) \implies 6x-3y=15 \quad (3)
         \]

         2. **Subtract equation (3) from equation (2)** to find the value of $x$:
            \[
               (7x-3y) - (6x-3y) = 20 - 15 \implies x = 5
                  \]

                  3. **Substitute $x=5$ back into equation (1)** to find the value of $y$:
                     \[
                        2(5) - y = 5 \implies 10 - y = 5 \implies y = 5
                           \]

                           Therefore, the solution to the original system of equations is $\boxed{\left\{\begin{array}{l}x=5\\y=5\end{array}\right.}$.
-/

theorem algebra_8997 {x y : ℝ} (h1 : 2 * x - y = 5) (h2 : 7 * x - 3 * y = 20) :
    x = 5 ∧ y = 5 := by
      -- determine $y$ by eqeuation h1
      have yeq : y = 2 * x - 5 := by
        apply_fun (· + y) at h1
        simp only [sub_add_cancel] at h1
        exact eq_sub_of_add_eq' (id (Eq.symm h1))
      rw [yeq] at h2
      -- simplify LHS of equation h2
      have : 7 * x - 3 * (2 * x - 5) = x + 15 := by ring
      rw [this] at h2
      apply_fun (· - 15) at h2
      simp only [add_sub_cancel_right] at h2
      -- just simple calculation
      have : 20 - 15 = (5 : ℝ) := by
        norm_cast
      -- thus $x = 20 - 15 = 5$
      rw [this] at h2
      constructor
      · exact h2
      · -- since $x = 5$ and $y = 2 * x - 5$
        rw [yeq, h2]
        norm_cast