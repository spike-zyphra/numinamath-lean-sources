import Mathlib

open Real

/- 4. Solve the system of equations $\left\{\begin{array}{l}3 x+\sqrt{3 x-y}+y=6, \\ 9 x^{2}+3 x-y-y^{2}=36 .\end{array}\right.$ -/
theorem algebra_162584 {x y : ℝ} (hx : 0 ≤ 3 * x - y) :
    3 * x + sqrt (3 * x - y) + y = 6 ∧  9 * x ^ 2 + 3 * x - y - y ^ 2 = 36 ↔
    (x = 2 ∧ y = -3) ∨ (x = 6 ∧ y = -18) := by
    apply Iff.intro
    {
        intro ⟨h1,h2⟩
        let u := sqrt (3 * x - y)
        let v := 3 * x + y

        -- Rewrite in terms of u and v
        have h1uv : v=6-u := by simp [u,v,←h1]; ring
        have h2uv_aux : u^2 * (6-u) + u^2 = 36 := by simp [←h1uv,u,←h2,sq_sqrt hx];ring
        have h2uv : u^3 - 7 * u^2 + 36 = 0 := by rw [←h2uv_aux];ring

        -- Factorize by selecting the integer root u=-2 and factoring the remaining quadratic polynomial
        have h_factored : u^3 - 7 * u^2 + 36 = (u+2) * (u-3) * (u-6) := by ring
        rw [h_factored] at h2uv

        -- We find the corresponding x and y for each root u
        have h_roots1 := mul_eq_zero.1 h2uv
        apply Or.elim h_roots1
        {
            intro h_aux
            have h_roots2 := mul_eq_zero.1 h_aux
            apply Or.elim h_roots2
            {
                -- The root u=-2 is not suitable because 0≤u
                intro hr1
                have hr1' : u = -2 :=eq_neg_of_add_eq_zero_left hr1
                simp [u] at hr1'
                have hs := sqrt_nonneg (3 * x - y)
                rw [hr1'] at hs
                norm_num at hs
            }
            {
                intro hr2
                have hr2' : u=3 := sub_eq_zero.1 hr2
                have hv' : 3*x+y = 3 := by rw [hr2'] at h1uv; norm_num at h1uv; exact h1uv
                apply Or.inl
                have hxy : 3*x-y = 9 := by rw [←sq_sqrt hx]; simp [u] at hr2';rw [hr2']; norm_num
                have hx' : x = 2 := by linarith
                have hy' : y = -3 := by linarith
                exact ⟨hx',hy'⟩
            }
        }
        {
            intro hr3
            have hr3' : u=6 := sub_eq_zero.1 hr3
            have hv' : 3*x+y = 0 := by rw [hr3'] at h1uv; norm_num at h1uv; exact h1uv
            apply Or.inr
            have hxy : 3*x-y = 36 := by rw [←sq_sqrt hx]; simp [u] at hr3';rw [hr3']; norm_num
            have hx' : x = 6 := by linarith
            have hy' : y = -18 := by linarith
            exact ⟨hx',hy'⟩
        }
    }
    {
        -- We verify that the pairs (x,y) we found are indeed solutions of the original system of equations
        intro hor
        apply Or.elim hor
        {
            intro hsol1
            have h9 : (9:ℝ) = 3^2 := by norm_num
            have h9' : sqrt 9 = 3 := by rw [h9,sqrt_sq (by norm_num)]
            simp [hsol1]; norm_num [h9']
        }
        {
            intro hsol2
            have h36 : (36:ℝ) = 6^2 := by norm_num
            have h36' : sqrt 36 = 6 := by rw [h36,sqrt_sq (by norm_num)]
            simp [hsol2]; norm_num [h36']
        }
    }