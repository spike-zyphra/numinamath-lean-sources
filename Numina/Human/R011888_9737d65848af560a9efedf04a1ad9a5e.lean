import Mathlib

open Real

/- 1 Inequality of series derived from the functional inequality $\ln (1+x)>x-\frac{x^2}{2}(x>0)$ -/
theorem inequalities_601576 (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)(r:Summable fun i => a i * (log (1 + a i) - (a i - a i ^ 2 / 2))) :
    ∑' n, a n * (log (1 + a n) - (a n - a n ^ 2 / 2)) > 0 := by
--step0:have ln_inequality (x : ℝ) (hx : x &gt; 0) : log (x + 1) &gt; x - x^2/2
   have ln_inequality (x : ℝ) (hx : x > 0) : log (x + 1) > x - x^2/2 := by
  --def of f
     let f (x:ℝ) :ℝ := log (x + 1) - x + 1/2*x^2
  --continuousOn log(x+1)
     have p : ContinuousOn (fun x => log (x + 1)) (Set.Ici 0) := by 
       refine ContinuousOn.log ?_ ?_
       fun_prop
       intro x hx
       by_contra hy
       simp only [interior_Ici,Set.mem_Ici] at hx
       linarith
  --differentiableAt ℝ log(x+1)   
     have q (x:ℝ )(hx:x>0):DifferentiableAt ℝ (fun x => log (x + 1)) x := by 
       refine DifferentiableAt.log ?_ ?_
       fun_prop;linarith
  --differentiableAt ℝ log(x+1)-x
     have q (x:ℝ )(hx:x>0):DifferentiableAt ℝ (fun x => log (x + 1)-x) x := by 
       refine (DifferentiableAt.sub_iff_right (q x hx)).mpr ?_
       fun_prop
  --stricmonoOn f [0,+inf)
     have h : StrictMonoOn f (Set.Ici 0) := by
       have t1(x:ℝ)(hx:x>0):deriv f x= (fun x => 1/(x+1)-(1-x)) x := by
         unfold f
         rw [deriv_add,deriv_sub,deriv_const_mul,deriv_id'',deriv_pow,deriv.log]
         simp;ring_nf;fun_prop;by_contra hy;linarith;fun_prop;tauto;fun_prop;tauto;fun_prop
       have t2(x:ℝ)(hx:x>0): ∀ x∈ interior (Set.Ici 0), 0 < (deriv f x) :=by
         have t3(x:ℝ)(hx:x>0): 0<1/(x+1)-(1-x) := by
           simp
           rw [←one_div (x+1)]
           apply (lt_div_iff₀ ?_).mpr ?_
           ring_nf;
           have p : 0<x :=by exact hx;
           linarith;ring_nf;simp;exact sq_pos_of_pos hx
         simp;intro y hy;let t4:= (t3 y) hy;let t5 := (t1 y) hy;rw[t5];tauto
       apply strictMonoOn_of_deriv_pos
       · exact convex_Ici 0
       · unfold f;fun_prop
       · tauto     
  --f(0)=0
     have h1 : f (0)=0 :=by unfold f;simp
  --final proof
     have h2 : 0<f (x) :=by
       rw[← h1]
       apply (StrictMonoOn.lt_iff_lt h ?_ ?_).mpr
       tauto
       exact Set.left_mem_Ici
       exact Set.mem_Ici_of_Ioi hx
     unfold f at h2
     linarith
--step1.have q(n:ℕ ):a n \* (log (1 + a n) - (a n - a n ^ 2 / 2)) &gt; 0
   have q(n:ℕ ):a n * (log (1 + a n) - (a n - a n ^ 2 / 2)) > 0 :=by 
     refine mul_pos (ha n) ?_
     let q1:=ln_inequality (a n) (ha n)
     simp;rw[add_comm];tauto
   have q1(n:ℕ ):a n * (log (1 + a n) - (a n - a n ^ 2 / 2)) ≥ 0 :=by exact le_of_lt (q n) 
--step2:∑' n, a n \* (log (1 + a n) - (a n - a n ^ 2 / 2)) &gt; 0
   apply tsum_pos
   tauto;tauto;tauto;exact USize.size