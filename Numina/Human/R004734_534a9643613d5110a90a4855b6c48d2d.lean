import Mathlib
set_option maxHeartbeats 0

/-It is known that the function\(a : \mathbb{N} \to \mathbb{Z}\) satisfies the following conditions: \(a(1) = 1\)\(a(2) = 3\) For all natural numbers\(n > 0\), the recurrence relation\(a(n+2) =| a(n+1)|- a(n)\) Solve: sum of the first 100 terms\(\sum_{i=1}^{100} a(i) = 100\)-/
theorem algebra_312615(a:ℕ→ℤ)(ha1:a 1=1)(ha2:a 2=3)(ha:∀ n,a (n+2)=abs (a (n+1))- a n):∑ i∈Finset.Ico 1 101, a i=89 :=by 
-- Step1:To prove the statement, we need to have a (k+9)=a k for all k∈ℕ
  have step1:(∀k≥1,a (k+9)=a k):=by 
   -- Induction on k
    intro k
    induction' k using Nat.case_strong_induction_on with k ih
    -- Proof split into two cases
    -- Case k=0
    · intro h
      tauto 
    -- Case general case
    · intro h
      -- Split the goal into three goals
      by_cases h1:k≥2
      rw[ha]
      have h1:a (k+1)=abs (a k)-a (k-1):=by 
        let h1':=ha (k-1) 
        have k1:k-1+1=k:=by omega
        have k2:k-1+2=k+1:=by omega
        rw[k1,k2] at h1'
        tauto
      rw[h1]
      have h2:k+8+1=k+9:=by omega
      rw[h2]
      have h3:a (k+9)=a k:=by apply ih;all_goals omega
      have h4: a (k+8)=a (k-1):=by 
        have w:k+8=k-1+9:=by omega
        rw[w]
        apply ih;all_goals omega
      simp only [h3,h4]
      -- Classify discussion
      have hk:k=0∨k=1:=by omega
      -- Subgoal:k=0
      rcases hk with hk | hk
      simp[hk]
      have ha3:a 3=2:=by rw[ha];ring_nf;rw[ha2,ha1];norm_num
      have ha4:a 4=-1:=by rw[ha];ring_nf;rw[ha3,ha2];norm_num
      have ha5:a 5=-1:=by rw[ha];ring_nf;rw[ha4,ha3];norm_num
      have ha6:a 6=2:=by rw[ha];ring_nf;rw[ha5,ha4];norm_num
      have ha7:a 7=3:=by rw[ha];ring_nf;rw[ha6,ha5];norm_num
      have ha8:a 8=1:=by rw[ha];ring_nf;rw[ha7,ha6];norm_num
      have ha9:a 9=-2:=by rw[ha];ring_nf;rw[ha8,ha7];norm_num
      have ha10:a 10=1:=by rw[ha];ring_nf;rw[ha9,ha8];norm_num
      simp[ha1]
      tauto
      -- Prove k=1
      simp[hk]
      have ha3:a 3=2:=by rw[ha];ring_nf;rw[ha2,ha1];norm_num
      have ha4:a 4=-1:=by rw[ha];ring_nf;rw[ha3,ha2];norm_num
      have ha5:a 5=-1:=by rw[ha];ring_nf;rw[ha4,ha3];norm_num
      have ha6:a 6=2:=by rw[ha];ring_nf;rw[ha5,ha4];norm_num
      have ha7:a 7=3:=by rw[ha];ring_nf;rw[ha6,ha5];norm_num
      have ha8:a 8=1:=by rw[ha];ring_nf;rw[ha7,ha6];norm_num
      have ha9:a 9=-2:=by rw[ha];ring_nf;rw[ha8,ha7];norm_num
      have ha10:a 10=1:=by rw[ha];ring_nf;rw[ha9,ha8];norm_num 
      have ha11:a 11=3:=by rw[ha];ring_nf;rw[ha10,ha9];norm_num
      simp[ha11,ha2]
  -- Step2:Split the summation using periodicity.
  have step2_1:∑ i∈Finset.Ico 1 101, a i=(∑ i∈Finset.Ico 1 10, a i) +(∑ i∈Finset.Ico 10 101, a i):=by refine Eq.symm (Finset.sum_Ico_consecutive a ?_ ?_) ;all_goals omega
  have step2_2:∑ i∈Finset.Ico 10 101, a i=(∑ i∈Finset.Ico 10 19, a i) +∑ i∈Finset.Ico 19 101, a i:=by refine Eq.symm (Finset.sum_Ico_consecutive a ?_ ?_) ;all_goals omega
  have step2_3:∑ i∈Finset.Ico 19 101, a i=(∑ i∈Finset.Ico 19 28, a i) +∑ i∈Finset.Ico 28 101, a i:=by refine Eq.symm (Finset.sum_Ico_consecutive a ?_ ?_) ;all_goals omega
  have step2_4:∑ i∈Finset.Ico 28 101, a i=(∑ i∈Finset.Ico 28 37, a i) +∑ i∈Finset.Ico 37 101, a i:=by refine Eq.symm (Finset.sum_Ico_consecutive a ?_ ?_) ;all_goals omega
  have step2_5:∑ i∈Finset.Ico 37 101, a i=(∑ i∈Finset.Ico 37 46, a i) +∑ i∈Finset.Ico 46 101, a i:=by refine Eq.symm (Finset.sum_Ico_consecutive a ?_ ?_) ;all_goals omega
  have step2_6:∑ i∈Finset.Ico 46 101, a i=(∑ i∈Finset.Ico 46 55, a i) +∑ i∈Finset.Ico 55 101, a i:=by refine Eq.symm (Finset.sum_Ico_consecutive a ?_ ?_) ;all_goals omega
  have step2_7:∑ i∈Finset.Ico 55 101, a i=(∑ i∈Finset.Ico 55 64, a i) +∑ i∈Finset.Ico 64 101, a i:=by refine Eq.symm (Finset.sum_Ico_consecutive a ?_ ?_) ;all_goals omega
  have step2_8:∑ i∈Finset.Ico 64 101, a i=(∑ i∈Finset.Ico 64 73, a i) +∑ i∈Finset.Ico 73 101, a i:=by refine Eq.symm (Finset.sum_Ico_consecutive a ?_ ?_) ;all_goals omega
  have step2_9:∑ i∈Finset.Ico 73 101, a i=(∑ i∈Finset.Ico 73 82, a i) +∑ i∈Finset.Ico 82 101, a i:=by refine Eq.symm (Finset.sum_Ico_consecutive a ?_ ?_) ;all_goals omega
  have step2_10:∑ i∈Finset.Ico 82 101, a i=(∑ i∈Finset.Ico 82 91, a i) +∑ i∈Finset.Ico 91 101, a i:=by refine Eq.symm (Finset.sum_Ico_consecutive a ?_ ?_) ;all_goals omega
  have step2_11:∑ i∈Finset.Ico 91 101, a i=(∑ i∈Finset.Ico 91 100, a i) +∑ i∈Finset.Ico 100 101, a i:=by refine Eq.symm (Finset.sum_Ico_consecutive a ?_ ?_) ;all_goals omega
  --Step3:Calculate each period step by step.
  have step3_1:∑ i∈Finset.Ico 10 19, a i=∑ i∈Finset.Ico 1 10, a (i+9):=rfl
  have step3_1':∑ i∈Finset.Ico 10 19, a i=∑ i∈Finset.Ico 1 10, a i:=by 
    rw[step3_1]
    apply Finset.sum_congr
    rfl
    intro x hx
    apply step1
    exact Finset.min_le_of_eq hx rfl
  have step3_2:∑ i∈Finset.Ico 19 28, a i=∑ i∈Finset.Ico 10 19, a (i+9):=rfl
  have step3_2':∑ i∈Finset.Ico 19 28, a i=∑ i∈Finset.Ico 10 19, a i:=by
    rw[step3_2]
    apply Finset.sum_congr
    rfl
    intro x hx
    apply step1
    have hmin:10≤x:=by exact Finset.min_le_of_eq hx rfl
    linarith
  have step3_3:∑ i∈Finset.Ico 28 37, a i=∑ i∈Finset.Ico 19 28, a (i+9):=rfl
  have step3_3':∑ i∈Finset.Ico 28 37, a i=∑ i∈Finset.Ico 19 28, a i:=by
    rw[step3_3]
    apply Finset.sum_congr
    rfl
    intro x hx
    apply step1
    have hmin:19≤x:=by exact Finset.min_le_of_eq hx rfl
    linarith
  have step3_4:∑ i∈Finset.Ico 37 46, a i=∑ i∈Finset.Ico 28 37, a (i+9):=rfl
  have step3_4':∑ i∈Finset.Ico 37 46, a i=∑ i∈Finset.Ico 28 37, a i:=by
    rw[step3_4]
    apply Finset.sum_congr
    rfl
    intro x hx
    apply step1
    have hmin:28≤x:=by exact Finset.min_le_of_eq hx rfl
    linarith
  have step3_5:∑ i∈Finset.Ico 46 55, a i=∑ i∈Finset.Ico 37 46, a (i+9):=rfl
  have step3_5':∑ i∈Finset.Ico 46 55, a i=∑ i∈Finset.Ico 37 46, a i:=by
    rw[step3_5]
    apply Finset.sum_congr
    rfl
    intro x hx
    apply step1
    have hmin:37≤x:=by exact Finset.min_le_of_eq hx rfl
    linarith
  have step3_6:∑ i∈Finset.Ico 55 64, a i=∑ i∈Finset.Ico 46 55, a (i+9):=rfl
  have step3_6':∑ i∈Finset.Ico 55 64, a i=∑ i∈Finset.Ico 46 55, a i:=by
    rw[step3_6]
    apply Finset.sum_congr
    rfl
    intro x hx
    apply step1
    have hmin:46≤x:=by exact Finset.min_le_of_eq hx rfl
    linarith
  have step3_7:∑ i∈Finset.Ico 64 73, a i=∑ i∈Finset.Ico 55 64, a (i+9):=rfl
  have step3_7':∑ i∈Finset.Ico 64 73, a i=∑ i∈Finset.Ico 55 64, a i:=by
    rw[step3_7]
    apply Finset.sum_congr
    rfl
    intro x hx
    apply step1
    have hmin:55≤x:=by exact Finset.min_le_of_eq hx rfl
    linarith
  have step3_8:∑ i∈Finset.Ico 73 82, a i=∑ i∈Finset.Ico 64 73, a (i+9):=rfl
  have step3_8':∑ i∈Finset.Ico 73 82, a i=∑ i∈Finset.Ico 64 73, a i:=by
    rw[step3_8]
    apply Finset.sum_congr
    rfl
    intro x hx
    apply step1
    have hmin:64≤x:=by exact Finset.min_le_of_eq hx rfl
    linarith
  have step3_9:∑ i∈Finset.Ico 82 91, a i=∑ i∈Finset.Ico 73 82, a (i+9):=rfl
  have step3_9':∑ i∈Finset.Ico 82 91, a i=∑ i∈Finset.Ico 73 82, a i:=by
    rw[step3_9]
    apply Finset.sum_congr
    rfl
    intro x hx
    apply step1
    have hmin:73≤x:=by exact Finset.min_le_of_eq hx rfl
    linarith
  have step3_10:∑ i∈Finset.Ico 91 100, a i=∑ i∈Finset.Ico 82 91, a (i+9):=rfl
  have step3_10':∑ i∈Finset.Ico 91 100, a i=∑ i∈Finset.Ico 82 91, a i:=by
    rw[step3_10]
    apply Finset.sum_congr
    rfl
    intro x hx
    apply step1
    have hmin:82≤x:=by exact Finset.min_le_of_eq hx rfl
    linarith
  --Step4:Use step 2 and step 3 to calculate the final result.
  have step4:∑ i∈Finset.Ico 1 101, a i=89:=by
    rw[step2_1,step2_2,step2_3,step2_4,step2_5,step2_6,step2_7,step2_8,step2_9,step2_10,step2_11]
    simp[step3_1',step3_2',step3_3',step3_4',step3_5',step3_6',step3_7',step3_8',step3_9',step3_10',← add_assoc]
    ring_nf
    have eq1:∑ i ∈ Finset.Ico 1 10, a i=8:=by
      have ha3:a 3=2:=by rw[ha];ring_nf;rw[ha2,ha1];norm_num
      have ha4:a 4=-1:=by rw[ha];ring_nf;rw[ha3,ha2];norm_num
      have ha5:a 5=-1:=by rw[ha];ring_nf;rw[ha4,ha3];norm_num
      have ha6:a 6=2:=by rw[ha];ring_nf;rw[ha5,ha4];norm_num
      have ha7:a 7=3:=by rw[ha];ring_nf;rw[ha6,ha5];norm_num
      have ha8:a 8=1:=by rw[ha];ring_nf;rw[ha7,ha6];norm_num
      have ha9:a 9=-2:=by rw[ha];ring_nf;rw[ha8,ha7];norm_num
      have h:∑ i ∈ Finset.Ico 1 10, a i=(a 1)+(a 2)+(a 3)+(a 4)+(a 5)+(a 6)+(a 7)+(a 8)+(a 9):=by 
        simp[add_assoc]
        have h':0=∑ i ∈ Finset.Ico 10 10, a i:=rfl
        have h'':a 9+0=∑ i ∈ Finset.Ico 9 10,a i:=by rw[h'];exact rfl
        rw[add_zero] at h''
        rw[h'']
        exact rfl
      simp[ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9] at h
      tauto
    have ha100:a 100=a 1:=by simp[step1]
    rw[ha1] at ha100
    simp[eq1,ha100]
  tauto


      




    

      


        
        



        





        
