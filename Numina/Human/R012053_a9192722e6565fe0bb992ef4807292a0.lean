import Mathlib

/--8th Irish 1995 Problem A2 Find all integers n for which x^2 + n*x*y + y^2 = 1
has infinitely many distinct integer solutions x, y. -/

--if the set of solutions to the equations with n is infinite, then also the set of solutions to the equation with -n is infinite
lemma reflection_of_roots (n : ℤ) (_ : n > 0) :
    {y : ℤ × ℤ | y.1 ^ 2 + n * y.1 * y.2 + y.2 ^ 2 = 1}.Infinite ↔
    {y : ℤ × ℤ | y.1 ^ 2 + (-n) * y.1 * y.2 + y.2 ^ 2 = 1}.Infinite := by
  let f : ℤ × ℤ → ℤ × ℤ := fun y => (y.1,-y.2)
  let s := {y : ℤ × ℤ | y.1 ^ 2 + n * y.1 * y.2 + y.2 ^ 2 = 1}
  let t := {y : ℤ × ℤ | y.1 ^ 2 + (-n) * y.1 * y.2 + y.2 ^ 2 = 1}
  have image_eq : f '' s = t := by
    simp[f,s,t]
    ext x
    constructor
    · intro h
      simp at h ⊢
      obtain ⟨a,b,hab,hp⟩ := h
      rw[← hp]
      simp
      exact hab
    · intro h
      simp at h ⊢
      --in fact it suffices to send a solution for the equation in n, (x1,x2), to (x1,-x2) which is a solution for the equation in -n
      --this way one finds a bijection of the sets.
      use x.1, -x.2
      exact ⟨by linarith, by norm_num⟩
  simp[s,t] at image_eq ⊢
  rw[← image_eq]
  symm
  apply Set.infinite_image_iff
  unfold Set.InjOn
  intro x hx y hy hxy
  simp[f] at hxy
  exact Prod.ext_iff.mpr hxy

--if n > 2, then given the solution (1,0) we can generate infinitely many solutions iterating the transformation f : ℤ × ℤ → ℤ × ℤ defined by f(x,y) = (n*x + y, -x)
lemma abundance_of_solutions {n : ℤ} (_ : n > 2) :
    let s : Set (ℤ × ℤ) := {(x, y) | x ^ 2 + n * x * y + y ^ 2 = 1}
    let f : ℤ × ℤ → ℤ × ℤ := fun x => (n * x.1 + x.2, -x.1)
    let g : ℕ → ℤ × ℤ := fun n => Nat.iterate f n (1,0)
    ∀ (x : ℕ), g x ∈ s:= by 
  intro s f g x
  induction x with
  --the 0^th case is trivial since it is (1,0)
  | zero =>
    simp[g, s]
  | succ d hd =>
    --in the inductive step, just develop all the terms and check that the result is still a solution of the equation x^2 + nxy + y^2 = 1
    simp[g, s] at hd ⊢
    rw[← Function.iterate_succ_apply, Function.iterate_succ_apply' f d (1, 0)]
    simp at hd ⊢
    rw[add_sq, mul_add, add_mul]
    ring_nf
    rw[add_comm]
    linarith

--if |x| ≥ 2 then x^2 + x*y + y^2 > 1
lemma bound_of_abs_bound_one {x : ℤ} (y : ℤ) (h : |x| ≥ 2) : 
    x ^ 2 + x * y + y ^ 2 > (1 : ℝ) := by 
  -- we have |xy| ≤ (x^2 + y^2) / 2 and hence x^2 + y^2 + xy ≥ (x^2 + y^2) / 2 by a chain of inequalities
  have ineq1 : (x : ℝ) ^ 2 + y ^ 2 + x * y ≥ x ^ 2 + y ^ 2 + - |x * y| := by 
    exact add_le_add (by rfl) (by norm_cast; exact neg_abs_le (x * y))
  have ineq2 : |x * y| ≤ (x ^ 2 + y ^ 2) / (2 : ℝ) := by 
    rw[Int.cast_abs, abs_le]
    constructor
    · have : (x + y) ^ 2 ≥ 0 := by exact sq_nonneg (x + y)
      rw[add_sq] at this
      rify at this
      norm_num
      linarith
    · have : (x - y) ^ 2 ≥ 0 := by exact sq_nonneg (x - y)
      rw[sub_sq] at this
      rify at this
      norm_num
      linarith
  have ineq3 : x ^ 2 + y ^ 2 + x * y ≥ (x ^ 2 + y ^ 2) / (2 : ℝ) := by 
    rw[(by linarith : (x ^ 2 + y ^ 2) / (2 : ℝ) = x ^ 2 + y ^ 2 - (x ^ 2 + y ^ 2) / (2 : ℝ))]
    exact le_trans (tsub_le_tsub_left ineq2 (x ^ 2 + y ^ 2)) ineq1
  --this is greater 1 since |x| ≥ 2 
  have ineq4 : (x ^ 2 + y ^ 2) / (2 : ℝ) > 1 := by
    rw[add_div, ← add_zero 1]
    exact add_lt_add_of_lt_of_le (by rw[lt_div_iff₀ (by linarith)]; norm_num; rify at h; rw[(by norm_num : (2 : ℝ) = |2|), ← sq_le_sq] at h; linarith) (by rw[le_div_iff₀ (by linarith)]; norm_num; norm_cast; exact sq_nonneg y)
  linarith

theorem number_theory_142167 {n : ℤ} :
    {(x,y) : ℤ × ℤ | x ^ 2 + n * x * y + y ^ 2 = 1}.Infinite ↔ n ≠ 0 ∧ n ≠ 1 ∧ n ≠ -1 := by
  --assume that n = 0
  by_cases hn0 : n = 0
  · rw[hn0]
    simp
    --then the set of solution is {(1,0), (-1,0), (0,1), (0,-1)} because x.1 and x.2 are forced to have absolute value ≤ 1.
    have set_eq : {x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 2 = 1} = {(1,0), (-1,0), (0,1), (0,-1)} := by
      ext x
      simp
      constructor
      all_goals intro h
      · have abs_le_one : |x.1| ≤ 1 ∧ |x.2| ≤ 1 := by
          rw[Int.abs_le_one_iff, Int.abs_le_one_iff]
          constructor
          all_goals
            by_contra h'
            push_neg at h'
          · have : |x.1| > 1 := by 
              rw[gt_iff_lt, lt_abs]
              omega
            rw[(by norm_num : (1 : ℤ) = |1|)] at this
            rw[gt_iff_lt, ← sq_lt_sq] at this
            have := lt_of_lt_of_le (this) (le_add_of_nonneg_right (sq_nonneg x.2))
            rw[h] at this
            linarith
          · have : |x.2| > 1 := by
              rw[gt_iff_lt, lt_abs]
              omega
            rw[(by norm_num : (1 : ℤ) = |1|)] at this
            rw[gt_iff_lt, ← sq_lt_sq] at this
            have := lt_of_lt_of_le (this) (le_add_of_nonneg_left (sq_nonneg x.1))
            rw[h] at this
            linarith
        rw[Int.abs_le_one_iff, Int.abs_le_one_iff] at abs_le_one
        obtain ⟨abs1,abs2⟩ := abs_le_one
        obtain abs10|abs11|abs1m1 := abs1
        · obtain abs20|abs21|abs2m1 := abs2
          · exfalso; rw[abs10,abs20] at h; linarith
          · right; right; left; ext; exact abs10; exact abs21
          · right; right; right; ext; exact abs10; exact abs2m1
        · obtain abs20|abs21|abs2m1 := abs2
          · left; ext; exact abs11; exact abs20
          · exfalso; rw[abs11, abs21] at h; linarith
          · exfalso; rw[abs11, abs2m1] at h; linarith
        · obtain abs20|abs21|abs2m1 := abs2
          · right; left; ext; exact abs1m1; exact abs20
          · exfalso; rw[abs1m1, abs21] at h; linarith
          · exfalso; rw[abs1m1, abs2m1] at h; linarith
      · obtain case1|case2|case3|case4 := h
        · rw[case1]; norm_num
        · rw[case2]; norm_num
        · rw[case3]; norm_num
        · rw[case4]; norm_num
    rw[set_eq]
    exact Set.Finite.ofFinset ({(1,0), (-1,0), (0,1), (0,-1)}) (by simp)
  --assume that n is not 0, then it suffices to show the claim for n positive, because we can apply the lemma reflection_of_roots to conclude
  · suffices ∀ m, m > 0 → ({(x,y) : ℤ × ℤ | x ^ 2 + m * x * y + y ^ 2 = 1}.Infinite ↔ m ≠ 1) by
      --in fact if n is positive then we just have the result by specializing the sufficient condition
      by_cases hnpos : n > 0
      · specialize this n hnpos
        rw[this]
        constructor
        · intro h
          exact ⟨hn0, h, by linarith⟩
        · intro h
          exact h.2.1
      --if n is negative then we specialize the sufficient condition at -n and then use the reflection lemma to conclude
      · have hnneg : n < 0 := by omega
        specialize this (-n) (by linarith)
        rw[reflection_of_roots (-n) (by linarith)] at this
        norm_num at this
        rw[neg_eq_iff_eq_neg] at this
        constructor
        · intro h
          exact ⟨hn0, by linarith, this.1 h⟩
        · intro h
          exact this.2 h.2.2
    --to prove it for positive m we divide
    intro m hm
    constructor
    all_goals intro h
    --m = 1 → the set of solutions is finite
    · contrapose h
      push_neg at h
      simp
      --in fact by the lemma bound_of_abs_bound_one we have that if |x.1| ≥ 2 or |x.2| ≥ 2 then x.1 ^ 2 + m * x.1 * x.2 + x.2 ^ 2 > 1
      --which directly implies that the set of solutions is contained in the set of pairs (x,y) such that |x| ≤ 1 and |y| ≤ 1, which is finite
      have finites : {x : ℤ × ℤ | |x.1| ≤ 1 ∧ |x.2| ≤ 1}.Finite := by 
        have set_eq : {x : ℤ × ℤ | |x.1| ≤ 1 ∧ |x.2| ≤ 1} = {(1,0), (-1,0), (0,1), (0,-1), (0,0), (1,1), (-1,-1), (1,-1), (-1,1)} := by 
          ext x
          constructor
          all_goals
            intro hk
            simp at hk ⊢
          · rw[abs_le, abs_le] at hk
            rw[Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
            simp
            omega
          · rw[abs_le, abs_le]
            rw[Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff] at hk
            simp at hk
            omega
        rw[set_eq]
        exact Set.Finite.ofFinset ({(1,0), (-1,0), (0,1), (0,-1), (0,0), (1,1), (-1,-1), (1,-1), (-1,1)}) (by simp)
      have subs : {x : ℤ × ℤ | x.1 ^ 2 + m * x.1 * x.2 + x.2 ^ 2 = 1} ⊆ {x : ℤ × ℤ | |x.1| ≤ 1 ∧ |x.2| ≤ 1} := by 
        rw[Set.subset_def]
        intro x hx
        simp at hx ⊢
        by_contra hk
        push_neg at hk
        rw[imp_iff_or_not] at hk
        push_neg at hk
        rw[h, one_mul] at hx
        obtain hk1|hk2 := hk
        · have := bound_of_abs_bound_one x.1 hk1
          rify at hx
          linarith
        · have := bound_of_abs_bound_one x.2 hk2
          rify at hx
          linarith
      exact Set.Finite.subset finites subs
    --m ≠ 1 → the set of solutions is infinite
    · by_cases hm2 : m = 2
      --when m = 2 we get that the function k ↦ (1 - k, k) is injective and maps ℕ into the set of solutions
      --this means that the set of solutions is infinite because it contains ℕ
      · rw[hm2]
        let f : ℕ → ℤ × ℤ := fun k => ((1 - k), k)
        have f_inj_nat : Set.InjOn f {x | x : ℕ}  := by
          unfold Set.InjOn
          intro x hx y hy
          simp[f]
        have f_mapsto : Set.MapsTo f {x | x : ℕ} {(x, y) | x ^ 2 + 2 * x * y + y ^ 2 = 1} := by
          unfold Set.MapsTo
          intro x hx
          simp
          rw[sub_sq]
          linarith
        have N_inf : Set.Infinite {x | x : ℕ}  := by
          rw[Set.infinite_iff_exists_gt]
          intro a
          use (a + 1)
          simp
        exact Set.infinite_of_injOn_mapsTo f_inj_nat f_mapsto N_inf
      --when m > 2 we get that by lemma abundance_of_solutions the set of solutions is infinite
      --non of them is equal to one another since the function g₁ which is the first component of the interation of f is strictly monotone 
      --and hence injective, since elements in ℤ × ℤ are the same if they are so componentwise
      · have hmgt : m > 2 := by omega
        let f : ℤ × ℤ → ℤ × ℤ := fun x => (m * x.1 + x.2, -x.1)
        let g : ℕ → ℤ × ℤ := fun n => Nat.iterate f n (1,0)
        have g_inj : Function.Injective g := by 
          unfold Function.Injective
          intro x y hxy
          let g₁ : ℕ → ℤ := fun n => (g n).1 
          have g₁eq : g₁ x = g₁ y := by 
            simp[g₁]
            exact congrArg Prod.fst hxy
          have g₁_strictmono : StrictMono g₁ := by 
            apply strictMono_nat_of_lt_succ
            intro a
            simp[g₁, g]
            rw[← Function.iterate_succ_apply, Function.iterate_succ_apply' f a (1, 0)]
            simp  
            have fst_snd_add : (f^[a] (1, 0)).1 ≥ 0 ∧ (f^[a] (1, 0)).2 > - (f^[a] (1, 0)).1 := by
              induction a with
              | zero => simp
              | succ d hd => 
              rw[ Function.iterate_succ_apply' f d (1, 0)]
              simp
              constructor
              · have ineq1' : m * (f^[d] (1, 0)).1 + (f^[d] (1, 0)).2 > m * (f^[d] (1, 0)).1 + - (f^[d] (1, 0)).1 := by 
                  exact Int.add_lt_add_left hd.2 (m * (f^[d] (1, 0)).1)
                have ineq2' : m * (f^[d] (1, 0)).1 - (f^[d] (1, 0)).1 ≥ 0 := by 
                  nth_rw 2 [← one_mul (f^[d] (1, 0)).1]
                  rw[← sub_mul]
                  nth_rw 2 [(by norm_num : (0 : ℤ) = 0 * (f^[d] (1, 0)).1)]
                  exact mul_le_mul (by linarith) (by rfl) hd.1 (by linarith)
                exact le_of_lt (lt_of_le_of_lt ineq2' ineq1')
              · have ineq1' : m * (f^[d] (1, 0)).1 + (f^[d] (1, 0)).2 > m * (f^[d] (1, 0)).1 + - (f^[d] (1, 0)).1 := by 
                  exact Int.add_lt_add_left hd.2 (m * (f^[d] (1, 0)).1)
                have ineq2' : m * (f^[d] (1, 0)).1 - (f^[d] (1, 0)).1 ≥ (f^[d] (1, 0)).1 := by 
                  nth_rw 2 [← one_mul (f^[d] (1, 0)).1]
                  rw[← sub_mul]
                  nth_rw 2 [← one_mul (f^[d] (1, 0)).1]
                  exact mul_le_mul (by linarith) (by rfl) hd.1 (by linarith)
                exact lt_of_le_of_lt ineq2' ineq1'
            have ineq1 : m * (f^[a] (1, 0)).1 + (f^[a] (1, 0)).2 > m * (f^[a] (1, 0)).1 + - (f^[a] (1, 0)).1 := by 
              exact Int.add_lt_add_left fst_snd_add.2 (m * (f^[a] (1, 0)).1)
            have ineq2 : m * (f^[a] (1, 0)).1 - (f^[a] (1, 0)).1 ≥ (f^[a] (1, 0)).1 := by 
              nth_rw 2 [← one_mul (f^[a] (1, 0)).1]
              rw[← sub_mul]
              nth_rw 2 [← one_mul (f^[a] (1, 0)).1]
              exact mul_le_mul (by linarith) (by rfl) fst_snd_add.1 (by linarith)
            exact lt_of_le_of_lt ineq2 ineq1
          have := StrictMono.injective g₁_strictmono
          unfold Function.Injective at this
          specialize this g₁eq
          exact this
        exact Set.infinite_of_injective_forall_mem g_inj (abundance_of_solutions hmgt)