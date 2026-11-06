import Mathlib

/-
Determine the sum of all distinct real values of $x$ such that

$$
|||\cdots|| x|+x|\cdots|+x|+x|=1
$$

where there are $2017 x$ 's in the equation.
-/

theorem algebra_609718 (f : ℝ → (ℕ→ ℝ)) (hf : ∀ x:ℝ, ((f x) 1 = |x|) ∧ (∀n≥1, (f x) (n+1) = |f x n + x|) ) :
  ∑ᶠ x ∈ {x:ℝ | f x 2017 =1}, x = -2016/2017 := by
  
  -- We first prove that those x with f x 2017 =1 can only be -1 or 1/2017.
  let S : Set ℝ := {x:ℝ | f x 2017 =1}
  have sol : S = {-1, 1/2017} := by 
    simp [S];
    ext x;

    --Two important lemmas, giving us the formula for f.
    have lem1 : ∀ x ≥ 0, (∀n≥1, f x n = n * x) := by 
      intro x xnneg
      intro n hn
      
      have eq: ∀ m : ℕ, f x (m+1) = (m+1) * x := by 
        intro m 
        induction' m with m hm
        simp [hf]; linarith

        have : f x (m+1 + 1) = |(f x (m+1)) + x| := by 
          have : ((f x) 1 = |x|) ∧ (∀n≥1, (f x) (n+1) = |f x n + x|) := by apply hf
          apply this.2 (m+1); linarith
        rw [this, hm]
        norm_cast; field_simp
        nth_rw 2 [add_mul]; rw[one_mul];
        have : 0≤ (↑m + 1) * x + x := by 
          norm_cast; 
          positivity
        exact abs_of_nonneg this

      have exi : ∃ k : ℕ, k+1 = n := by use n-1; omega
      obtain ⟨k,hk⟩ := exi
      have : f x (k + 1) = (↑k + 1) * x := by apply eq
      norm_cast at this
      rw [hk] at this; assumption

    have lem2 : ∀ x < 0, (∀n≥1, (Odd n → f x n = |x|)∧(Even n → f x n = 0)) := by 
      intro x xneg
      intro n hn

      have eq : ∀ m : ℕ, (Odd (m+1) → f x (m+1) = |x|)∧(Even (m+1) → f x (m+1) = 0) := by 
        intro m
        induction' m with m hm
        simp [hf];

        have : f x (m+1 + 1) = |(f x (m+1)) + x| := by 
          have : ((f x) 1 = |x|) ∧ (∀n≥1, (f x) (n+1) = |f x n + x|) := by apply hf
          apply this.2 (m+1); linarith
        rw[this]
        
        by_cases oddmp1 : Odd (m+1)
        have evenmp1p1: Even (m+1+1) := by exact Odd.add_one oddmp1
        have : f x (m + 1) = |x| := by exact hm.left oddmp1
        rw [this]
        simp [evenmp1p1]
        have : |x| = - x := by exact abs_of_neg xneg
        rw [this]; ring

        have evenmp1 : Even (m+1) := by exact Nat.not_odd_iff_even.mp oddmp1
        have oddmp1p1 : Odd (m+1+1) := by exact Even.add_one evenmp1
        have : f x (m+1) = 0 := by exact hm.right evenmp1
        rw [this]
        simp [oddmp1p1]

      have exi : ∃ k : ℕ, k+1 = n := by use n-1; omega
      obtain ⟨k,hk⟩ := exi
      have : (Odd (k + 1) → f x (k + 1) = |x|)∧(Even (k + 1) → f x (k + 1) = 0) := by apply eq
      norm_cast at this
      rw [hk] at this; assumption
    

    --Now we use the formula for f to prove that x can only be -1 or 1/2017.
    constructor
    -- prove if x is a solution then it belongs to {-1, 1/2017}
    simp
    intro h

    by_cases x < 0
    have tmp: (∀ n≥1, (Odd n → f x n = |x|)∧(Even n → f x n = 0)) := by apply lem2; assumption
    have : f x 2017 = |x| := by 
      have t: (Odd 2017 → f x 2017 = |x|)∧(Even 2017 → f x 2017 = 0) := by apply tmp; linarith
      have t2: (Odd 2017 → f x 2017 = |x|) := by exact t.left
      apply t2; use 1008; norm_num
    rw [this] at h
    have : x = 1 ∨ x = -1 := by exact eq_or_eq_neg_of_abs_eq h
    cases this
    linarith
    left; assumption

    have : 0 ≤ x := by linarith
    have tmp := lem1 x this
    have : f x 2017 = 2017*x := by exact tmp 2017 (by linarith)
    rw [this] at h; 
    right; linarith
    
    -- prove -1 and 1/2017 satisfies the condition
    simp
    intro h
    rcases h with h|h

    have t: (∀ n≥1, (Odd n → f x n = |x|)∧(Even n → f x n = 0)) := by apply lem2; linarith
    have : (Odd 2017 → f x 2017 = |x|) ∧ (Even 2017 → f x 2017 = 0) := by apply t 2017; linarith
    have t2: (Odd 2017 → f x 2017 = |x|) := by exact this.left
    have odd2017: Odd 2017 := by use 1008; norm_num
    apply t2 at odd2017; rw [odd2017]; rw [h]; norm_num

    have t: (∀ n≥1, f x n = n * x)  := by apply lem1; linarith
    have : f x 2017 = 2017 * x := by apply t; linarith
    rw [this,h]; norm_num


  --Now, we add them up.
  have eq : ∑ᶠ x ∈ {x:ℝ | f x 2017 =1}, x = ∑ᶠ x ∈ S, x := by simp [S]
  rw [eq]; simp [sol]; norm_num
  have : -((2016:ℝ)/2017) = -1 + 1/2017 := by ring
  rw [this];
  refine finsum_mem_pair ?_
  linarith
  