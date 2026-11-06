import Mathlib

-- Let $f$ be a function from the nonnegative integers to the positive reals such that $f(x+y)=f(x) \cdot f(y)$ holds for all nonnegative integers $x$ and $y$. If $f(19)=524288 k$, find $f(4)$ in terms of $k$.
open Real

theorem Algebra_609307 {f : ℕ → ℝ}  {k : ℝ} (hpos : ∀ (x : ℕ), f x > 0)
  (hf : ∀ x y : ℕ, f (x + y) = f x * f y) 
  (h19 : f 19 = 524288 * k) : 
  f 4 = 16 * k ^ (4 / (19 : ℝ)) := by

  -- First, prove f 0 = 1 
  have h0 : f 0 = 1 := by 
    have h1 : f 0 > 0 := hpos 0
    have h2 : f (0 + 0) = f 0 * f 0 := hf 0 0 
    simp at h2 
    nlinarith [h1]

  -- Prove that f n = f 1 ^ n for all n
  have h2 : ∀ (n : ℕ), f n = f 1 ^ n := by 
    intro n 
    induction' n using Nat.strongRec with n ih 
    cases n with 
    | zero =>
      simp
      all_goals simpa using h0
    | succ n => 
      have h3 : f (n + 1) = f n * f 1 := by 
        specialize hf n 1 
        simpa using hf
      rw [h3]
      rw [ih n (by omega)]
      simp [pow_succ]

  -- Calculate f 19 = f 1 ^ 19
  have h19' : f 19 = f 1 ^ 19 := by 
    specialize h2 19
    simpa using h2

  -- From h19' and h19, we have f 1 ^ 19 = 524288 * k
  have eq1 : f 1 ^ 19 = 524288 * k := by 
    linarith [ h19', h19 ]

  -- Prove f 4 = (f 1 ) ^ 4
  have eq2 : f 4 = (f 1 ) ^ 4 := by 
    specialize h2 4
    simpa using h2
  
  have hk1 : k > 0 := by 
    have h11 : f 19 > 0 := hpos 19
    nlinarith [ h19 ]

  have hf1 : f 1 > 0 := hpos 1
  
  have eq4 : f 1 = (524288 * k) ^ (1 / (19 : ℝ)) := by 
    have eq5 : (f 1) ^ (19 : ℝ) = (524288 * k) := by
      have h8 : (f 1) ^ (19 : ℝ) = (f 1 ^ 19 : ℝ) := by 
        norm_cast 
      rw [h8] 
      exact_mod_cast eq1 
    have eq8 : f 1 > 0 := hf1 
    have h9 : (f 1) = ((f 1) ^ (19 : ℝ)) ^ (1 / (19 : ℝ)) := by 
      rw [← Real.rpow_mul] 
      field_simp 
      all_goals nlinarith 
    rw [eq5] at h9 
    linarith

  -- Prove f 4 = 16 * k ^ (4 / 19)
  -- Now, need to compute ( (524288 * k )^(1/19) )^ 4
  -- which is (524288 * k )^(4/19 ) 
  -- and this is 16 * k^(4/19 )
  have eq6 : f 4 = 16 * k ^ (4 / (19 : ℝ)) := by 
    rw [eq2] 
    rw [eq4] 
    have eq8 : ((524288 * k) ^ (1 / (19 : ℝ))) ^ 4 = (524288 * k) ^ (4 / (19 : ℝ)) := by 
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      field_simp
      all_goals nlinarith
    rw [eq8] 
    have eq10 : (524288 * k) ^ (4 / (19 : ℝ)) = 16 * k ^ (4 / (19 : ℝ)) := by 
      have eq11 : (524288 * k) ^ (4 / (19 : ℝ)) = (524288 : ℝ) ^ (4 / (19 : ℝ)) * (k : ℝ) ^ (4 / (19 : ℝ)) := by 
        rw [show (524288 * k : ℝ) = (524288 : ℝ) * (k : ℝ) by ring]
        rw [Real.mul_rpow]
        all_goals nlinarith [ hk1 ]
      rw [eq11] 
      have eq12 : (524288 : ℝ) ^ (4 / (19 : ℝ)) = (16 : ℝ) := by 
        have eq13 : (524288 : ℝ) ^ (4 / (19 : ℝ)) = ((2 : ℝ) ^ (19 : ℝ)) ^ (4 / (19 : ℝ)) := by
          norm_num 
        rw [eq13] 
        have eq14 : ((2 : ℝ) ^ (19 : ℝ)) ^ (4 / (19 : ℝ)) = (2 : ℝ) ^ (4 : ℝ) := by 
          rw [← Real.rpow_mul] 
          field_simp 
          all_goals nlinarith 
        rw [eq14] 
        all_goals norm_num
      rw [eq12] 
      all_goals nlinarith 
    linarith [ eq10 ]
  exact_mod_cast eq6