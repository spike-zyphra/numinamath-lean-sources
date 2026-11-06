import Mathlib

/-The polynomial
$$g(x) = x^3 - x^2 - (m^2 + m) x + 2m^2 + 4m + 2$$is divisible by $x-4$ and all of its zeroes are integers. Find all possible values of $m$.-/
theorem algebra_16144 {m : ℤ}{g : Polynomial ℝ} (hg : g = Polynomial.X ^ 3 - Polynomial.X ^ 2 - ((m : Polynomial ℝ) ^ 2 + (m : Polynomial ℝ)) * Polynomial.X + 2 * (m : Polynomial ℝ) ^ 2 + 4 * (m : Polynomial ℝ) + 2)
    (h1 : g.eval 4 = 0) (h2 : ∀ x ∈ g.roots, ∃ n : ℤ, x = n) :
    m = 5 := by 
  rw [hg] at h1
  simp [Polynomial.eval_X] at h1
  -- simplify g.eval 4 = 0 to (m - 5) * (m + 5) = 0
  have eq₁ : (m - 5) * (m + 5) = 0 := by ring_nf at h1; norm_cast at h1; linarith only [h1]
  rw [mul_eq_zero] at eq₁
  -- so that we have m = 5 or m = -5
  cases eq₁ with
  -- case1 : m = 5, exact the conclusion
  | inl hm =>
    linarith only [hm]
  -- case 2 : m = -5, try to find the contradiction
  | inr hm =>
    -- first, substitute m = -5 into the function g
    replace hm : m = -5 := by linarith only [hm]
    rw [hm] at hg
    ring_nf at hg
    
    -- suppose f is the function g.eval x  
    set f := fun (x : ℝ) => g.eval x with hf
    -- prove the continuity of f
    have continuous₁ : Continuous f := by
      apply Polynomial.continuous
    -- use the intermediate theorem to prove ∃ 1 < x < 2, x ∈ g.roots
    -- first, we have (f(2), f(1)) ⊆ Im((1, 2))
    have intermediate₁ : Set.Ioo (f 2) (f 1) ⊆ f ''Set.Ioo 1 2 := by
      apply intermediate_value_Ioo'
      norm_num
      apply Continuous.continuousOn
      exact continuous₁
    -- calculate f 1 = 12 and f 2 = -4
    nth_rewrite 1 2 [hf] at intermediate₁
    simp at intermediate₁
    rw [hg] at intermediate₁
    simp [Polynomial.eval_X] at intermediate₁
    norm_num at intermediate₁
    -- simplify the set-form proposition to ∃ 1 < x < 2, f x = 0
    rw [Set.subset_def] at intermediate₁
    have include₁ : 0 ∈ f ''Set.Ioo 1 2 := by
      apply intermediate₁ 0
      simp
    rw [Set.mem_image] at include₁
    obtain ⟨x, hx, hfx⟩ := include₁
    simp at hx
    -- convert f x = 0 to x ∈ g.roots 
    rw [hf] at hfx
    simp at hfx
    rw [<-Polynomial.IsRoot.def, <-Polynomial.mem_roots] at hfx
    -- finally find the contradiction with 1 < x < 2 and x ∈ ℤ
    have Nat_x := h2 x hfx
    obtain ⟨n, hn⟩ := Nat_x
    rw [hn] at hx
    norm_cast at hx
    linarith only [hx]
    -- prove g ≠ 0
    intro h0
    have h00 : g.eval 0 = 0 := by
      rw [h0];
      simp
    have h01 : g.eval 0 = 32 := by
      rw [hg]
      simp
    rw [h01] at h00
    norm_num at h00
    
  
