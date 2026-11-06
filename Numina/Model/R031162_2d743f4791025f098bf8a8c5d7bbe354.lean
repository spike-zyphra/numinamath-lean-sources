import Mathlib

theorem algebra_15336 {p : Set ℝ} {n : ℕ} {s : ℝ}
    (hp : p = { v |
      ∃ f : ℝ → ℝ, f 1 = 1 ∧
        (∀ x y : ℝ, f (x ^ 2 - y ^ 2) = (x - y) * (f x + f y)) ∧
        v = f 2})
    (hn : n = p.ncard)
    (hs : s = ∑ᶠ x ∈ p, x) :
    n * s = 2 := by
  have h1 : p = {2} := by
    ext v
    simp only [hp, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume v ∈ p, so v = f 2 for some function f satisfying the given conditions
      intro hp
      rcases hp with ⟨f, hf1, hf2, h_eq⟩
      have f00 : f 0 = 0 := by
        specialize hf2 2 2
        norm_num at hf2
        linarith
      have f3 : f 3 = f 2 + 1 := by
        specialize hf2 2 1
        norm_num at hf2
        rw [hf1] at hf2
        linarith
      have eq1 := hf2 (Real.sqrt 2) 0
      have eq2 := hf2 (Real.sqrt 2) 1
      have h_eq5' : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      norm_num [f00, h_eq5'] at eq1
      norm_num [hf1, h_eq5'] at eq2
      have h3 : f (Real.sqrt 2) = Real.sqrt 2 := by
        have eq8 : f (Real.sqrt 2) = Real.sqrt 2 := by
          nlinarith [Real.sqrt_nonneg 2, h_eq5', sq_nonneg (f (Real.sqrt 2) - Real.sqrt 2), sq_pos_of_pos (show (0 : ℝ) < Real.sqrt 2 by positivity)]
        exact_mod_cast eq8
      have h4 : f 2 = 2 := by
        rw [h3] at eq1 
        have h_eq5' : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        nlinarith [h_eq5', h3, eq1, sq_nonneg (f 2 - 2)]
      rw [h_eq] at *
      linarith [h4]
    · -- Now prove the reverse: 2 in p
      intro hp
      rw [hp] at *
      use (fun x => x)
      constructor
      · -- Check f 1 = 1
        norm_num
      constructor
      · -- Check functional equation
        intro x y
        ring_nf
      · -- Check last part
        norm_num
  rw [h1] at hn
  rw [h1] at hs
  have hn1 : (↑n : ℝ) = 1 := by
    rw [hn]
    simp [Set.ncard_singleton]
  have hs1 : s = 2 := by 
    rw [hs]
    simp
  rw [hn1, hs1]
  all_goals norm_num