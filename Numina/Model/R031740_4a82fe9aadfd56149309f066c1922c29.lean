import Mathlib

theorem algebra_13173 :
    ∃(S : Finset ℝ), S = {w : ℝ | ∃ f : ℝ → ℝ, (∀ x y : ℝ, f (f x + y) = f (x ^ 2 - y) + 4 * f x * y) ∧ w = f 3} ∧
    (∑ w ∈ S, w) * S.card = 18 := by 
  have h1 : {w : ℝ | ∃ f : ℝ → ℝ, (∀ x y : ℝ, f (f x + y) = f (x ^ 2 - y) + 4 * f x * y) ∧ w = f 3} = {0, 9} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume that there exists $f$ satisfying the functional equation such that $w = f(3)$
      rintro ⟨f, hf, hw⟩
      have h2 : ∀ x, f (f x) = f (x ^ 2) := by 
        intro x
        specialize hf x 0
        simp at hf
        simpa using hf
      have h3 : ∀ x, f x = 0 ∨ f x = x ^ 2 := by 
        intro x
        have h4 : f (f x + (x ^ 2 - f x)) = f (x ^ 2 - (x ^ 2 - f x)) + 4 * f x * (x ^ 2 - f x) := hf x (x ^ 2 - f x)
        have h6 : f (f x + (x ^ 2 - f x)) = f (x ^ 2) := by 
          have h7 : f x + (x ^ 2 - f x) = x ^ 2 := by linarith 
          rw [h7]
        have h7 : f (x ^ 2 - (x ^ 2 - f x)) = f (f x) := by 
          have h8 : x ^ 2 - (x ^ 2 - f x) = f x := by linarith 
          rw [h8]
        have h8 : f (f x + (x ^ 2 - f x)) = f (x ^ 2) := h6
        have h9 : f (x ^ 2 - (x ^ 2 - f x)) = f (f x) := h7 
        rw [h6, h7] at h4 
        have h10 : 4 * f x * (x ^ 2 - f x) = 0 := by 
          have h11 : f (f x) = f (x ^ 2) := h2 x 
          linarith 
        by_cases h : f x = 0 
        · exact Or.inl h 
        · -- If $f(x) ≠ 0$, then from $4f(x)(x ^ 2 - f(x)) = 0$, we must have $x^2 - f(x) = 0$ 
          have h13 : x ^ 2 - f x = 0 := by 
            apply (mul_left_inj' h).mp 
            linarith 
          right 
          linarith 
      have h4 : f 3 = 0 ∨ f 3 = 3 ^ 2 := h3 3 
      rcases h4 with h4 | h4 
      · -- Case f 3 = 0 
        rw [hw] 
        left 
        linarith 
      · -- Case f 3 = 3 ^ 2 = 9 
        rw [hw] 
        right 
        norm_num at h4 ⊢ 
        linarith 
    · -- Show that if $w \in \{0, 9\}$, then there exists a function $f$ satisfying the equation 
      rintro (rfl | rfl)
      · -- Case $w = 0$ 
        use fun x => (0 : ℝ)
        constructor
        · -- Show $f$ satisfies the equation 
          intro x y 
          simp 
        · -- Show $f(3) = 0$ 
          all_goals 
            simp 
      · -- Case $w = 9$ 
        use fun x => x ^ 2 
        constructor 
        · -- Show $f$ satisfies the equation 
          intro x y 
          ring_nf 
        · -- Show $f(3) = 9$ 
          all_goals 
            norm_num 
  use ({0, 9} : Finset ℝ)
  constructor 
  · -- Show that S = {w : ℝ | ∃ f : ℝ → ℝ, (∀ x y : ℝ, f (f x + y) = f (x ^ 2 - y) + 4 * f x * y) ∧ w = f 3}
    rw [h1]
    all_goals
      ext w 
      simp
  · -- Calculate the sum and cardinality 
    norm_num [Finset.sum_insert, Finset.sum_singleton]