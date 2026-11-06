import Mathlib

open Real

lemma lemma_1 (a b : ℝ) : a + b - abs (a - b) = 2 * min a b := by
  cases' abs_cases (a - b) with h h <;> cases' min_cases a b with h1 h1 <;>
    all_goals
      linarith


theorem algebra_161175 (f g : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc (-1) 1)) (hg : MonotoneOn g (Set.Icc (-1) 1))
    (hfg : ∃ c d, Function.Periodic f c ∧ Function.Periodic g d) :
    MonotoneOn (fun x => f x + g x - abs (f x - g x)) (Set.Icc (-1) 1) ∧
    Even (fun x => f x + g x + f (-x) + g (-x)) := by
  constructor
  · -- We need to prove that f(x)+g(x)-abs(f(x)-g(x)) is monotone on [-1,1]
    intro x hx y hy hxy
    have h1 : -1 ≤ x := by
      have h2 : x ∈ Set.Icc (-1 : ℝ) 1 := hx
      simp at h2 ⊢
      linarith
    have h2 : x ≤ 1 := by
      have h3 : x ∈ Set.Icc (-1 : ℝ) 1 := hx
      simp at h3 ⊢
      linarith
    have h3 : -1 ≤ y := by
      have h4 : y ∈ Set.Icc (-1 : ℝ) 1 := hy
      simp at h4 ⊢
      linarith
    have h4 : y ≤ 1 := by
      have h5 : y ∈ Set.Icc (-1 : ℝ) 1 := hy
      simp at h5 ⊢
      linarith
    have h5 : f x ≤ f y := by
      apply hf
      all_goals
      try { 
        norm_num at *
        all_goals
          try { 
            tauto 
          } 
      }
    have h6 : g x ≤ g y := by
      apply hg
      all_goals
      try { 
        norm_num at *
        all_goals
          try { 
            tauto 
          } 
      }
    have h7 : (f x + g x - abs (f x - g x)) ≤ (f y + g y - abs (f y - g y)) := by
      have h8 : (f x + g x - abs (f x - g x)) = 2 * min (f x) (g x) := by
        apply lemma_1
      have h9 : (f y + g y - abs (f y - g y)) = 2 * min (f y) (g y) := by
        apply lemma_1
      rw [h8, h9]
      have h10 : min (f x) (g x) ≤ min (f y) (g y) := by
        cases' min_cases (f x) (g x) with h11 h11 <;> 
        cases' min_cases (f y) (g y) with h12 h12 <;> 
        all_goals
          try { 
            nlinarith 
          }
      linarith
    exact h7
  · -- We need to prove that f(x)+g(x)+f(-x)+g(-x) is even
    unfold Even
    use (fun x => (f x + g x + f (-x) + g (-x)) / 2)
    funext x
    simp
    all_goals
      ring_nf