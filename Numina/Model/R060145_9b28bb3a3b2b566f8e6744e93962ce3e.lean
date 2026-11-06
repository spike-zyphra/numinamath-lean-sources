import Mathlib

theorem algebra_184147 {f g : ℝ → ℝ} (hf : f = fun x => 2 ^ x) (hg : g = fun x => 4 ^ x)
    (hfg : ∀ x, g (g x) > g (f x) ∧ g (f x) > f (g x)) :
    0 < x ∧ x < 1 := by 
  have h1 := hfg 0
  norm_num [hf, hg] at h1
  all_goals 
    norm_num [hf, hg] at h1 ⊢ 
    <;> tauto