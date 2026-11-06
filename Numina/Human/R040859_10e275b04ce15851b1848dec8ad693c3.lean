import Mathlib

open Real Set
open scoped BigOperators

/- 3. (CAN) Find the minimum value of  $$ \max (a+b+c, b+c+d, c+d+e, d+e+f, e+f+g) $$  subject to the constraints (i) $a, b, c, d, e, f, g \geq 0$, (ii) $a+b+c+d+e+f+g=1$. -/
theorem inequalities_23789 :
  IsLeast {x | ∃ a b c d e f g : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ e ≥ 0 ∧ f ≥ 0 ∧ g ≥ 0 ∧
    a + b + c + d + e + f + g = 1 ∧ x = max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g)} (1/3) := by
  -- 1/3$ is achieved by taking $(a, b, c, d, e, f, g)=(1 / 3,0,0,1 / 3,0,0,1 / 3)$.
  refine' ⟨⟨1/3, 0, 0, 1/3, 0, 0, 1/3, by norm_num, by norm_num, _⟩, _⟩
  norm_num
  rintro _ ⟨a, b, c, d, e, f, g, ha, hb, hc, hd, he, hf, hg, h_sum, h_goal⟩
  rw [h_goal]
  -- Denote $\max (a+b+c, b+c+d, c+d+e, d+e+f, e+f+g)$ by p.
  let p := max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g)
  -- We have $(a+b+c) \leq p$ ∧ $(c+d+e) \leq p$ ∧ $(e+f+g) \leq p$.
  have h₁ : a + b + c ≤ p := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  have h₂ : c + d + e ≤ p := by
    let m1 := max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)
    let m2 := max (max (a + b + c) (b + c + d)) (c + d + e)
    have step1 : c + d + e ≤ m2 := by
      apply le_max_right
    have step2 : m2 ≤ m1 := by
      apply le_max_left
    have step3 : m1 ≤ p := by
      apply le_max_left
    exact le_trans (le_trans step1 step2) step3
  have h₃ : e + f + g ≤ p := by
    exact le_max_right _ _
  -- We have $$ (a+b+c)+(c+d+e)+(e+f+g)=1+c+e \leq 3 p $$.
  have h_total : a + b + c + c + d + e + e + f + g = 1 + c + e := by linarith
  have h_nonneg : c ≥ 0 ∧ e ≥ 0 := by constructor <;> linarith
  -- which implies that $p \geq 1 / 3$.
  nlinarith [h_total, h_nonneg.1, h_nonneg.2]