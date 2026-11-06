import Mathlib

open Topology Filter Real Complex TopologicalSpace

/- 28.45. The functions $f(x)$ and $g(x)$ are differentiable on the interval $[a, b]$, and the derivative $g'(x)$ does not vanish at any interior point of this interval. Prove that there exists an interior point $x_0$ of the interval $[a, b]$ such that


$$

\frac{f(b)-f(a)}{g(b)-g(a)}=\frac{f'\left(x_{0}\right)}{g'\left(x_{0}\right)} \quad(\text{Cauchy})

$$

## 28.8. Inequalities -/


theorem calculus_229334 {a b : ℝ} {f g : ℝ → ℝ} (hab : a < b) (hf : DifferentiableOn ℝ f (Set.Icc a b))
    (hg : DifferentiableOn ℝ g (Set.Icc a b)) (hfg : ∀ x ∈ Set.Ioo a b, deriv g x ≠ 0) :
    ∃ x ∈ Set.Ioo a b, (f b - f a) / (g b - g a) = (deriv f x) / (deriv g x) := by
  -- the differentiabilities imply continuity on [a, b]
  have h_f_continuous := hf.continuousOn
  have h_g_continuous := hg.continuousOn
  -- then by cauchy theorem we have f'(c) * (g(b) - g(a)) = g'(c) * (f(b) - f(a)), that c will be used for proof
  have h_cauchy := exists_ratio_deriv_eq_ratio_slope f hab h_f_continuous
      (hf.mono Set.Ioo_subset_Icc_self) g h_g_continuous (hg.mono Set.Ioo_subset_Icc_self)
  obtain ⟨c, hc, hfgc⟩ := h_cauchy
  use c
  simp [hc]
  -- g'(c) is not 0 by hypothesis
  have h_g_deriv_ne_zero := hfg c hc
  -- g(a) ≠ g(b), as g(a) = g(b) implies by rolle's theorem there is c' s.t. g'(c') = 0 contraciting hypothesis
  have h_g_a_ne_g_b : g a ≠ g b := by
    by_contra h
    have h_rolle := exists_deriv_eq_zero hab h_g_continuous h
    obtain ⟨c', hc', hgc'⟩ := h_rolle
    specialize hfg c' hc'
    contradiction
  -- now as g'(c) ≠ 0 and g(a) - g(b) ≠ 0 then the ratio is proved from hfgc
  rw [ne_comm, ← sub_ne_zero] at h_g_a_ne_g_b
  field_simp
  linarith