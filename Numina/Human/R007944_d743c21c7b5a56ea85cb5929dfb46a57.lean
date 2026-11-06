import Mathlib

open Polynomial Complex

/- For certain real numbers $a$, $b$, and $c$, the polynomial
$$
g(x) = x^3 + ax^2 + x + 10
$$
has three distinct roots, and each root of $g(x)$ is also a root of the polynomial
$$
f(x) = x^4 + x^3 + bx^2 + 100x + c.
$$
What is $f(1)$?
$\textbf{(A)}\ -9009 \qquad\textbf{(B)}\ -8008 \qquad\textbf{(C)}\ -7007 \qquad\textbf{(D)}\ -6006 \qquad\textbf{(E)}\ -5005$ -/
theorem algebra_96240 {a b c : ℝ} (g f : Polynomial ℝ)
    (hg : g = X ^ 3 + C a * X ^ 2 + X + C 10)
    (hf : f = X ^ 4 + X ^ 3 + C b * X ^ 2 + C 100 * X + C c)
    (_ : (g.map ofRealHom).roots.Nodup)
    (hroots : (g.map ofRealHom).roots ≤ (f.map ofRealHom).roots) :
    f.eval 1 = -7007 := by

  -- Firstly, we prove that f and g is monic
  have hg_monic : (g.map ofRealHom).Monic := by
    simp [hg, add_assoc (X ^ 3), add_assoc]
    apply Monic.add_of_left
    · exact monic_X_pow 3
    · simp
      have : (C (a : ℂ) * X ^ 2 + (X + C 10)).degree ≤ 2 := by compute_degree!
      exact lt_of_le_of_lt this (by decide)
  have hf_monic : (f.map ofRealHom).Monic := by
    simp [hf, add_assoc (X ^ 4), add_assoc]
    apply Monic.add_of_left
    · exact monic_X_pow 4
    · simp
      have : (X ^ 3 + (C (b : ℂ) * X ^ 2 + (C 100 * X + C (c : ℂ)))).degree ≤ 3 := by
        compute_degree!
      exact lt_of_le_of_lt this (by decide)

  -- We also prove that f and g have 4 and 3 (complex) roots respectively
  have hg_roots_card : (g.map ofRealHom).roots.card = 3 := by
    convert (natDegree_eq_card_roots (p := g) (i := ofRealHom) ?_).symm
    · symm
      rw [hg]
      compute_degree!
    · exact IsAlgClosed.splits_codomain g
  have hf_roots_card : (f.map ofRealHom).roots.card = 4 := by
    convert (natDegree_eq_card_roots (p := f) (i := ofRealHom) ?_).symm
    · symm
      rw [hf]
      compute_degree!
    · exact IsAlgClosed.splits_codomain f

  -- As ℂ is algebraically closed, we can write f(X) and g(X) as product of X - r over all roots r
  have hg_eq := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hg_monic (by
    rw [natDegree_map, show g.natDegree = 3 by rw [hg]; compute_degree!]
    have := natDegree_eq_card_roots (p := g) (i := ofRealHom) ?_
    · rw [← this, hg]
      compute_degree!
    · exact IsAlgClosed.splits_codomain g
  )
  have hf_eq := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf_monic (by
    rw [natDegree_map, show f.natDegree = 4 by rw [hf]; compute_degree!]
    have := natDegree_eq_card_roots (p := f) (i := ofRealHom) ?_
    · rw [← this, hf]
      compute_degree!
    · exact IsAlgClosed.splits_codomain f
  )

  -- Since all roots of g are roots of f, we can write f(X) as g(X) * (X - r) for some r
  have hf_roots_eq :
      (f.map ofRealHom).roots
        = (g.map ofRealHom).roots + ((f.map ofRealHom).roots - (g.map ofRealHom).roots) := by
    ext w
    rw [Multiset.count_add, Multiset.count_sub]
    rw [Nat.add_sub_of_le]
    exact Multiset.count_le_of_le _ hroots
  have hdiff_roots_eq : ((f.map ofRealHom).roots - (g.map ofRealHom).roots).card = 1 := by
    rw [Multiset.card_sub hroots, hf_roots_card, hg_roots_card]
  obtain ⟨r, hr⟩ := Multiset.card_eq_one.mp hdiff_roots_eq
  rw [hf_roots_eq, Multiset.map_add, Multiset.prod_add, hg_eq, hr] at hf_eq
  simp [hf, hg] at hf_eq

  -- Now, we expand the parentheses to compare coefficients
  have h_eqs :
      X ^ 4 + C (a - r) * X ^ 3 + C (1 - a * r) * X ^ 2 + C (10 - r) * X - C (10 * r)
        = X ^ 4 + X ^ 3 + C (b : ℂ) * X ^ 2 + C 100 * X + C (c : ℂ) := by
    convert hf_eq using 1
    simp [C_sub, C_add]
    ring_nf

  -- From here, we look at all coefficients to solve for r, a, b, c in that order.
  have hr : r = -90 := by
    apply_fun fun p ↦ p.coeff 1 at h_eqs
    simp at h_eqs
    rw [← C_sub, ← C_mul, ← C_1, ← C_sub] at h_eqs
    simp_rw [coeff_C_mul_X_pow] at h_eqs
    simp at h_eqs
    rw [sub_eq_iff_eq_add', ← sub_eq_iff_eq_add] at h_eqs
    norm_num at h_eqs
    exact h_eqs.symm
  subst hr

  have ha : a = -89 := by
    apply_fun fun p ↦ p.coeff 3 at h_eqs
    simp at h_eqs
    rw [← C_add, ← C_mul, ← C_1, ← C_add] at h_eqs
    simp_rw [coeff_C_mul_X_pow] at h_eqs
    simp at h_eqs
    rw [← eq_sub_iff_add_eq] at h_eqs
    norm_num at h_eqs
    exact_mod_cast h_eqs
  subst ha

  have hb : b = -8009 := by
    apply_fun fun p ↦ p.coeff 2 at h_eqs
    simp at h_eqs
    rw [← C_neg, ← C_add, ← C_1, ← C_mul, ← C_sub] at h_eqs
    simp_rw [coeff_C_mul_X_pow] at h_eqs
    simp at h_eqs
    norm_num at h_eqs
    exact_mod_cast h_eqs.symm
  subst hb

  have hc : c = 900 := by
    apply_fun fun p ↦ p.coeff 0 at h_eqs
    simp at h_eqs
    exact_mod_cast h_eqs.symm
  subst hc

  -- Finally, f(1) can be evaluated as we know all coefficients
  simp [hf]
  norm_num